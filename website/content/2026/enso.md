+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Why Modern Network Cards Need a New Interface: Introducing Ensō"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2026-07-28

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Systems"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["nic", "streaming", "networking", "hardware"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Hugo Sadok", url = "https://hsadok.com" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    # {name = "David Andersen", url = "https://www.cs.cmu.edu/~dga/"},
    {name = "Riccardo Paccagnella", url = "https://www.cs.cmu.edu/~rpaccagn/"},
    {name = "Yonghao Zhuang", url = "https://zyhowell.github.io/"},
]
+++


We often think about improving application performance by speeding up some part of the application itself. This can be done in many ways, such as optimizing the application code, using a more efficient algorithm, or even offloading parts of the application to specialized hardware. But a lot of the overheads that applications experience today are instead imposed by the underlying hardware interface. In this blog post, we will look at how the interface exposed by existing network interface cards (NICs) imposes significant overheads on modern applications and how a new NIC interface called Ensō can help eliminate these overheads.
<!-- more -->

<script>
// Single listener that resizes whichever simulator iframe sent the message.
window.addEventListener('message',function(e){
  if(!e.data||typeof e.data.ensoSimHeight!=='number') return;
  document.querySelectorAll('iframe.enso-sim').forEach(function(f){
    if(f.contentWindow===e.source) f.style.height=e.data.ensoSimHeight+'px';
  });
});
</script>

*This blog post is based on the OSDI '23 paper [Ensō: A Streaming Interface for NIC-Application Communication](https://www.usenix.org/conference/osdi23/presentation/sadok). Refer to the paper if you are interested in more technical details.*


## The Rise of the Packetized NIC Interface

Thirty years ago, NICs were significantly simpler. Their only job was to move raw packets between the network and the kernel; the kernel handled all protocol processing (e.g., through the TCP stack), so applications dealt only with processed data. The existing NIC interface was designed around this simple model, where the NIC and the kernel exchange individual packets. We refer to this interface as the *packetized* NIC interface.


### Overview of the Packetized NIC Interface

At a high level, the packetized interface places each incoming and outgoing packet in a dedicated packet buffer in host memory. Each packet buffer has a fixed size that is usually set so that it can accommodate the largest packet size allowed by the protocol (the maximum transmission unit, or MTU). This is necessary, as software does not know ahead of time what the next packet size will be.

The following interactive diagram illustrates how software receives packets from the NIC using a packetized NIC interface. To receive a packet, the software first needs to post empty packet buffers to the NIC (not shown). The NIC will then keep the addresses of the next available buffers in its internal memory so that, when a packet arrives, the NIC can directly copy the packet to the next available buffer in host memory. Then, for each packet, the NIC sends a descriptor to a descriptor ring buffer, informing the software of the packet's location in memory.

You can play with the following diagram to explore how the packetized NIC interface works. Click on "Receive" to simulate receiving packets from the NIC and on "Consume" to simulate software consuming the packets. Note that each packet is placed in a dedicated buffer and that the NIC sends a descriptor for every packet received.

<div style="margin: 1.5em 0;">
<iframe class="enso-sim"
  src="./simulator.html?iface=packetized&format=packet&size=1518&locked=1&pcie=0&l1d=0&play=r,2000,r,2000,r,2000,r,2000,c,1000,c,1000,c,1000,c,1000"
  title="Packetized NIC interface receiving packets"
  width="100%" height="500" style="border:none;display:block;" loading="lazy"></iframe>
</div>


## The Fall of the Packetized NIC Interface

Many things have changed since the packetized interface was first introduced. On the NIC side, modern NICs have thousands of queues. Applications can now have dedicated queues and rely on the NIC to deliver incoming packets directly to the application's memory. Modern NICs can also take over tasks that were traditionally done in software (offloads), from simple ones such as checksum computation and segmentation to more complex ones such as full transport protocol implementations. On the software side, applications have also evolved. High-performance network stacks often employ techniques such as *batching*---where they process multiple packets at a time, instead of individual packets---which helps reduce per-packet overheads.

> While NICs and packet processing software have changed dramatically over the last few decades, the interface that NICs expose has remained surprisingly unchanged---still designed to exchange individual packets with software.

The mismatch between the NIC interface and the data being exchanged leads to the following three problems:

❶ **Packetized Abstraction:** The first problem with the packetized interface is the packetized *abstraction* itself. This arises from the current trend of NICs increasingly implementing functionality that operates at higher layers of the network stack. NICs that implement a transport protocol are able to push application-level messages or bytestreams---assembled at the NIC by combining multiple packets---directly to software. Unfortunately, by shoehorning these high-level data types into the packetized abstraction, the packetized interface imposes unnecessary overheads on software.

For instance, consider a NIC that implements a transport protocol such as TCP. Implementing transport on the NIC can improve application performance by sparing CPU cycles. With TCP, applications exchange data using bytestreams. TCP is responsible for packetizing the data and making sure that every piece of data sent is received by the application. Therefore, a NIC that implements TCP, or other bytestream-based transport, should be able to reassemble packets and directly push bytestreams to software. But if the NIC exposes a packetized interface, it needs to split the incoming bytestream into chunks that fit in the available packet buffers. The following interactive diagram illustrates this issue.

<div style="margin: 1.5em 0;">
<iframe class="enso-sim"
  src="./simulator.html?title=Issue with the Packetized Abstraction · Receiving bytestreams&reasm=1&iface=packetized&format=bytestream&size=5120&locked=1&pcie=0&l1d=0&play=r,m=Reassembled bytestream is larger than the packet buffers and needs to be split.,5000,m=Software needs to recombine pieces before processing.,c,2000,c,4000,m="
  title="Packetized NIC interface splitting a received bytestream"
  width="100%" height="500" style="border:none;display:block;" loading="lazy"></iframe>
</div>

Upon receiving these separate chunks, software needs to recombine them to be able to deliver a contiguous bytestream to the application. This is problematic for two reasons: First, recombining these pieces into a contiguous buffer requires data copies, which consumes CPU cycles. Second, because these pieces can be in arbitrary memory locations, it is hard for the CPU to predict what the next memory access will be. We explore this second problem in more detail next.

❷ **Chaotic Memory Accesses:** Because the packetized interface places incoming data in packet buffers that can be in *arbitrary* memory locations, it is hard for the CPU to predict what the next access will be. This prevents CPU features such as the streaming prefetcher---which speculatively loads sequential memory---from working well, leading to a significant number of cache misses. To illustrate this, consider the following interactive diagram that simulates receiving 64&#8239;B packets using the packetized interface. Because addresses are unpredictable, whenever software accesses a new packet, it must fetch it from the last-level cache (LLC) or main memory, paying a much higher cost compared to serving data from the L1 cache.

<div style="margin: 1.5em 0;">
<iframe class="enso-sim"
  src="./simulator.html?title=Chaotic Memory Accesses · Receiving 64%E2%80%AFB packets&iface=packetized&format=packet&size=64&cache=1&locked=1&pcie=0&play=m=Note how each packet is placed in a dedicated buffer.,r,2000,r,2000,r,2000,r,2000,m=When software consumes packets%2C accesses are unpredictable and packets are fetched from the LLC or memory.,c,2000,c,2000,c,2000,c,2000,,m="
  title="Packetized NIC interface causing chaotic memory accesses for 64&#8239;B packets"
  width="100%" height="500" style="border:none;display:block;" loading="lazy"></iframe>
</div>

Note that simply arranging the packet buffers sequentially in memory does not solve the problem.
This is because packet buffers are fixed-size while packets are not: smaller packets leave holes at the end of their buffers, producing a variable stride between consecutive packets that the CPU cannot predict. Chaotic memory accesses result in as much as a 55% miss ratio for the L2 cache.

❸ **Per-Packet Overhead:** The packetized interface also adds significant overhead due to per-packet metadata. NICs communicate with the CPU through a PCIe interconnect, whose limited bandwidth must be shared between the data itself and any metadata. Since software needs to post a buffer to the NIC for every packet, and the NIC must send software a descriptor for every packet, the packetized interface consumes a significant fraction of PCIe bandwidth just to exchange metadata. High-performance network stacks such as DPDK, a library for kernel-bypass networking, employ batching. But while this saves CPU cycles, it does nothing to reduce per-packet metadata. As a result, when processing small packets, the bottleneck becomes PCIe rather than the CPU: the system cannot reach the full speed of the network link no matter how many cores it uses.

The following interactive diagram illustrates the issue. Note the PCIe efficiency counter in the bottom right corner, which shows the percentage of PCIe bandwidth used for payload vs. metadata. With small packets (64&#8239;B), the PCIe efficiency can be as low as 61%, meaning that 39% of the PCIe bandwidth is used for metadata.

<div style="margin: 1.5em 0;">
<iframe class="enso-sim"
  src="./simulator.html?title=Per-Packet Overhead · Receiving 64%E2%80%AFB packets&iface=packetized&format=packet&size=64&cache=0&locked=1&speed=2&l1d=0&play=m=The packetized NIC needs to send a descriptor for every packet.,r,1000,r,1000,r,1000,r,1000,c,r,1000,c,r,1000,c,r,m=These descriptors cause PCIe bandwidth to be wasted with metadata.,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,m=With small packets (e.g.%2C 64%E2%80%AFB) the PCIe efficiency can be as low as 61%25.,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,r,1000,c,1000,c,1000,c,1000,c,1000,m="
  title="Packetized NIC interface per-packet overhead for 64&#8239;B packets"
  width="100%" height="500" style="border:none;display:block;" loading="lazy"></iframe>
</div>


## Ensō: A Streaming NIC Interface

Ensō is a new NIC interface that provides a *streaming abstraction*. At a high level, Ensō allows the software and the NIC to exchange data using bytestreams. Instead of fixed-size buffers, Ensō gives software the illusion of an unbounded buffer through a new primitive called Ensō Pipe. Software can then use Ensō Pipes to exchange data with the NIC, by reading sequentially to receive data, and by writing sequentially to transmit data.

Ensō imposes no structure on the data written to these buffers---applications and the NIC can use Ensō Pipes to communicate arbitrary streams of bytes. This allows Ensō Pipes to be flexibly used regardless of the functionality running on the NIC. NICs that implement no offloads can use Ensō Pipes to communicate raw packets. NICs that implement a message-based transport protocol can push complete messages to these buffers. Finally, NICs that implement a bytestream-based transport protocol, such as TCP, can use Ensō Pipes to communicate bytestreams directly with applications.


### How can we implement a streaming abstraction?

Unlike the packetized interface, which uses a ring buffer of *descriptors*, Ensō uses a ring buffer of *data* for each Ensō Pipe. Because data is written to the ring buffer itself, applications and the NIC can read and write sequentially.

To synchronize access to the buffer, the NIC and the application each control a pointer. When the application is receiving data from the NIC, the NIC advances its pointer (tail) after writing data to the buffer, and the application advances its pointer (head) when it is done processing the data.

To allow the NIC to send pointer updates to software, Ensō also has a notification buffer. Similar to the descriptor ring buffer in the packetized interface, the notification buffer is a ring buffer with fixed slots. Whenever the NIC wishes to advance its pointer, it sends a notification to software through the notification buffer. Unlike descriptors, notifications do not need to be sent for every chunk of data written to the buffer. Instead, the NIC can send one notification to inform software of *multiple* chunks of data at once.

The following interactive diagram illustrates the Ensō interface. Note that the packets are written sequentially in the same Ensō Pipe. Also note that the NIC is able to send a single notification for a *batch* of packets. When the first packet arrives, the NIC sends a notification; it then withholds further notifications until software consumes the first one.

<div style="margin: 1.5em 0;">
<iframe class="enso-sim"
  src="./simulator.html?iface=enso&format=packet&size=1518&cache=0&locked=1&pcie=0&l1d=0&play=m=The NIC sends a notification after the first packet.,r,1000,r,1000,r,1000,r,1000,m=The NIC then places subsequent packets sequentially in the same buffer without sending notifications.,r,1000,r,1000,r,1000,r,1000,r,1000,r,1000,m=When software consumes packets%2C it advances its pointer and receives the next notification.,c,1000,c,1000,c,1000,c,1000,m=This allows the NIC to notify multiple packets at once without waiting for software to advance its pointer.,c,1000,c,1000,c,1000,c,1000,c,1000,c,1000,c,m="
  title="Ensō interface receiving packets"
  width="100%" height="500" style="border:none;display:block;"
  loading="lazy"></iframe>
</div>


### How can a streaming abstraction improve performance?

Besides being a more flexible abstraction for high-level offloads running on the NIC, Ensō's streaming abstraction also solves the performance issues with the packetized interface that we described earlier.

**Streaming abstraction:** Bytestreams and large messages no longer need to be split and recombined, eliminating the copies imposed by the packetized interface.

**Sequential memory accesses:** Since multiple chunks of data are placed back to back in Ensō Pipes, memory accesses are naturally sequential. This makes it easier for the CPU to predict what the next memory access will be. As a result, Ensō vastly reduces the number of cache misses compared to the packetized interface.

**No per-packet overhead:** Placing data sequentially in Ensō Pipes also allows the NIC to notify multiple chunks of data at once. This avoids the per-packet notification required in the packetized interface. As a result, Ensō significantly reduces the amount of PCIe bandwidth used for metadata as well as CPU cycles required to produce, access, and consume descriptors.

The following interactive diagrams illustrate how Ensō solves the problems we described earlier for the packetized interface.

<style>
.enso-tabs{margin:1.5em 0}
.enso-tabs__list{display:flex;flex-wrap:wrap;gap:4px;border-bottom:1px solid #e7e5e4;margin-bottom:10px}
.enso-tabs__tab{appearance:none;border:0;background:transparent;color:#57534e;font:600 13px/1 -apple-system,BlinkMacSystemFont,"Segoe UI",Roboto,sans-serif;padding:10px 14px;cursor:pointer;border-bottom:2px solid transparent;margin-bottom:-1px;transition:color .12s,border-color .12s}
.enso-tabs__tab:hover{color:#1c1917}
.enso-tabs__tab[aria-selected="true"]{color:#4f46e5;border-bottom-color:#4f46e5}
.enso-tabs__tab:focus-visible{outline:none;box-shadow:0 0 0 3px rgba(79,70,229,.20);border-radius:4px}
.enso-tabs__panel[hidden]{display:none}
.enso-tabs iframe{width:100%;height:500px;border:0;display:block}
</style>
<div class="enso-tabs" id="enso-solutions-tabs">
  <div class="enso-tabs__list" role="tablist" aria-label="Ensō solutions to the three packetized-interface problems">
    <button class="enso-tabs__tab" role="tab" id="enso-tab-1" aria-controls="enso-panel-1" aria-selected="true" tabindex="0">❶ Streaming Abstraction</button>
    <button class="enso-tabs__tab" role="tab" id="enso-tab-2" aria-controls="enso-panel-2" aria-selected="false" tabindex="-1">❷ Sequential Memory Accesses</button>
    <button class="enso-tabs__tab" role="tab" id="enso-tab-3" aria-controls="enso-panel-3" aria-selected="false" tabindex="-1">❸ No Per-Packet Overhead</button>
  </div>
  <div class="enso-tabs__panel" role="tabpanel" id="enso-panel-1" aria-labelledby="enso-tab-1">
    <iframe class="enso-sim"
      data-src="./simulator.html?iface=enso&format=bytestream&size=10120&locked=1&reasm=1&pcie=0&l1d=0&title=Streaming%20Abstraction%20%C2%B7%20Receiving%20bytestreams%20natively&play=r,m=With Ensō bytestreams do not need to be split.,4000,m=Software can access chunks of sequential data without copies.,c,5000,m="
      title="Ensō receiving bytestreams natively" loading="lazy"></iframe>
  </div>
  <div class="enso-tabs__panel" role="tabpanel" id="enso-panel-2" aria-labelledby="enso-tab-2" hidden>
    <iframe class="enso-sim"
      data-src="./simulator.html?iface=enso&format=packet&size=64&cache=1&locked=1&pcie=0&l1d=1&title=Sequential%20Memory%20Accesses%20%C2%B7%20Receiving%2064%E2%80%AFB%20packets&play=m=Incoming packets are placed sequentially in the same buffer.,r,1000,r,1000,r,1000,r,1000,r,1000,r,1000,r,1000,r,1000,m=Software consumes data using sequential accesses%2C allowing the CPU to prefetch data%2C increasing L1d hits.,1000,c,1000,c,1000,c,1000,c,1000,c,1000,c,1000,c,1000,c,1000,c,m="
      title="Ensō with sequential memory accesses for 64&#8239;B packets" loading="lazy"></iframe>
  </div>
  <div class="enso-tabs__panel" role="tabpanel" id="enso-panel-3" aria-labelledby="enso-tab-3" hidden>
    <iframe class="enso-sim"
      data-src="./simulator.html?iface=enso&format=packet&size=64&cache=0&locked=1&speed=2&l1d=0&pcie=1&title=No%20Per-Packet%20Overhead%20%C2%B7%20Receiving%2064%E2%80%AFB%20packets&play=m=Ensō improves PCIe efficiency by avoiding sending a notification for every packet.,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,r,250,m=This vastly reduces the fraction of PCIe bandwidth used to send metadata.,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,250,c,c,m="
      title="Ensō eliminating per-packet overhead for 64&#8239;B packets" loading="lazy"></iframe>
  </div>
</div>
<script>
(function(){
  var root=document.getElementById('enso-solutions-tabs');
  if(!root) return;
  var tabs=Array.prototype.slice.call(root.querySelectorAll('[role="tab"]'));
  function activate(tab){
    tabs.forEach(function(t){
      var selected=t===tab;
      t.setAttribute('aria-selected',selected?'true':'false');
      t.setAttribute('tabindex',selected?'0':'-1');
      var panel=document.getElementById(t.getAttribute('aria-controls'));
      if(!panel) return;
      if(selected){
        panel.removeAttribute('hidden');
        var f=panel.querySelector('iframe');
        if(f&&!f.src&&f.dataset.src){f.src=f.dataset.src}
      }else{
        panel.setAttribute('hidden','');
      }
    });
  }
  tabs.forEach(function(t,i){
    t.addEventListener('click',function(){activate(t);t.focus()});
    t.addEventListener('keydown',function(e){
      var idx=-1;
      if(e.key==='ArrowRight') idx=(i+1)%tabs.length;
      else if(e.key==='ArrowLeft') idx=(i-1+tabs.length)%tabs.length;
      else if(e.key==='Home') idx=0;
      else if(e.key==='End') idx=tabs.length-1;
      if(idx>=0){e.preventDefault();activate(tabs[idx]);tabs[idx].focus()}
    });
  });
  // Load the initially-selected tab's iframe.
  var initial=root.querySelector('[role="tab"][aria-selected="true"]')||tabs[0];
  if(initial) activate(initial);
})();
</script>


## Implementation

Because Ensō is a new NIC interface, implementing it requires changes to both the NIC and the software running on the CPU. Ensō's implementation comprises three components:

**NIC hardware:** We implemented a NIC in SystemVerilog that exposes the Ensō interface. We synthesized the design targeting an FPGA (a programmable hardware device). Using an FPGA lets us test the implementation in a real system, but the design can also be synthesized as fixed-function hardware.

**User-space library:** The software implementation is designed so that applications can communicate directly with the NIC without going through the kernel. Applications can link to the Ensō library and use its streaming API to push data to or pull data from the NIC.

**Kernel module:** While applications use the library to communicate directly with the NIC, setup and resource management are still done by the kernel. Ensō provides a kernel module to accomplish these tasks. The library talks with the kernel module whenever it needs to allocate and free resources, e.g., Ensō Pipes.


## Impact on Application Performance

Ensō's performance improvements translate into benefits for real applications. To show this, we ported four different applications to use Ensō and compared their performance with DPDK implementations running with an Intel E810 100&#8239;Gb NIC.

The following table summarizes the results. It shows the throughput improvement of the Ensō implementation compared to the original DPDK implementation running with the E810 NIC. We see that Ensō is able to improve throughput by up to 6⨉.

| Application | Throughput Improvement |
|:----------- | ----------------------:|
| Google's Maglev Load Balancer \[[NSDI '16](https://www.usenix.org/conference/nsdi16/technical-sessions/presentation/eisenbud)\] | Up to 6⨉ |
| Network Telemetry with NitroSketch \[[SIGCOMM ’19](https://dl.acm.org/doi/10.1145/3341302.3342076)\] | Up to 3.5⨉ |
| MICA Key-Value Store \[[NSDI ’14](https://www.usenix.org/conference/nsdi14/technical-sessions/presentation/lim)\] | Up to 47% |
| Log Monitor (Inspired by [AWS CloudWatch Logs](https://docs.aws.amazon.com/AmazonCloudWatch/latest/logs/WhatIsCloudWatchLogs.html)) | Up to 95% |

The results above cover different classes of applications. Google's Maglev Load Balancer and the network telemetry application are typical applications that operate on raw packets. MICA is a key-value store that operates on messages. Finally, the Log Monitor application is a streaming application that operates on bytestreams. These improvements stem only from the change in NIC interface; we expect even more benefits as Ensō enables NICs to implement more complex offloads such as transport protocols with less software overhead.

The paper includes more detailed experiments: we conduct a series of microbenchmarks that evaluate how some of our design choices affect performance. We also show that Ensō is able to achieve 100&#8239;Gbps line rate (the full speed of the link) with minimum-size packets using a *single* CPU core.

<div style="text-align: center; letter-spacing: 1em; text-indent: 1em; margin: 2.5em 0;">* * *</div>

The packetized interface no longer suits the demands of high-performance applications or the features offered by modern NICs. It is time for NICs to move to a streaming interface. If you would like to use Ensō with your own applications, you can check out its [open-source code](https://github.com/crossroadsfpga/enso) and [documentation](https://enso.cs.cmu.edu). And for more technical details, take a look at the [OSDI '23 paper](https://www.usenix.org/conference/osdi23/presentation/sadok).
