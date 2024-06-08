+++
# The title of your blogpost. No sub-titles are allowed, nor are line-breaks.
title = "Mariposa: the Butterfly Effect in SMT-based Program Verification"
# Date must be written in YYYY-MM-DD format. This should be updated right before the final PR is made.
date = 2024-06-08

[taxonomies]
# Keep any areas that apply, removing ones that don't. Do not add new areas!
areas = ["Programming Languages"]
# Tags can be set to a collection of a few keywords specific to your blogpost.
# Consider these similar to keywords specified for a research paper.
tags = ["SMT solver", "program verification"]

[extra]
# For the author field, you can decide to not have a url.
# If so, simply replace the set of author fields with the name string.
# For example:
#   author = "Harry Bovik"
# However, adding a URL is strongly preferred
author = {name = "Yi Zhou", url = "https://yizhou7.github.io/" }
# The committee specification is simply a list of strings.
# However, you can also make an object with fields like in the author.
committee = [
    "Committee Member 1's Full Name",
    "Committee Member 2's Full Name",
    {name = "Harry Q. Bovik", url = "http://www.cs.cmu.edu/~bovik/"},
]
+++


The Satisfiability Modulo Theories (SMT) solver is a
powerful tool for automated reasoning. For those who are
unfamiliar, you may think of an SMT solver as a "bot" that
answers logical or mathematical questions. For example, I
can ask if the following statement holds: 

$$ \exists \, a, b, c \in Z \, | \,
3a^{2} -2ab -b^2c = 7 $$

Using the SMT standard format, I may express the question as
the following query. Hopefully the translation is pretty
self-explanatory. Maybe a quirk is that the expressions are in
prefix form, where each operator comes before its
operands.

```
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(assert (exists ((a Int) (b Int) (c Int))
    (=
        (+ (* 3 a a) (* -2 a b) (* -1 b (* c b)))
        7
    )
))
(check-sat)
```
If the bot responds with "Yes", that is good! The answer is
not so obvious to me at least. What's more, the bot provides
fairly high assurance about its responses. I will refrain
from going into the details, but its answer is justified by
**precise mathematical reasoning**. For example, in this
case the bot can also provide a solution, `a = 1, b = 2, c =
-2`, which serves as a checkable witness to the "Yes"
answer.

However, the robot is not perfect. Suppose that I slightly
tweak the formula and ask again:

<!-- $ \exists \, e, f, g \in Z \, | \,
3e^{2} -2ef -e^2g = 7 $
 -->

```
(declare-fun e () Int)
(declare-fun f () Int)
(declare-fun g () Int)
(assert (exists ((e Int) (f Int) (g Int))
    (=
        (+ (* 3 e e) (* -2 e f) (* -1 f (* g f)))
        7
    )
))
(check-sat)
```

This time, the following may happen: the robot gives up,
saying "I don't know" to this new query. Understandably,
this may seem puzzling. As you might have noticed, the two
queries are essentially the same, just with different
variable names. Why would the bot give different responses?
Is it even a legitimate move for it to give up?

Before you get mad at the bot, let me explain. As mentioned
earlier, the SMT solver sticks to precise mathematical
reasoning, meaning that it should not give any bogus answer.
Consequently, when it sees hard questions, it is allowed to
give up. How hard? Well, some questions can be NP-hard! In
fact, the above examples pertain to Diophantine equations,
which are undecidable in general. Therefore, no program can
answer all such questions correctly. The poor bot has to
resort to heuristics, which may not be robust against
superficial modifications to the input query.

<!-- ### Instability of SMT Solving -->

What we have observed is the phenomenon of **SMT
instability**, where trivial changes to the input query may
incur large performance variations (or even different
responses) from the solver. While there can be many
applications of SMT solvers, in this blog post, I will focus
on the instability in **SMT-based program verification**, where
we ask the SMT solver to prove programs correct. Instability
manifests as a butterfly effect: small changes in the
program may lead to large changes in the proof performance
or even outcome, creating spurious verification failures.

<!-- spurious proof failures, where a previously proven program
may be (wrongfully) rejected after trivial changes to the
source code.  -->

# Why SMT-based Program Verification?

If you already know about program verification, please feel
free to skip this section. Otherwise, let me briefly explain
why program verification is useful and how SMT solvers
can help in this process.

As programmers, we often make informal claims about our
software, including its correctness, efficiency, security,
and so on. However, as myself can also testify, these claims
can sometimes be unfounded or even straight-up wrong.
Fortunately, formal verification offers a path to move
beyond these informal claims.

Formal verification uses **mechanized proofs** to show that
the code meets its specification. In comparison to testing,
formal verification offers a higher level of assurance,
since it reasons about all possible inputs, not just the
ones we have tested. For example, we can show that the
program never crashes, or that it always terminates. These
are all fundamentally logical statements. Naturally, we can
ask the SMT solver to help us prove these statements.

As you might have gathered from the previous example, SMT
solvers can reason about pretty complex logical statements.
In practice, SMT solver provides a high degree of
automation, allowing the developer to skip many of the
tedious proof steps. 

Now hopefully you can see how instability can be a big
problem in SMT-based program verification. We use program
verification for higher assurance, but if the verification
process is unstable, the assurance is less convincing.

## Another Subsection Heading

Some more text.
You can write lines
separately
and it'll still
be considered
a single paragraph. Paragraphs are separated by a
blank line.

# Another Section

You can **bold** things by wrapping them in two asterisks/stars. You
can _italicise_ things by wrapping them in underscores. You can also
include inline `code` which is done by wrapping with backticks (the
key likely to the left of the 1 on your keyboard).

If you want to add larger snippets of code, you can add triple
backticks around them, like so:

```
this_is_larger = true;
show_code(true);
```

However, the above doesn't add syntax highlighting. If you want to do
that, you need to specify the specific language on the first line, as
part of the backticks, like so:

```c
#include <stdio.h>

int main() {
   printf("Hello World!");
   return 0;
}
```

If you want to quote someone, simply prefix whatever they said with a
`>`. For example:

> If it is on the internet, it must be true.

-- Abraham Lincoln

You can also nest quotes:

> > You miss 100% of the shots you don't take
>
> -- Wayne Gretzky

-- Michael Scott

Every paragraph _immediately_ after a quote is automatically right
aligned and pressed up against the quote, since it is assumed to be
the author/speaker of the quote. You can suppress this by adding a
`<p></p>` right after a quote, like so:

> This is a quote, whose next para is a normal para, rather than an
> author/speaker

<p></p>

This paragraph is perfectly normal, rather than being forced
right. Additionally, you could also add a `<br />` right beside the
`<p></p>` to give some more breathing room between the quote and the
paragraph.

In the author notifications above, btw, note how the double-hyphen
`--` automatically becomes the en-dash (--) and the triple-hyphen
`---` automatically becomes the em-dash (---). Similarly, double- and
single-quotes are automagically made into "smart quotes", and the
ellipsis `...` is automatically cleaned up into an actual ellipsis...

---

You can add arbitrary horizontal rules by simply placing three hyphens
on a line by themselves.

---

Of course, you can write \\( \LaTeX \\) either inline by placing stuff
within `\\(` and `\\)` markers, or as a separate equation-style LaTeX
output by wrapping things in `\\[` and `\\]`:

\\[ \sum_{n_1 \in \N} \frac{n_1}{n_2} \\]

Alternatively, you can wrap it inside of a pair of double-dollar signs
`$$`:

$$ \frac{\Phi \in \psi}{\psi \rightarrow \xi} $$

Single dollar signs unfortunately do not work for inline LaTeX.

# More fun!

Of course, you can add links to things, by using the right syntax. For
example, [here is a link to NASA](https://www.nasa.gov/). Standard
HTML-like shenanigans, such as appending a `#anchor` to the end of the
link also work. Relative links within the website also work.

You can also use the links to link back to parts of the same
blogpost. For this, you need to find the "slug" of the section. For
this, you can force a slug at the section heading, and then simply
refer to it, like the [upcoming section](#finale), or alternatively,
you can take the lowercase version of all the parts of a section and
place hyphens between them, like [this](#more-fun) or
[this](#another-section).

Pictures, of course, can be added. The best way to do this is to
utilize relative links (just add images into the right directory, see
the main `README` file in this repository to learn where it should
go), but you can link to external images too in the same way. For
example,

![i are serious cat](https://upload.wikimedia.org/wikipedia/commons/4/44/CatLolCatExample.jpg)

Of course, it is good etiquette to add alt-text to your images, like
has been done in the previous image, with "i are serious cat". It
helps with accessibility.

Images are automatically shown at a reasonable size by limiting their
maximum width. If you have a particularly tall image, you might have
to do some manipulation yourself though. Images should also
automatically work properly in mobile phones :)

---

Do you want some tables? Here are some tables:


| Header 1   | Another header here   | This is a long header |
|:---------- | ---------------------:|:---------------------:|
| Some data  | Some more data        | data \\( \epsilon \\) |
| data       | Some _long_ data here | more data             |
| align left |   right               | center                |

You use the `:` specifier in the table header-body splitting line to
specify whether the particular column should be left, center, or right
aligned. All the standard markdown elements continue to work within
the table, so feel free to use them.

# Finale {#finale}

Finally, you're at the end of your blogpost! Your name will appear
again at the end automatically, as will the committee members who will
(hopefully) approve your blogpost with no changes! Good luck!
