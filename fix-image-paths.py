#!/usr/bin/env python3.11

#FIXME: change the absolute path to use the blog host, not the test server

# Only needs to be run from the admin-build script

# Rewrite all image links to be absolute instead of relative. This isn't necessary for
# the blog itself, but is needed for the poor RSS implementation (don't ask) on the TVs
# up around the CSD spaces that periodocally display blog content.

# needs to be passed the path to an index file relative to the website directory

from bs4 import BeautifulSoup
import re
import sys

f = sys.argv[1]
# find the path relative to what will be used on the live blog
subdir = re.findall('./public/(.*)/index.html', f)[0]

with open(f) as fin:
    soup = BeautifulSoup(fin, features="html.parser")
    fin.close()

    for img in soup.findAll('img'):
        if not img['src'].startswith('https'):
            if img['src'].startswith('./'):
                img['src'] = img['src'][2:]
            img['src'] = f'https://www.cs.cmu.edu/~csd-phd-blog/{subdir}/{img["src"]}'

    with open(f, "wb") as fout:
        fout.write(soup.prettify("utf-8"))
