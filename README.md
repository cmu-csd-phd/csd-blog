# CMU CSD PhD Blog

This repository holds the source files for the CMU CSD PhD blog,
hosted at **TODO**.

## Instructions for the student

1. Make a GitHub account if you don't already have one (in the rest of
   the instructions, this will be referred to as `harrybovik`)
2. Fork this repository (click the fork button on the GitHub
   interface) to your user account. This will make
   `https://github.com/harrybovik/csd-blog`.
3. The rest of these instructions assume you are on Linux or MacOS. If
   you are not on either of these, you can use the Andrew Linux
   machines, or set up a VM, or adapt the instructions to the OS of
   your choice. If you have working instructions for a different OS,
   improvements to these instructions would be appreciated.
4. Clone the repository locally using `git clone
   https://github.com/harrybovik/csd-blog`.
5. Copy the `template.md` file from root of the repository into
   `website/content/YEAR/` where `YEAR` is the current year, and
   modify it as necessary for your blog. If the folder for the current
   year does not exist, make a new folder, copying `_index.md` from
   the previous year into the directory first. The name you give to
   the copied `template.md` should indicate a short name for the
   blogpost, so for example if the title of your blogpost is
   "Underwater Basketweaving: A New Approach to Fast Weaving", an
   ideal filename would be `underwater-basketweaving.md`. This file is
   written in Markdown, and the template shows common uses for most
   supported Markdown. If you need help with writing Markdown, please
   refer to the [CommonMark help](https://commonmark.org/help/). If
   you need to use LaTeX in your blogpost, you can use `\\( x^y \\)`
   for inline LaTeX, and `\\[ x^y \\]` or `$$ x^y $$` block-style
   LaTeX. If you want to dive deeper into more advanced stuff you can
   do, you can look at the
   [documentation](https://www.getzola.org/documentation/) for the
   site generator being used, Zola.
6. Run `./local_server.sh` to build the website and view it
   locally. This will start the local server to serve the website at
   http://127.0.0.1:1111/ (check output of the command if this doesn't
   work). Check this URL in your browser to see if it looks ok. Once
   happy, hit Ctrl-C to stop the local server.
7. Run `./local_build.sh` to produce a zip file, and send over the
   produced `generated-website.zip` to committee members (along with
   the `.md` file, for committee members who prefer that).
8. Wait nervously for reviews, suggestions, comments, criticisms,
   praise, and (hopefully) acceptance to come in. If not accepted,
   make changes, and repeat previous steps until accepted by
   committee.
9. Commit your changes to your fork of the repository (`git commit -am
   'Blogpost by Harry Bovik'`) and push changes to GitHub (`git
   push`).
10. Make a pull request to the official repository by clicking the
    pull request button, adding all requested information.
11. Wait for the web-admin to confirm that everything is on order and
    pull your changes into the main repository.
12. Rejoice!

## Instructions for the committee

You do not need to run anything in this repository if you don't want
to. Instead, you simply receive and look at the email sent by the
student.

1. Receive email from student with the zipped/compressed
   folder. Alternatively, you can read the `.md` file directly from
   the student if you prefer that.
2. Unzip it and look at the student's post's HTML file (can be found
   inside `public/YEAR/POSTNAME/index.html`). Links (currently) within
   the post will point to the main website, not to the local
   copy. This may be fixed in the future if someone has time to update
   the scripts/instructions.
3. Provide reviews to students (via email).
4. Rinse and repeat, until post is acceptable.

## Instructions for the web-admin

The following steps need to be run (in order) whenever a pull request
comes from a student:

1. Confirm that the particular blogpost has been approved
   (confirmation from committee (?))
2. Run `./admin_server.sh ID` (where ID is the pull-request number on
   the GitHub interface) to grab a local copy of the student's
   changes, and generate the website on the local machine. This will
   start a local server at http://127.0.0.1:1111/
3. Confirm that the locally generated website looks good (i.e., the
   front page is actually showing the student's new post on top, and
   the link can be clicked on) by visiting the URL with a
   browser. Once satisfied, hit Ctrl-C in the previously running
   command to kill the local server.
4. Merge the changes made by the student on the GitHub web interface,
   so that it is now made permanent in the repository.
5. Run `./admin_build.sh` to pull the authoritative version of the
   repository and build the actual `generated-website.zip` file that
   can then be moved onto AFS and unzipped into the right location.
6. Confirm that the changes are now live (again, just check that the
   new post is visible).

## Technical Information

(Relevant if you are planning on updating the core infrastructure
 around this repository)

+ The exact version of the compiled binary is maintained in
  `./binaries`. If updating to a new version of Zola, the only change
  needed would be to remove the old version in that directory and
  replace it with the new `.tar.gz` and the scripts should
  automatically pick it up.
+ LaTeX rendering performed via KaTeX.
+ The website is hosted via an AFS share at the moment, but since this
  repository works via a site-generator, if the particular web-hosting
  changes, all that would be necessary to change is _where_ the
  produced HTML files are dropped into.

## Credits

- Static site generator and theme setup - Jay Bosamiya (@jaybosamiya)
