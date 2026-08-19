# PR #1 highlighted review diff

`pr-1-vs-main-highlighted.tex` is a self-contained review snapshot comparing
PR #1 with `main` at commit `83a0305`. Blue marks PR additions, red marks text
removed from `main`, and pink marks revisions made from PDF review comments.

Rebuild the PDF from the repository root:

```sh
./doc/review/build.sh
```

The script writes `doc/build/review/pr-1-vs-main-highlighted.pdf`. It requires
XeLaTeX, `latexmk`, and `kpsewhich`; the last command resolves the Latin Modern
fonts bundled with TeX Live so the build does not depend on system font discovery.
