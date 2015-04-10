* When creating a new LaTeX document, be sure to `\usepackage{chicken}` in the
  document's preamble.
  * Package dependencies of chicken:
    [One way to install what you don't have is using `tlmgr` (`sudo tlmgr
    install <package name>`), though everything should be in TeXLive.]
    0. xifthen
    1. mathpazo
    2. fontenc
    3. eucal
    4. fancyhdr
    5. lastpage
    6. geometry
    7. amssymb
    8. amsmath
    9. amsthm
* Add macros as necessary to the bottom of `//latex/chicken.sty`.
* All compilation will be assumed to be done with pdflatex.
  * To compile (assuming you're using chicken.sty), you need to set the
    shell global TEXINPUTS to the path to include the parent directory of
    chicken.sty on your filesystem. The trailing `/:` as shown in the
    following example is necessary.
      Here's an example command:
    ```
    TEXINPUTS=../../latex//: pdflatex foo.tex
    ```
