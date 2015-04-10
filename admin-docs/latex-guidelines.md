* When creating a new LaTeX document, symlink `//latex/chicken.sty` in the
  directory of your project and be sure to `\usepackage{chicken}` in the
  document's preamble.
* Add macros as necessary to the bottom of `//latex/chicken.sty`.
* All compilation will be assumed to be done with pdflatex.
  * To compile (assuming you're using chicken.sty), here are the necessary
    packages:
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
