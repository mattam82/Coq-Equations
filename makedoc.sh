#!/bin/sh

cd doc
coqc -I ../src -R ../theories Equations intro.v
coqdoc --no-lib-name --latex --body-only --interpolate intro.v
pdflatex equations.tex

