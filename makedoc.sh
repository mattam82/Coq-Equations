#!/bin/sh

cd doc
coqc intro.v
coqdoc --latex --body-only --interpolate intro.v
pdflatex equations.tex

