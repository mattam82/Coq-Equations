#/bin/sh

cd _build/default/examples

for i in *.v
do
  coqdoc -s --no-lib-name -parse-comments --no-index --utf8 --interpolate --html \
      --external http://github.com/mattam82/Coq-Equations/tree/main Equations \
      -Q ../theories Equations -Q . Examples -d ../../../../equations-www/examples $i
done

cd ../../../../equations-www

git checkout examples/coqdoc.css
