#/bin/sh
for i in examples/*.v doc/*.v
do
  coqdoc -s --no-lib-name -parse-comments --no-index -utf8 -interpolate -html -R theories Equations -d docs/examples $i
done

git checkout docs/examples/coqdoc.css