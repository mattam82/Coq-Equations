#/bin/sh
for i in examples/*.v
do
  coqdoc -parse-comments --no-index -utf8 -interpolate -html -R theories Equations -d docs/examples $i
done
