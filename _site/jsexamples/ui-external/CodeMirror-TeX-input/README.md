# TeX-style input for CodeMirror

This addon provides a completion hint for CodeMirror which allows to
use the backslash key `\` to compose Unicode characters in TeX style.

It was inspired by Emacs' `qual-completion`, but it differs a bit on feeling.

See a demo here:
https://ejgallego.github.io/CodeMirror-TeX-input/demo/tex-input.html

See also a demo of the Emacs mode here here: https://youtu.be/3hwUnhdKWiI?t=5m55s

_Warning_: The project is in α-state :)

## How to install

Just include the `addon/hint/tex-input-hint.js` file.

## TODO

The mode pretty much works, we need:

- Add a much larger Unicode table.
- Add support for options, such that users can configure completion
  on space, add new symbols to the table, etc...
