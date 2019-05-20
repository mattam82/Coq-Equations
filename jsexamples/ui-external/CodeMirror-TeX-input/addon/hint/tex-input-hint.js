// CodeMirror, copyright (c) by Marijn Haverbeke and others
// Distributed under an MIT license: http://codemirror.net/LICENSE

// TeX-style completion, written by Emilio J. Gallego Arias.

// No merge into CodeMirror is planned for now.

/*

  List of open issues:

  - Make the unicode table a parameter.

  - Review if the way we capture the '\' keypress comforms to CM
    coding standards.

*/

(function(mod) {
  if (typeof exports == "object" && typeof module == "object") // CommonJS
    mod(require("../../lib/codemirror"));
  else if (typeof define == "function" && define.amd) // AMD
    define(["../../lib/codemirror"], mod);
  else // Plain browser env
    mod(CodeMirror);
})(function(CodeMirror) {

  var Pos = CodeMirror.Pos;

  // XXX: Generate automatically...
  var unicodePreTable = [
    { text: "\\",       symbol: "\\"},
    { text: "\\_1",     symbol: "₁" },
    { text: "\\_2",     symbol: "₂" },
    { text: "\\alpha",  symbol: "α" },
    { text: "\\beta",   symbol: "β" },
    { text: "\\delta",  symbol: "δ" },
    { text: "\\epsilon", symbol: "ε" },
    { text: "\\exists", symbol: "∃" },
    { text: "\\forall", symbol: "∀" },
    { text: "\\gamma",  symbol: "γ" },
    { text: "\\lambda", symbol: "λ" },
    { text: "\\land",   symbol: "∧" },
    { text: "\\llbracket", symbol: "〚"},
    { text: "\\lnot",   symbol: "¬" },
    { text: "\\lor",    symbol: "∨" },
    { text: "\\mid",    symbol: "∣" },
    { text: "\\models", symbol: "⊧" },
    { text: "\\oplus",  symbol: "⊕" },
    { text: "\\otimes", symbol: "⊗" },
    { text: "\\pi",     symbol: "π" },
    { text: "\\phi",    symbol: "φ" },
    { text: "\\psi",    symbol: "ψ" },
    { text: "\\rrbracket", symbol: "〛"},
    { text: "\\sigma",  symbol: "σ" },
    { text: "\\times",  symbol: "×" },
    { text: "\\to",     symbol: "→" },
    { text: "\\vdash",  symbol: "⊢" },
    { text: "\\Delta",  symbol: "Δ" },
    { text: "\\Gamma",  symbol: "Γ" },
    { text: "\\Lambda", symbol: "Λ" },
    { text: "\\Pi",     symbol: "Π" },
    { text: "\\Sigma",  symbol: "Σ" }
  ];

  /* How our TeX-style completion works:

     We always complete on a press of "\", then we scan back to read
     the token. More fancy things could happen but this works
     reasonably well for now.
   */

  function TeX_input_hint(editor, _options) {

    var cur = editor.getCursor();

    // IMPORTANT: We want to be mode independent so we match backwards
    // from the cursor to the first \.

    var curPos   = Pos(cur.line, cur.ch);
    var matchEnd = Pos(cur.line, cur.ch);

    var match = "";

    while ( 0 <= curPos.ch ) {
      curPos.ch--;
      match = editor.getRange(curPos, matchEnd);
      if (match[0] == '\\') break;
    }

    var matchStart = curPos;

    console.log('cur/tok', cur, match);

    // Replace the current token !
    var insertFun = function(cm, _self, data) {
      cm.replaceRange(data.symbol, matchStart, matchEnd);
    };

    var rList = [];

    // Build of our table
    unicodePreTable.map( function(obj) {
      console.log('Considering: ', obj, ' for ', match);

      if ( obj.text.startsWith(match) ) {
        // XXX: This can be improved for sure.
        obj.displayText = obj.symbol + ' ' + obj.text;
        obj.hint = insertFun;
        rList.push(obj);
      }
    });

    return { list: rList,
             from: matchStart,
             to:   matchEnd
           }
  };

  // We bind '\\'
  function initTexInput (CodeMirror) {

    // We bind slash to the latex autocomplete symbol.
    // We also bind Space to insert current hint.
    CodeMirror.defineInitHook(function (cm) {

      // XXX: Do we want to hook on "_" and "^", etc... ?
      cm.addKeyMap({"\\": function(cm)
                    {
                      cm.replaceSelection("\\");
                      cm.execCommand("autocomplete");
                    }});

      // We need to update the local keymap to the hints.
      var extraHintKeyMap = { Space: function(cm) {

        var cA = cm.state.completionActive;

        if (cA) {
          cA.widget.pick();
          // XXX: Ummmm, not if I want this... maybe make a parameter?
          cm.replaceSelection(" ");
        } } };

      var cmplOpt = cm.getOption("hintOptions");

      cmplOpt = cmplOpt || {};
      cmplOpt['extraKeys'] = extraHintKeyMap;
      cm.setOption("hintOptions", cmplOpt);

    });

    CodeMirror.registerGlobalHelper("hint", "tex-input",
                                    (function () { return true; }), TeX_input_hint);
  }

  initTexInput(CodeMirror);
});

// Local Variables:
// js-indent-level: 2
// End:

