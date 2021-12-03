Changes in Equations 1.3.1:
------------------------------
  
- Fix #279: variable capture bug
- Fix issue #327: performance issue in pattern sigma, resulting in slow noconfusion proofs
- Fix #445: better errors in case unification is unable to find a covering due to occur-checks
- Fix issue #365 and support simplification of sigma types with codomain in SProp
- Fix parsing issue: pattern lists cannot be empty
- Fix issue #449, Equations was reloading the Ltac plugin, breaking redefinitions of tactics
  from that plugin
- Fix an issue with eliminator generation for nested where clauses

Changes in Equations 1.3beta2:
------------------------------

- Fix #399: allow simplification in indices when splitting a variable, 
  to expose the head of the index.
- Fix #389: error derving EqDec in HoTT variant.
- Allow universe binder annotations @{} on Equations definitions.
- Fix "struct" parsing issue that required a reset of Coq sometimes
- Pattern enhancements: no explicit shadowing of pattern variables 
  is allowed anymore. Fix numerous bugs where generated implicit names 
  introduced by the elaboration of patterns could shadow user-given names, 
  leading to incorrect names in right-hand sides.
