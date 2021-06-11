Changes in Equations 1.3beta2:
------------------------------

- Fix #399: allow simplification in indices when splitting a variable, 
  to expose the head of the index.
- Fix "struct" parsing issue that required a reset of Coq sometimes
- Pattern enhancements: no explicit shadowing of pattern variables 
  is allowed anymore. Fix numerous bugs where generated implicit names 
  introduced by the elaboration of patterns could shadow user-given names, 
  leading to incorrect names in right-hand sides.
