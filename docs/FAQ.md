---
layout: page
title: FAQ
permalink: /FAQ/
---

## Known limitations

# Version 1.0beta2

- Mutual and even nested structural recursion are supported. Note that
  sometimes the automation can fail to prove the elimination principle due
  to the weakness of the syntactic guardedness criterion. In that case
  switching to a mutual induction might help. If it fails in case of
  nested recursion, one needs to craft the right elimination principle for
  the decreasing argument's inductive type by hand.

- The ``dependent elimination`` tactic is in active development, and does
  not have a ``dependent induction`` counterpart yet.

- We don't try to automatically prove the completeness of the functions
  graph.

- The ``Equations Logic`` command has been very lightly tested, and not
  everything supports it yet.

# Version 1.0beta

- It does not support mutual structural recursion (one can use a section
  to define the bodies but it loses the elimination principle).

- The ``dependent elimination`` tactic is in active development, and does
  not have a ``dependent induction`` counterpart yet.

- We don't try to automatically prove the completeness of the functions
  graph.
 
- The ``Equations Logic`` command has been very lightly tested, and not
  everything supports it yet.
