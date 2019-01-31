---
layout: page
title: FAQ
permalink: /FAQ/
---

## Known limitations

- Mutual and even nested structural recursion are supported. Note that
  sometimes the automation can fail to prove the elimination principle due
  to the weakness of the syntactic guardedness criterion. In that case
  switching to a well-founded induction can help. If it fails in case of
  nested recursion, one needs to craft the right elimination principle for
  the decreasing argument's inductive type by hand.

- The ``dependent elimination`` tactic is in active development, and does
  not have a ``dependent induction`` counterpart yet.

- We don't try to automatically prove the completeness of the functions
  graph.
