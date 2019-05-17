---
layout: page
title: Equations Reloaded
---

This
[article](https://www.irif.fr/~sozeau/research/publications/drafts/Equations_Reloaded.pdf)
presents the foundations of version 1.2 of the Equations package.

Abstract
--------

Equations is a plugin for the Coq proof assistant which provides a
notation for defining programs by dependent pattern-matching and
structural or well-founded recursion. It additionally derives useful
high-level proof principles for demonstrating properties about them,
abstracting away from the implementation details of the function and its
compiled form. We present a general design and implementation that
provides a robust and expressive function definition package as a
definitional extension to the Coq kernel. At the core of the system is
a new simplifier for dependent equalities based on an original handling
of the no-confusion property of constructors.

Virtual Machine
---------------

All the examples from the article are available to play with running the 
following virtual machine in Virtual Box, setup with Coq 8.9.0 and Equations-1.2:
[VM](https://www.irif.fr/~sozeau/research/publications/artifacts/equations-reloaded.vbox)
