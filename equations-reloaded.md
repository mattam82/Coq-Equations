---
layout: page
permalink: /equations-reloaded
title: Equations Reloaded
---

[Equations Reloaded: High-Level Dependently-Typed Functional Programming and Proving in Coq](https://www.irif.fr/~sozeau//research/publications/Equations_Reloaded-ICFP19.pdf). Matthieu Sozeau and Cyprien Mangin.
In: Proc. ACM Program. Lang. 3, ICFP, Article 86 (August 2019), 29 pages. [DOI](https://doi.org/10.1145/3341690),
[slides](http://www.irif.fr/~sozeau/research/publications/Equations_Reloaded-ICFP19-190819.pdf).

This article presents the foundations of version 1.2 of the Equations package.

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

Sources
-------

The following [archive](assets/equations-reloaded.tgz) contains
all examples included in the paper, in full, along with a version of the
proof of normalization for Predicative System F and a reflexive tactic
for solving polynomial equations (1.8MB, MD5 hash:
`3b555d9328c04e622c446a82af64bdca`).

Virtual Machine
---------------

All the examples from the article are also available to play with
running the following virtual machine in Virtual Box, setup with
Ubuntu-64, Coq 8.9.0 and Equations-1.2:
[VM](https://drive.google.com/file/d/1Zt_vLSBZou6nw-FwUrtRocs5jxyOoqq3/view?usp=sharing)
(5.2GB, MD5 hash: `a6272c3810e1861f6896293c261fde91`)
