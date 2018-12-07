## Project Goals

* A concise and compiler-friendly core language based on _Calculus of Constructions_ (CoC) that collapses three levels (terms, types, kinds) uniformly into one
* _Decidable type checking_ and managed type-level computation by replacing implicit conversion rule of CoC with _generalized fold/unfold_
* _General recursion_ by introducing recursive types for both terms and types by one primitive `μx.E`
* _First-class equality_ for encoding GADTs and other related extensions by System FC and FC-Pro
* Source language with _datatypes and pattern matching_ encoded into the core language
* Prototype interpreter of the source language
* _Type-level computation_ support, e.g. inductive data types (vectors, finite sets) (?)
* Check proofs by Coq (?)

## Schedule

_Last updated:_ 27 April

Week | Linus | Jeremy
---: | :--- | :---
1 | a. __skeleton__ of paper in _SIGPLAN format_: section titles, motivation, basic literature review; b. consider __removing fold from values__ | __first-class equality__: syntax, statics & dynamics, encoding GADT
2 | _Exam week_ | _Exam week_
3 | _section 2 & 3_ about the core lang w/o equality; needed to illustrate __necessity__ of generalized fold/unfold | continue on __first-class equality__, investigating the translation of __newtype__ (do we need to introduce __axiom__?)
4 | __proofs of soundness__ for all sections related to core lang | writing _section 4 & 5_ about the core lang w/ equality and the __source language__
5 | continue on writing proofs; consider __using coq__ to check | continue writing __section 4 & 5__ as well as implementation
6 | examples for type-level computation | _same as left_ and consider implementation
7 | wrap up and work out 1st draft | _same as left_
8 | 2nd draft | _same as left_
9 | 3rd draft | _same as left_
10 | final version | _same as left_


Notes:

* Week 1 starts from __27 April__, Monday.
* Due date is __6 July__, on Week 11.