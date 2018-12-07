We thank the reviewers for their comments.

# Reviewer A

> why are distributivity rules only allowed in one direction?

Because the other direction is derivable from the existing subtyping rules:

```
  A1 <: A1    A2 & A3 <: A2                ...
----------------------------- S-Arr  --------------------------
  A1 -> A2 & A3 <: A1 -> A2           A1 -> A2 & A3 <: A1 -> A3
---------------------------------------------------------------- S-And
         A1 -> A2 & A3 <: (A1 -> A2) & (A1 -> A3)
```

We will point this out in the paper.

> why require termination in the formulation of the logical relation?
> (E[[t1;t2]]) more relaxed formulations (using implication(s) instead of
> conjunction) would be sufficient, right?

We use the textbook definition of `E[[_;_]]`. If expressions are possibly
divergent, then step-indexed logical relations can be used. Suppose the
formulation is changed to use implications, then when `E[[_;_]]` appears in the
premise, not only do we have to provide `v1` and `v2`, we also need to provide
evidence of `e1 ->* v1` and of `e2 ->* v2` to make use of `E[[_;_]]`, whereas using
conjunctions, we get more premises out of `E[[_;_]]`.

# Reviewer B

> In particular, the conclusion is vacuously true by picking e’’ = e’.

You are right, we have made a silly mistake when copying the `type_safety`
theorem from our Coq formalisation in `Target_Safety.v` to the paper. We have
introduced the typo that has yielded the last multi-step reduction (`->*`)
instead of the single step in Coq. We realise now that it would have been
interesting to show the `progress` and `preservation` lemmas from
`Target_Safety.v` in addition to this corollary.

> And even if ->* is replaced by —> or ->+ there is nothing implying that e’’
> isn’t a stuck term.

This theorem guarantees that well-typed programs don't get stuck, see Ahmed's
"Step-Indexed Syntactic Logical Relations for Recursive and Quantified Types"
(Theorem 1), where she presented the exactly same theorem.


> Moreover, the semantics seemingly can only be defined by
> elaboration, and this elaboration isn’t even fully abstract.

Using the fact that we have an elaboration semantics, which is
not fully abstract, against us is unfair in our view.

Type classes (in Haskell and many other languages) are an example of a highly
successful language mechanism defined by elaboration and where the elaboration
is also not fully abstract. Consider the
following program:

```haskell
class Get a where
  get :: () -> a

class Get a => Sub1 a
class Get a => Sub2 a

f :: (Sub1 a, Sub2 a) => a
f = get ()
```

There are two possible elaborations of `f` in the target language (here for simplicity, Haskell without type classes instead of System F_C):

```haskell
data Get a = GetDict { get :: () -> a }
data Sub1 a = Sub1Dict { super1 :: Get a }
data Sub2 a = Sub2Dict { super2 :: Get a }

f1 :: Sub1 a -> Sub2 a -> a
f1 d1 d2 = get (super1 d1) ()

f2 :: Sub1 a -> Sub2 a -> a
f2 d1 d2 = get (super2 d2) ()
```

From within the source language `f1` and `f2` are not distinguishable, because Haskell
enforces that *there is only one instance of a type class per type*. In the target language
we can however construct distinct dictionaries for the same type:

```haskell
distinguish = 
    f1 (Sub1Dict (GetDict (\() -> 1))) (Sub2Dict (GetDict (\() -> 2))) -- yields 1
 == 
    f2 (Sub1Dict (GetDict (\() -> 1))) (Sub2Dict (GetDict (\() -> 2))) -- yields 2
```

Moreover, we follow the same approach used by Dunfield [19], where elaboration
is used to compile intersection types to products, which is similar to
the elaboration approach of Type Classes.

> ...the approach relies on deep coercive subtyping 

Again we feel that using deep coercive subtyping against us
is unfair. Coercive subtyping is very well-established in PL
research. Also, many PL papers that focus on the meta-theory do not
discuss performance considerations (often this is assumed to be a separate
*but agreeably important* thread of work). In particular many papers
present naive small-step operational semantics, which would have
terrible performance if implemented directly.

We do agree that having a discussion about the performance of coercive
subtyping, and possible alternatives/optimizations, is a reasonable
request for the paper and we will talk about it.

> Corollaries 1-3 cannot possibly be correct as stated.

Maybe it's the problem of our notation, but the relevant preconditions are contained
in the definition of contextual equivalence. In our Coq formulation, contextual
equivalence is defined as

```
Definition ctx_equiv Γ E1 E2 A := forall e1 e2 dir dir' C c,
    has_type Γ E1 dir A e1 ->
    has_type Γ E2 dir A e2 ->
    CTyp C Γ dir A nil dir' styp_nat c ->
    ...
```

So whenever we say `Γ |- E1 =ctx E2 : A`, there are preconditions implied. We will highlight this in the narrative.

# Reviewer C

>The main issues I have with this paper concerns 1...

We do not agree that what is in hindsight obviously an elegant and satisfying
approach, was obvious to anyone before. And by anyone we do not just mean
ourselves. As we point out in the introduction, there are multiple separate strands
of research on intersection types:

* Firstly, mainstream language implementations and calculi for such languages with
intersection types (such as Scala, TypeScript, Flow, DOT ...) 
do not use BCD: they use the same subtyping rules for intersections
that both we and Dunfield [19] have used in the past. See for example the DOT calculus [2],
which captures the essence of Scala.

* Secondly, many works on the *merge operator* never involved BCD
subtyping; this includes the work by Dunfield [19], which led to
our work on disjoint intersection types. In the past, we have used the
same rules as Dunfield.

* Finally, BCD is popular in theoretical work focusing on developing calculi
that capture exactly all strongly normalizing lambda terms, where it
plays a central role. However,
those calculi: 1) do not use merge; 2) they mostly do not consider
algorithmic aspects or coherence (which we must consider in our work);
and 3) they do not consider the practical applications of BCD for nested composition.

The reviewer argues that it is surprising that we have not used BCD
before, but we argue that it was only natural: Dunfield (the work that
inspired our own) didn't use it; and mainstream languages with intersection
types did not use it either. A contribution of our work is to identify
why BCD subtyping is a useful thing to have in a programming language: it allows nested
composition, which has significant practical applications. 

> The second issue I have with the paper is that 2 is quite unrelated to 1...

1 and 2 are not unrelated. What they have in common is that they are both
enabled by the same solution: a semantic, rather than a syntactic approach
to coherence. In fact, while we were initially aiming to solve 1, we discovered
that our solution also enabled 2. In hindsight,
the relaxation of disjointness paves the way for the extension of BCD
subtyping.

> The third issue I have is about the logical relations methods used by the authors...

We disagree that it follows obviously from [2], or any other work for that
matter, how to use logical relations for establishing coherence of a calculus
with intersection types and a merge operator. Indeed, as far as we know 
no existing work concerns logical relations for intersection types or 
the merge operator.

Specifically for [2], the step to our setting is non-trivial for two reasons:

- We need to reason about programs that type-check in the source language, but
  operate on the terms in the target language. Additionally, since we use
  bi-directional typechecking in the source, we need to carefully adapt the
  meta-theory to account for bi-directional judgements. This is a major
  challenge not present in [2].

- The structural subtyping in [2] is much simpler than BCD. This is reflected
  in our logical relation's non-trivial treatment of pairs.

> In p4 the paper claims as contributions an implementation and a coq formalization.

The Coq formalization strengthens every claim we made in the paper in that they
are rigorously proved. It also reveals some missing lemmas and oversights in
Pierce's manual proof of the algorithmic subtyping, as we mentioned in Section
5.
