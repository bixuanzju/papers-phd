We thank the reviewers for their comments. We will follow all
requests for additional discussion in the revised version of the paper.
Here, we try only to address the most important concerns/questions.

## Review B

> I would like a more in-depth comparison with Igarashi et al.

Firstly, we would like to note that the difference between implicit and explicit
polymorphism is very relevant for this question and the examples. One of the
examples by Igarashi et al (in their Sec. 3.3) is:

```
/\X. \x : Bool . x : Bool => * => X
```

Their distinction between gradual and static type variables fundamentally
depends on the fact that they have type abstractions, which allows them to
write:

```
/\X :: G. \x : Bool . x : Bool => * => X
```

and which is accepted in their calculus.

In our implicitly polymorphic calculus there are no type abstractions
and thus there isn't a possibility to annotate type variables (also
note that in Igarashi's calculus forall types *do not* track the
labels, so they cannot be used to recover such information).

In our calculus we could write a similar program as follows:

```
(\x . x : *) : forall X . Bool -> X
```

This program is also accepted, but we cannot do the fine-grained
distinction allowed in Igarashi's calculus, where alternatively
annotating `X` with a static label:

```
/\X :: S. \x : Bool . x : Bool => * => X
```

would lead to a program that is statically rejected.

Secondly their approach to attach labels to universal variables (C_AllS and
C_AllGL in their Fig. 3) is based on the structure of types. But this simple
heuristic does not work in implicit polymorphism, consider we have

```
forall X. X -> X <~ * -> * (accepted because X :: G by C_AllGL)
```

In implicit setting, we have `* -> * <: forall X. * -> *` , and by the property
of consistent subtyping we would have

```
forall X. X -> X <~ forall X. * -> *
```

but this is rejected because `X :: S` by C_AllS.


> Please elaborate on the restriction to predicative polymorphism.

Implicit impredicative polymorphism is generally undecidable. Although there is
some work providing some degree of impredictive polymorphism, they
usually require more refined types and sophisticated meta-theory.
In contrast the polymorphic subtyping relation for predicative
polymorphism is decidable and requires only System F types.
(GHC) Haskell, for example, adopts predicative polymorphism.
Thus it feels natural for us to use this approach too.

> The discussion about example foo p.6 contradicts your previous statement.

Sorry for the confusion caused. The example would still work if we rewrite it as

```
(\f. (x [1, 2] , x [′a′, ′b′])) reverse
```

For readability reasons, we used a let expression.


> Please discuss the relation to the following paper, appearing at POPL 2018.

We will include a discussion in a revised version.

> what if you replace App with the following two rules:... It seems like
> this is an equivalent but simpler and more declarative specification of your
> declarative type system.

We agree that those two rules should work. We use matching instead of these two
rules is because

1) we want to make the declarative system syntax-directed. This is also one step
towards the algorithm.

2) matching can be extended naturally to work for algorithm, where we add one
more rule to deal with existential variables (as in Fig. 12). Therefore it has
more directed connection with the algorithmic type system.

> There are several comments about the algorithmic typing.

In both declarative and algorithmic systems, the typing context is an ordered
list. Namely any existential variable can only be solved by variables appearing
before it. This ensures that we can throw away contexts that are out of
scope, insert a type variable in the correct place, and this leads to the eager
application of ACS-ForalR.

> You mention that the dynamic guarantee is an open question, but the coherence
> issue discussed in section 4.2 quite clearly shows that this guarantee is
> broken, I think.

The reviewer is right, the guarantee is broken by the coherence issue. We will
acknowledge this more directly. However, we believe that the approach briefly
discussed in Section 6.2 to restore coherence may work, and even if it works the
dynamic guarantee is still an open question. As acknowledged by Igarashi in
their paper, the difficulty lies in the definition of term precision that
preserves the semantics. We will explore this further in future work.

## Review C

> in order to extend gradual typing to full Haskell, what other challenges do you envisage?

To type-check features such as GADTs and type families, (GHC) Haskell employs
extensions/variants of type-inference algorithms for predicative implicit
polymorphism such as the one presented here. Probably the main challenge would
be to adapt our work to work with the OutsideIn (Vytiniotis et al.) approach,
which is the core of the idea of Haskell's type inference engine.

> Could you spend some words on how your approach would extend to explicit
> polymorphism, as in mainstream object-oriented languages this is the most
> common form?

Essentially the reviewer's question is related to gradualizing F<:
(Explicitly Polymorphic System F with Subtyping). This is clearly
an interesting and non-trivial question. In some ways
explicit polymorphism simplifies subtyping because the relation
between universal quantification becomes structural, and there's no
need for unification-like techniques. However, bounded polymorphism
(which is supported in F<: and languages like Java) brings its own set of
challenges. Our technique shows that Top (which F<: has) can be dealt
with while preserving orthogonality.
We believe orthogonality would be preserved even in the presence of
bounded quantification, but without careful study it is impossible to say for sure.
