ESOP '18 Paper #2 Reviews and Comments
===========================================================================
Paper #70 Consistent Subtyping for All


Review #70A
===========================================================================

Overall merit
-------------
A. Accept (Good paper. I will champion it at the PC meeting.)

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper gradualizes a core language with predicative implicit higher-rank polymorphism. As such, it extends the body of literature of gradual typing and parametric polymorphism by covering an as-yet-uncovered point in the design space. To achieve this, the paper starts by proposing a new definition of consistent subtyping that generalizes the definition of Siek and Taha in a way that makes it suitable for polymorphism. The resulting semantics hits a sweet spot in between existing formulations by Ahmed et al. (which is arguably too permissive statically) and Igarashi et al. (which is arguably too restrictive statically). 
The gradual language is developed by first giving a declarative type system, which is proven to satisfy the static components of Siek et al’s refined criteria, and then an algorithmic type system is presented. This system relies on an algorithmic version of consistent subtyping that tracks existential type variables and their progressive resolution. The algorithmic type system is shown to be sound and complete wrt the declarative one. The paper ends by showing how the top type can be added to the system.

Comments for author
-------------------
This is a well-written paper that presents a valuable contribution to the gradual typing literature, addressing an important topic if one is to see gradual typing make its way to languages like Haskell. Illustrations and discussion of related work are informative.

The extension of consistent subtyping allows to relate two types through 2 steps of subtyping separated by one step of consistency, which is not groundbreaking, but is really sensible and effective, as properly demonstrated. 

A weak point of the paper is its (non-)treatment of the dynamic semantics. Indeed, while the non-determinism of the declarative system is not controversial statically, it is a problem dynamically, as some possible typings might generate runtime errors. The authors briefly discuss an alternative design to take care of this, but they do not directly address it. This reminds me of work on gradual typestates by Garcia et al (ECOOP’12, TOPLAS’14) where the declarative system is first amended in order to make it deterministic, so as to ensure determinism in the runtime behavior as well.



Review #70B
===========================================================================

Overall merit
-------------
A. Accept (Good paper. I will champion it at the PC meeting.)

Reviewer expertise
------------------
X. Expert

Paper summary
-------------
This paper considers the design of a surface language that combines implicit polymorphism with gradual types.
Previous work on combining polymorphism with gradual types either only looks at an internal compiler language (blame calculus) or is a bit ambivalent about the matter (Igarashi et al.).
The authors motivate, present and evaluate a declarative and algorithmic type system, building on existing work from both gradual type systems and type inference for polymorphic languages.
A central design decision is that they try to separate subtyping from consistency checking.
Evaluation is done by proving some of the criteria proposed for gradually-typed languages in previous work.

Comments for author
-------------------
Strong points:
* Interesting, relevant problem

* Keeping subtyping and consistency checking separate is well-motivated and appears to solve problems in previous work.

* Results appear generally sound.

* Well written, well explained.

Weak points:
* No implementation.

* An important coherence issue is left unsolved.
  The issue seems to be problematic for the dynamic guarantee (even though the authors leave that as an open question).

General assessment:
This is another paper on combining parametric polymorphism with gradual typing.
However, it takes a look at a new aspect of the problem, namely the design of a surface language with implicit polymorphism, which previous work ignored or treated ambivalently.
The authors take a well-motivated principled point of view (separating subtyping from consistency) that seems to produce a nice, consistent system (contrary to, for example, [13], which treats types involving * differently than static types).
There still seem to be open issues, particularly concerning the coherence issue discussed in section 6.2 (which the authors, to their credit, discuss in detail rather than attempt to hide).
Anyway, I'm a bit on the fence because of the coherence issue, but all things considered, I believe this work already presents an important advance in the line of work on combining gradual typing and parametric polymorphism and should be accepted.
However, I do encourage the authors to take another look at the coherence issue, perhaps for a journal version of the paper?

General comments:
* I would like a more in-depth comparison with Igarashi et al.
  Particularly, how do you solve the examples that they use to motivate their distinction between gradual and static type variables.
  It seems that the asymmetricity of your consistent subtyping relation solves a number of issues that follow from their symmetric treatment of consistency, is that correct?

* Please elaborate on the restriction to predicative polymorphism.
  Why is this needed?

* The discussion about example foo p.6 contradicts your previous statement that you omit let expressions for simplicity because they are non-essential and have been covered elsewhere already.
  Here, you are using an alternative form of type inference for let expressions as a main motivation of the work.

* p.8: "According to the syntax in Fig. 3, monotypes do not contain the unknown type": This discussion makes me wonder whether you could allow instantiating a polymorphic variable with type * if the variable occurs only once in the type.
  For example, there does not appear to be a reason to not allow functions like "forall A B. B -> A -> A" to be cast to "forall A. * -> A -> A" or "* -> Int -> Int".
  Any thoughts on this?

* p.9: "both relations allow for example forall a. a -> Int to be related with * -> Int, which in our view, is some sort of (implicit) polymorphic subtyping and that should be derivable by the more primitive notions in the type system"
  This seems to contradict the fact that you rule it out in your polymorphic subtyping judgement.
  See also question above.
  Update: this is related to the discussion of coherence in section 4.2.
  It might be a good idea to add a forward reference?

* Please discuss the relation to the following paper, appearing at POPL 2018:
  https://popl18.sigplan.org/event/popl-2018-papers-parametricity-versus-the-universal-type
  https://people.mpi-sws.org/~marcopat/marcopat/Publications_files/poly-seal-no.pdf
  Your polymorphic subtyping judgement seems to exclude the gradual type * (or types containing it) from being used as a type argument to polymorphic functions, which may exclude the counterexample to parametricity discussed in that paper?

* p.15: "Note that matching saves us from having a subsumption rule":
  Your previous discussion about keeping subtyping orthogonal to consistency actually suggests that you could use a subsumption rule for normal subtyping and use consistency in the application rule, which might yield a simpler formulation than your current one using matching.
  In other words, what if you replace App with the following two rules:

    Psi |- e_1 : A     A <: B
    - - - - - - - - - - - - -
    Psi |- e_1 : B
    
    Psi |- e_1 : A   A ~ A_1 -> A_2   Psi |- e_2 : A_1
    - - - - - - - - - - - - - - - - - - - - - - - - - 
    Psi |- e_1 e_2 : A_2

  It seems like this is an equivalent but simpler and more declarative specification of your declarative type system.
  Additionally, it seems more in the spirit of your discussion about keeping subtyping orthogonal to consistency than the matching stuff.

* p.18: "As for the dynamic guarantee": even if you don't prove this guarantee, you should at least mention it!

* p.20, Fig.10, rule ACS-ForallR: what if Theta contains unsolved existential variables?
  Aren't you ignoring potential type ambiguity here?

* p.20: "In practice, one can apply ACS-ForallR eagerly": shouldn't you mandate this, to obtain syntax-directedness and determinacy?
  Also: what happens if you try ACS-ForallL first?

* p.21, Fig.11, rule InstLAllR: what about the scope of b: can you be sure that it's reasonable to instantiate a-hat to types involving b?

* p.23-24, section 6.2: 
  Perhaps a different way to formalize what you seem to propose is to model type inference such that an existential type variable can be either unsolved, or instantiated to a type tau (possibly containing *), but when it is instantiated to a type tau, this solution can still be refined further by replacing it with a type that is directedly consistent with it, for example, * -> * could be instantiated further to (Int -> *) -> *.
  The equivalent of rule InstLSolveU would then actually instantiate ahat to *, but leave open the possibility for refining it further on.
  There may be some relation to abstract interpretation here, where similar information increases happen but for variables instead of types.

* You mention that the dynamic guarantee is an open question, but the coherence issue discussed in section 4.2 quite clearly shows that this guarantee is broken, I think.
  The example

    $(\lambda f : (\forall a. a -> a). \lambda x : Int. f x) (\lambda x. x) 3$

  works fine but

    $(\lambda f : (\forall a. a -> a). \lambda x : *  . f x) (\lambda x. x) 3$

  fails.
  Any reasonable definition of term precision would consider this a less precisely typed term, right?
  In other words, you should not mention the dynamic guarantee as an open question, but as something that is broken by the coherence issue. 

Detailed comments:
* p.3: "Ahmed et al.'s notion of compatibility": you haven't mentioned these names before, so it's not clear you're continuing the discussion on lambda-B here.
* p.3: "all of the static aspects of the refined criteria": what about dynamic aspects?
* p.4: "her
* p.6: "Haskell implements the Damas-Milner rule": perhaps it's worth mentioning that recent GHCs allow you to add type annotations to fix the example.
* p.6: "à posteriori": a posteriori (Latin, not French)
  Again on p.8
* p.8: "According to the syntax in Fig. 3, monotypes do not contain the unknown type": do not include the ...
* p.11, Fig.6: the type on the top right of this diagram should not have the "forall a." any more, right?
* p.12: "for type constructors": what are type constructors in their setting?
* p.12, Prop.3: you might say that consistency is the transitive-symmetric closure of precision.
* p.17: "Coherency": coherence?
* p.18: "it produces more general types": more specific types?
* p.20, Fig.10: what does the notation "Gamma[a-hat]" mean?
  Does it mean that a-hat cannot yet be solved in Gamma?
* p.20: "a notion of information increase from input contexts Gamma to output contexts Delta": please explain a bit more what this means?



Review #70C
===========================================================================

Overall merit
-------------
A. Accept (Good paper. I will champion it at the PC meeting.)

Reviewer expertise
------------------
Y. Knowledgeable

Paper summary
-------------
This paper is about consistent subtyping, as defined by Siek and Taha. This is a relation that comprises classic subtyping and correct conversions of unknown types into more precise ones in gradual type systems (consistency). The authors generalise the notion of consistent subtyping to implicit polymorphic subtyping. As a first outcome of this work, the generalisation of the notion is proved useful to understand previous proposals of subtyping for polymorphic gradual type systems without consistency. The second outcome of the paper is a gradually typed calculus for implicit polymorphism that uses the new notion of consistent subtyping. The calculus is presented in a declarative and an algorithmic version, and they prove that it satisfies all static aspects of the refined criteria for gradual typing.

Comments for author
-------------------
It seems to me that this paper is a breakthrough in understanding the relations and the interplay among subtyping that relates polymorphic types to their instantiations and gradual typing conversion. The paper is extremely well-written, it reads like a novel (the only sentence I was not able to understand is on page 6, line -10, starting with "Finding").

- Questions for the authors -

I am not expert enough to judge if a gradual typing system for Haskell (one of the motivations for your paper you mention) would be desirable, also because here only its core it is considered: in order to extend gradual typing to full Haskell, what other challenges do you envisage?

Could you spend some words on how your approach would extend to explicit polymorphism, as in mainstream object-oriented languages this is the most common form? Would it be possible to maintain the sought orthogonality between subtyping and consistency?
