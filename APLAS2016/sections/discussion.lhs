%include polycode.fmt
%include format.fmt

\section{Discussion and Future Work}
\label{sec:discuss}

\bruno{Generally speaking you have to spend a few hours carefully thinking 
about the arguments you want to make here.}

\paragraph{Making Type-level Computation Convenient}
\bruno{The point here is that programs using intensive type-level 
computation can be written, but are not convenient to use. You 
should show what's inconvenient, and discuss what can be done 
to make it more convenient. You probably want to talk about type-equality, and mention 
that although \name only supports syntactic equality we may be able to support 
a source language that supports a more expressive form of type-equality. Say if we 
can compute how many casts need to be introduced?}
\jeremy{dependent pattern matching, recursive functions on the type level}

Though \name, by design, provides full support for type-level
computation, we are still quite restricted\bruno{not restricted, inconvenient 
to write.}. The problem becomes
pronounced when having recursive functions on the type level. For
example, it is legal to write the following:

< letrec many : * -> * -> Nat -> * =
<   \ a : * . \ b : * . \ n : Nat .
<      case n of
<        Zero => b
<     |  Suc (m : Nat) => a -> many a b m

|many| takes two types and a natural number, produces another type
depending on the number:

< many Nat Bool Z          -- return ``Bool''
< many Nat Bool (S Z)      -- return ``Nat $\rightarrow$ Bool''
< many Nat Bool (S (S Z))  -- return ``Nat $\rightarrow$ Nat $\rightarrow$ Bool''

\bruno{This is what the a system with the conversion rules would return, right? 
What you want to show here is what \name returns, and that you have to use explicit 
casts.}
What might this be useful?\bruno{That's a distracting discussion, just skip 
the zipWith example.} It could be used to write a very simplified
version of variable-arity |zipWith| that takes a number $n$ as arity,
a type $t$, another type $g$, a function of type |many t g n|, $n$
lists of type $t$, and finally returns a list of type $g$:

< zipWith :  (n : Nat) -> (t : *) -> (g : *) -> (many t g n) ->
<            (many (List t) (List g) n)

The problem arises when we try to figure out how many \cast operations
(or beta reductions) are needed for |many| function to compute
something useful (e.g., by analysis, it needs at least 6 |castdown|'s
to be reduced to a function type). 

The solution\bruno{Not "the solution": rather a possible solution.}, as in Haskell we have
type classes and type families to guide the type-level computation, is
to introduce some language constructors in the surface language, of
which the compiler can make use to atomically generate \cast
operations.

\bruno{Is this about GADTs? if so, that's in the wrong-spot.}
Under the presence of inductive families of datatypes (e.g.,
length-fixed vectors), our translation of pattern matching is far too
clumsy. In short, it does not take into consideration the information
embedded in the dependent types. In the future work, we plan to
incorporate Conor McBride's ideas on eliminating dependent pattern
matching~\cite{elim:pi:pattern} into our work.

\paragraph{Eliminating Cast Values}

Explicit type \cast operators $[[castup]]$ and $[[castdown]]$ are
generalized from $[[fold]]$ and $[[unfold]]$ of iso-recursive
types. By convention, $[[castup]]$ follows $[[fold]]$ as a value, so
it cannot be further reduced during the evaluation. This choice may 
lead to unexpected semantics in some cases, and performance issues.

In terms of semantics, suppose there is a non-terminating term
$\mathit{loop}$. If $\mathit{loop}$ is
wrapped by $[[castup]]$ like $[[castup]]~[ [[t]] ]~\mathit{loop}$, the
evaluation stops immediately. So the dynamic semantics of a term-level
expression wrapped by $[[castup]]$ might differ from the wrapped term. The
performance issue may occur during code generation. Since $[[castup]]$
will remain after evaluation, too many $[[castup]]$ constructs can
increase the size of the program and cause runtime overhead.

In fact, \cast operators can be safely eliminated after type checking,
because they do not actually transform a term other than changing its
type. 
%There are two choices of when to remove \cast operators, during
%evaluation or code generation. 
An alternative operational semantics would be to have reduction
rules eliminate casts during evaluation:
\ottusedrule{\ottdruleSXXCastUpE{}}
\ottusedrule{\ottdruleSXXCastDownE{}} This way $[[castup]]$ is no
longer treated as a value. With such modification, we can obtain
$[[castup]]~[ [[t]] ]~\mathit{loop} [[-->]] \mathit{loop}$. So
$[[castup]]$ will not interfere with the original dynamic semantics of
terms. 

However, there is also a problem with this approach: 
$[[castup [t] e]]$ or $[[castdown e]]$ have
different types from $[[e]]$. Therefore types of terms are not preserved during
evaluation. This breaks the subject reduction theorem, and
consequently type-safety.

Therefore, we stick to the semantics of iso-recursive types for \cast
operators which has type preservation. This way explicit casts and
recursion can genuinely be seen as a generalization of recursive
types. Furthermore, we believe that all \cast operators can be
eliminated through type erasure, when generating code,
to address the potential performance issue of code generation.

\paragraph{Encoding of GADTs}
\bruno{The point is again to show how Fin could be encoded using \name, 
and show a program using case analysis that should be valid but does 
not type-check. In principle this should happen due to the lack of 
equality proofs and type-constructor injectivity. Mention that this is part 
of our future work plan.}
Our translation rules also open opportunity for encoding GADTs. In our
experiment, we have several running examples of encoding GADTs. Below
we show a GADT-encoded representation of well-scoped lambda terms
using de Bruijn notation.

In this notation, a variable is represented as a number -- its de
Bruijn index, where the number $k$ stands for the variable bound by
the $k$'s enclosing $\lambda$. Using the GADT syntax, below is the
definition of lambda terms:

< data Fin : Nat -> * =
<      fzero : (n : Nat) -> Fin (S n)
<   |  fsucc : (n : Nat) -> Fin n -> Fin (S n);
<
< data Term : Nat -> * =
<      Var : (n : Nat) -> Fin n -> Term n
<   |  Lam : (n : Nat) -> Term (S n) -> Term n
<   |  App : (n : Nat) -> Term n -> Term n -> Term n;
\bruno{Show Fin only: no need for |Term|.}
The datatype \emph{Fin n} is used to restrict the the de Brujin index,
so that it lies between $0$ to $n - 1$. The type of a closed term is
simply |Term Z|, for instance, a lambda term
$\lambda x.\,\lambda y.\, x$ is represented as (for the presentation,
we use decimal numbers instead of Peano numbers):

< Lam 0 (Lam 1 (Var 2 (fsucc 1 (fzero 0))))

If we accidentally write the wrong index, the program would fail to
pass type checking.


We do not have space to present a complete encoding, but instead show
the encoding of \emph{Fin}:

< let Fin : Nat -> * =
<   mu X : Nat -> * . \ a : Nat .
<     (B : Nat -> *) ->
<     ((n : Nat) -> B (S n)) ->
<     ((n : Nat) -> X n -> B (S n)) ->
<     B a

\jeremy{issues of encoding GADTs, because of equality, injectivity of type constructors?}

% The key issue in encoding GADTs lies in type of variable $B$. In
% ordinary datatype encoding, $B$ is fixed to have type $\star$, while
% in GADTs, its type is the same as the variable $X$ (possibly
% higher-kinded). Currently, we have to manually interpret the type
% according to the particular use of some GADTs. We are investigating if
% there exits a general way to do that.
