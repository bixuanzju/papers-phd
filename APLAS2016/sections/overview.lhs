%include polycode.fmt
%include forall.fmt
%include format.fmt

\section{Overview}

In this section, we informally introduce the main features of \name. In
particular, we show how the casts in \name can be
used instead of the typical conversion rule present in calculi such as
the calculus of constructions. The formal details of \name are
presented in Section~\ref{sec:ecore} and \ref{sec:full}.

\subsection{The Calculus of Constructions and the Conversion Rule}
\label{sec:coc}

The calculus of constructions (\coc)~\cite{coc} is a
higher-order typed lambda calculus supporting dependent types (among
various other features).  A crucial
feature of \coc is the \emph{conversion rule}:
\[\cocconv{}\]
% For the most part \name is similar to the \emph{Calculus of Constructions}
%(\coc)~\cite{coc}, which is a higher-order typed lambda calculus.
%However unlike \name and \coc is the
%absence of a conversion rule 
It allows one to derive $e:[[t2]]$ from the
derivation of $e:[[t1]]$ and the beta equality of $[[t1]]$ and
$[[t2]]$. This rule is important to \emph{automatically} allow terms
with beta equivalent types to be considered type-compatible. For
example, consider the following identity function:
\[f = [[\y:(\x:star.x)int.y]]\] The type of $y$
is a \emph{type-level}
identity function applied to $[[int]]$. Without the conversion rule,
$f$ cannot be applied to $3$ for example, since the type of $3$
($[[Int]]$) differs from the type of $y$ ($[[(\x:star.x)int]]$). Note that the
beta equivalence
$ [[(\x:star.x)int =b int]] $ holds.
The conversion rule allows the application of $f$ to $3$ by
converting the type of $y$ to
$
[[Int]]
$.

\paragraph{Decidability of Type Checking and Strong Normalization}
While the conversion rule in \coc brings a lot of convenience, an
unfortunate consequence is that it couples decidability of type
checking with strong normalization of the
calculus~\cite{pts:normalize}.  Therefore adding general recursion to
\coc becomes difficult, since strong normalization is lost.  Due to
the conversion rule, any non-terminating term would force the type
checker to go into an infinite loop (by constantly applying the
conversion rule without termination), thus rendering the type system
undecidable. For example, assume a term $z$ that has type
$\mathsf{loop}$, where $\mathsf{loop}$ stands for any diverging
computation. If we type check % the following application
$ [[(\x:int . x) z]] $
under the normal typing rules of \coc, the type checker would get
stuck as it tries to do beta equality on two terms: $[[int]]$ and
$\mathsf{loop}$, where the latter is non-terminating.

\subsection{An Alternative to the Conversion Rule: Iso-Types}
\label{subsec:cast}

In contrast to the conversion rule of \coc, \name features
\emph{iso-types}, making it explicit as to when and where
to convert one type to another. Type conversions are explicitly controlled by
two language constructs: $[[castdown]]$ (one-step reduction)
and $[[castup]]$ (one-step expansion). The benefit of this approach is
that decidability of type checking is no longer coupled with strong
normalization of the calculus.

\paragraph{Reduction} The $[[castdown]]$ operator allows a type
conversion provided that the resulting type is a \emph{reduction}
of the original type of the term. To explain the use of
$[[castdown]]$, assume an identity function $g$ defined by
$ g = [[\y:int.y]] $
and a term $[[e]]$ such that
$ [[e]] : [[(\x:star.x)int]] $.
In contrast to \coc,
we cannot directly apply $g$ to $[[e]]$ in \name 
since the type of $e$ ($[[(\x:star.x)int]]$) is not 
\emph{syntactically equal} to |Int|.
However, note that the reduction relation
$ [[(\x:star.x)int --> int]] $ holds.
We can use $[[castdown]]$ for the explicit (type-level)
reduction:
\[ [[castdown e]] : [[int]] \]
Then the application $g\,([[castdown e]])$ type checks.

\paragraph{Expansion} The dual operation of $[[castdown]]$ is
$[[castup]]$, which allows a type conversion provided that the
resulting type is an \emph{expansion} of the original type of the
term. To explain the use of $[[castup]]$, let us revisit the example
from Section~\ref{sec:coc}. We cannot apply $f$ to $3$ without the
conversion rule.
Instead, we can use $[[castup]]$ to expand the type of $3$:
\[ ([[castup[(\x:star.x)int] three]]): [[(\x:star.x)int]] \]
Thus, the application $f~([[castup[(\x:star.x)int] three]])$ becomes
well-typed. Intuitively, $[[castup]]$ performs expansion, as the
type of $3$ is $ [[int]] $, and $ [[(\x:star.x)int]] $ is the 
expansion of $[[int]]$ witnessed by
$ [[(\x:star.x)int --> int]]$. Notice that for
$[[castup]]$ to work, we need to provide the resulting type as
argument. This is because for the same term, there may be more than one
choice for expansion. For example, $1 + 2$ and $2 + 1$ are both the
expansions of $3$. 

\paragraph{One-Step}
The \cast rules allow only \emph{one-step} reduction or expansion.
If two type-level terms require more than one step of reductions or
expansions for normalization, then multiple casts must be used.
Consider a variant of the example such that
$ e: [[(\x : star . \y:star. x) int bool]] $.
Given $g = [[\y:int.y]]$, the expression $g~[[(castdown e)]]$
is ill-typed because $[[castdown e]]$ has
type $[[(\y : star. int) bool]]$, which is not syntactically equal to
$[[int]]$. Thus, we need another $[[castdown]]$:
\[ [[castdown (castdown e)]] : [[Int]] \]
to further reduce the type and allow the program $g~[[(castdown (castdown e))]]$ to type check.

% These fine-tuned \cast rules gain us more control over type-level
% computation. The full technical details about \cast rules are
% presented in Section~\ref{sec:ecore}.

\paragraph{Decidability without Strong Normalization}

With explicit type conversion rules the decidability of type checking
no longer depends on the strong normalization property.  Thus the type
system remains decidable even in the presence of non-termination at
type level. Consider the same example using the term $z$ from
Section~\ref{sec:coc}. This time the type checker will not get stuck when
type checking $ [[(\x:int . x) z]]$.
This is because in \name, the type checker only performs syntactic
comparison between $[[int]]$ and $\mathsf{loop}$, instead of beta
equality. Thus it rejects the above application as ill-typed. Indeed
it is impossible to type check such application even with the use of
$[[castup]]$ and/or $[[castdown]]$: one would need to write infinite
number of $[[castdown]]$'s to make the type checker loop forever
(e.g., $([[\x:int.x]])([[castdown]]([[castdown]] \dots z))$). But it
is impossible to write such program in practice.

\begin{comment}
In summary, \name achieves decidability of type checking by
explicitly controlling type-level computation using casts. Since each 
cast performs only one step of computation at a time, type-level
computation performed by each cast is guaranteed to terminate.
\end{comment}

\paragraph{Variants of Casts}
A reduction relation is used in cast operators to convert types. 
We study two possible reduction relations: call-by-name
\emph{weak-head reduction} and \emph{full reduction}. Weak-head reduction
cannot reduce sub-terms at certain positions (e.g., inside $\lambda$
or $\Pi$ binders), while full reduction can reduce sub-terms at any
position. We define two variants of casts, namely \emph{weak} and
\emph{full} casts, by employing weak-head and full reduction
respectively. We also create two variants of \name, namely \ecore and
\namef. The only difference is that \ecore uses weak-head
  reduction in weak cast operators $[[castup]]$ and $[[castdown]]$,
while \namef uses full reduction, specifically \emph{parallel reduction}, in full cast operators
$[[castupf]]$ and $[[castdownf]]$. Both variants reflect the idea of
iso-types, but have trade-offs between simplicity and expressiveness:
\ecore uses the same call-by-name reduction for both casts and
evaluation to keep the system and metatheory simple, but loses some
expressiveness, e.g. cannot convert $\mathit{Vec}~(1+1)$ to
$\mathit{Vec}~2$. \namef is more expressive but results in a more
complicated metatheory (see Section \ref{sec:full:meta}). Note that when generally referring to \name, we
do not specify the reduction strategy, which could be either variant.

\subsection{General Recursion}
\label{sec:overview:recursion}

\name supports general recursion and allows writing unrestricted
recursive programs at term level. The recursive construct is also used
to model recursive types at type level. Recursive terms and types 
are represented by the same $\mu$ primitive.

\paragraph{Recursive Terms}

The primitive $[[mu x:t.e]]$ can be used to define recursive functions.  For
example, the factorial function would be written as:
\[
    \mathit{fact} = \mu f:[[Int -> Int]].~\lambda x : [[Int]].~\kw{if}
    ~x==0~\kw{then}~1~\kw{else}~x \times \mathit{f}~(x - 1) \]
% \begin{small}
% < fact =  mu f : Int -> Int. \x : Int . if x == 0 then 1 else x time f (x - 1)
% \end{small}
% \bruno{show how to use fact} \jeremy{Linus already has an exmaple of
%   using fact step by step in Section~\ref{subsec:recur}, still need
%   here?} 
We treat the $\mu$ operator as a \emph{fixpoint}, which evaluates
$[[mu x:t.e]]$ to its recursive unfolding $e [x \mapsto [[mu x:t.e]] ]$.
Term-level recursion in \name works as in any standard functional
language, e.g., |fact 3| produces |6| as
expected (see Section \ref{sec:ecore:twoface}). 

% The dynamic semantics of $\mu$ requires the recursive binder to satisfy (omit type annotations for clarity):  \[ \mu f.\,E = (\lambda f.\,E) (\mu f.\,E) \] which, however, does not terminate in strict languages. Therefore, to loosen the function-type restriction to allow any types, the sensible choice for the evaluation strategy is \emph{call-by-name}.

\paragraph{Recursive Types}
The same $\mu$ primitive is used at the type level to represent
iso-recursive types~\cite{eqi:iso}. In the
\emph{iso-recursive} approach a recursive type and its unfolding are
different, but isomorphic. The isomorphism is witnessed by two
operations, typically called \fold and \unfold. In \name, such
isomorphism is witnessed by $[[castup]]$ and $[[castdown]]$. 
In fact, $[[castup]]$ and $[[castdown]]$
\emph{generalize} \fold and \unfold: they can convert any types, not
just recursive types, as we shall see in the example of encoding
parametrized datatypes in Section \ref{sec:fun}.
\begin{comment}
To demonstrate the use of casts with recursive types, we
show the formation of the ``hungry'' type~\cite{tapl}
$H = [[mu x:star.int -> x]]$. A term $z$ of type $H$ will accept one
more integer every time when it is unfolded by a $[[castdown]]$:
% accepts any
% number of integers and returns a new function that is hungry for more,
% as illustrated below:
\begin{align*}
[[(castdown z) three]] &: H  \\
[[castdown((castdown z) three) three]] &: H \\
[[castdown]](\dots ([[castdown z]])\,3 \dots)\,3 &: H
\end{align*}
\end{comment}

% <       #b : * . b -> (a -> List a -> b) -> b
% <  <~~  (\a : * . #b : * . b -> (a -> List a -> b) -> b) a
% <  <~~  (/L : * -> * . \a : * . #b : * . b -> (a -> L a -> b) -> b) a

% Due to the unification of recursive types and recursion, we can use
% the same $\mu$ primitive to write both recursive types and recursion
% with ease.

% \paragraph{Call-by-Name}
% Due to the unification, the \emph{call-by-value} evaluation strategy
% does not fit in our setting. In call-by-value evaluation, recursion
% can be expressed by the recursive binder $\mu$ as $\mu f : T
% \rightarrow T.\, E$ (note that the type of $f$ is restricted to
% function types). Since we don't want to pose restrictions on the
% types, the \emph{call-by-name} evaluation is a sensible choice.
% \bruno{Probably needs to be improved. I'll came back to this later!}

% \subsection{Logical Inconsistency}
% Although the decidability of type-checking is preserved, a consequence
% having general recursion in \name is that the logical consistency is
% lost. In \name every type is inhabited, which is problematic if we
% want to view \name as a logic. Indeed, unlike many other dependently 
% calculi which have been proposed in the past, \name cannot be used 
% directly to do theorem proving.

% Nevertheless the loss of logical consistency is a deliberate design
% decision. Although there are dependently typed languages that support
% general recursion and still preserve logical consistency, this is done
% at the cost of additional complexity in the
% system~\cite{zombie:popl14, Swamy2011, fstar}. In \name we trade the
% loss of logical consistency by a significantly simpler system.

% Since our goal is 
% use \name as a foundational calculus for languages like Haskell,
% logical consistency is not an important property: traditional 
% functional languages like Haskell are logically inconsistent as well. 
% For example, in Haskell, we can write a ``false'' type:

% < type False = forall a. a

% With general recursion, a value with type |False| is given:

% < false  ::  False
% < false  =   false

% whose denotational semantics is |undefined|, which corresponds to
% inconsistency in logic. 

% \paragraph{Type in Type}
% \linus{Duplicated.}
% Since logical consistency is already lost due to general recursion,
% \name also uses the $\star : \star$ axiom~\cite{handbook}. As a
% consequence, having this rule adds expressiveness and simplifies our
% system (e.g., it will be easy to explicitly quantify over kinds). We
% return to this issue in Section~\ref{sec:related}.

\begin{comment}
\subsection{Encoding Datatypes}
The explicit type conversion rules and the $\mu$ primitive facilitate
the encoding of recursive datatypes and recursive functions over
datatypes. While inductive datatypes can be encoded using either the
Church~\cite{tapl} or the Scott~\cite{encoding:scott} encoding, we
choose to work with the Scott encoding as it encodes case analysis,
making it more convenient to encode pattern matching. The formal
treatment of encoding datatypes is presented in
Section~\ref{sec:surface}.\bruno{Move this text to somewhere in Section 5.}
\end{comment}



\begin{comment}

  We demonstrate the encoding method using a simple datatype as a
running example: Peano numbers. The datatype declaration for Peano
numbers in Haskell is:

<  data Nat = Z | S Nat

The Scott encoded datatype |Nat| reflects how its two constructors are
going to be used. Since |Nat| is a recursive datatype, we have to use
recursive types at some point to reflect its recursive nature. As it
turns out, the typed Scott encoding of |Nat| is:

< mu X : * . (b : *) -> b -> (X -> b) -> b

The function type |(b -> (X -> b) -> b)| demystifies the recursive
nature of |Nat|: the first argument of type $b$ corresponds to the type of the constructor |Z|,
and |X -> b| corresponds to the type of the constructor |S|. The
intuition is that any recursive use of the datatype in the data
constructors is replaced with a variable ($X$ in this case) bound by
$\mu$. Moreover, the resulting type variable ($b$ in this case) is
universally quantified so that elements of the datatype with different
result types can be used in the same program.

The two constructors of |Nat| can be encoded correspondingly via the \cast rules:

< Z = castup[Nat] (\ b : * . \ z : b . \ f : Nat -> b . z)
< S = \ n : Nat .  castup[Nat]
<                  (\ b : * . \ z : b . \ f : Nat -> b . f n)

Intuitively, each constructor selects a different function from the
function parameters ($z$ and $f$ in the above example). This provides
branching in the process flow, based on the constructors. However, note that we
use $[[castup]]$ to do type conversion between the recursive type and
its unfolding.

Finally a recursive function that adds two natural numbers can be
defined as:

< mu f : Nat -> Nat -> Nat . \ n : Nat . \ m : Nat .
<     (castdown n) Nat m (\ n' : Nat . S (f n' m))

The above definition resembles case analysis commonly seen in modern
functional programming languages. If we take apart the
definition, we see that the use of $[[castdown]]$ plays an
important role. First of all, recall that |Nat| is
encoded as:

< mu X : * . (b : *) -> b -> (X -> b) -> b

Then |castdown n| reduces the above to

< (b : *) -> b -> (Nat -> b) -> b

which matches the types of the terms applied to |castdown n|: the
result type is |Nat|; $m$ is used for the base case; and |\ n' : Nat
. S (f n' m)| the recursive step.

\end{comment}

% The formal treatment of encoding case analysis is presented in
% Section~\ref{sec:surface}.



%%% Local Variables:
%%% mode: latex
%%% TeX-master: "../main"
%%% End:
