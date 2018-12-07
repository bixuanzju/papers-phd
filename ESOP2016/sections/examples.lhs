%include polycode.fmt
%include format.fmt

\section{\sufcc: A Surface Language on Top of \name}
\label{sec:app}

The main goal of \name is to serve as an expressive core language
for functional languages like Haskell or ML.
This section shows a number of programs written in the surface
language \sufcc, which is built on top of \name. We illustrate the
expressiveness of \name by encoding functional programs that require
some of the latest features of Haskell, or are
non-trivial to encode in a dependently typed language like Coq or
Agda. All examples shown in this section are runnable in our prototype
interpreter. The formalization of the surface language is presented in
Section~\ref{sec:surface}.

\begin{comment}
\subsection{Parametric HOAS}
\label{sec:phoas}

Parametric Higher Order Abstract Syntax (PHOAS) is a higher order
approach to represent binders, in which the function space of the
meta-language is used to encode the binders of the object language. We
show that \name can handle PHOAS by encoding lambda calculus as below:

\begin{figure}[h!]
\begin{spec}
data PLambda (a : *) = Var a
   | Num nat
   | Lam (a -> PLambda a)
   | App (PLambda a) (PLambda a);
\end{spec}
\end{figure}

Next we define the evaluator for our lambda calculus. One advantage of
PHOAS is that, environments are implicitly handled by the
meta-language, thus the type of the evaluator is simply |plambda value
-> value|. The code is presented in Figure~\ref{fig:phoas}.

\begin{figure}[ht]
\begin{spec}
data Value  = VI nat
   | VF (Value -> Value);
let eval : PLambda Value -> Value =
   mu ev : PLambda Value -> Value .
     \ e : PLambda Value . case e of
       Var (v : Value) => v
     | Num (n : nat)   => VI n
     | Lam (f : Value -> PLambda Value) =>
         VF (\ x : Value . ev (f x))
     | App (a : PLambda Value) (b : PLambda Value) =>
        case (ev a) of
          VI (n : nat)            => VI n -- impossible to reach
        | VF (f : Value -> Value) => f (ev b)
in
\end{spec}
  \caption{Lambda Calculus in PHAOS}
  \label{fig:phoas}
\end{figure}

Now we can evaluate some lambda expression and get the result back as
in Figure~\ref{fig:pex}

\begin{figure}[ht]
\begin{spec}
let show : Value -> nat =
  \ e : Value . case e of
    VI (n : nat)            => n
  | VF (f : Value -> Value) => 10000 -- impossible to reach
in
let example : PLambda Value =
  App Value
      (Lam Value (\ x : Value . Var Value X))
      (Num Value 42)
in show (eval example) -- return 42
\end{spec}
\caption{Example of using PHOAS}
\label{fig:pex}
\end{figure}
\end{comment}

\paragraph{Datatypes}
Conventional datatypes like natural numbers or polymorphic lists can
be easily defined in \sufcc. For instance, below is the
definition of polymorphic lists:

<  data List (a : *) = Nil | Cons (x : a) (xs : List a);

% Because \sufcc is explicitly typed, each parameter needs to be
% accompanied with a corresponding kind or type annotation.
The use of the above datatype is illustrated by the |length|
function:

< letrec length : (a : *) -> List a -> int =
<   \ a : * . \l : List a . case l of
<      Nil => 0
<   |  Cons (x : a) (xs : List a) => 1 + length a xs in
< let test : List int = Cons int 1 (Cons int 2 (Nil int))
< in length int test -- returns 2

The |length| function is recursive. \sufcc supports a standard
|letrec| construct that facilitates defining recursive functions.  The
return type of |length| is |int|, the built-in integer type.  Note
that due to explicit typing, the program requires quite a few type
annotations and type parameters. However, apart from the extra typing,
the program is similar to the code that would be written in a language
like Haskell or ML.

\paragraph{HOAS}
\emph{Higher-order abstract syntax}~\cite{hoas} is a representation of
abstract syntax where the function space of the meta-language is used
to encode the binders of the object language. We show an example of
encoding a simple lambda calculus:

< data Exp = Num (n : int)
<   |  Lam (f : Exp -> Exp)
<   |  App (a : Exp) (b : Exp);

Note that in the lambda constructor (|Lam|), the recursive occurrence
of |Exp| appears in a negative position (i.e., in the left side of a
function arrow).  Systems like Coq and Agda would reject such programs
since it is well-known that such datatypes can lead to logical
inconsistencies. Moreover, such logical inconsistencies can be
exploited to write non-terminating computations, and make
type checking undecidable. However \sufcc is able to express HOAS in a
straightforward way, while preserving decidable type checking.

Using |Exp| we can write an evaluator for the lambda calculus. As
noted by Fegaras and Sheard~\cite{Fegaras1996}, the evaluation function needs an extra
function |(reify)| to invert the result of evaluation. The code for
the evaluator is shown next (we omit most of the unsurprising cases):

< data Value = VI (n : int) | VF (f : Value -> Value);
< rcrd Eval = Ev  {  eval'   : Exp    -> Value , reify'  : Value  -> Exp };
< letrec ev : Eval =
<   Ev  (\ e : Exp . case e of
<       | ...
<       | Lam (fun : Exp -> Exp) =>
<           VF (\e' : Value . eval' ev (fun (reify' ev e')))
<       (\v : Value . case v of
<       | ...
<       | VF (fun : Value -> Value) =>
<           Lam (\e' : Exp . reify' ev (fun (eval' ev e')))
< in let eval : Exp -> Value = eval' ev

The definition of the evaluator is mostly straightforward. Here we
create a record |Eval| (by using |rcrd| keyword), inside which are two
mutually recursive functions |eval'| and |reify'|. The former one is
conventional, dealing with each possible shape of an expression. The
tricky part lies in the evaluation of a lambda abstraction, where we
need a second function, called |reify'|, of type |Value -> Exp| that
lifts a values into terms. Thanks to the
flexibility of the $\mu$ primitive, mutual recursion can be encoded by
using records.

Evaluation of a lambda expression proceeds as follows:

< let test : Exp = App  (Lam (\ f : Exp . App f (Num 42))) (Lam (\g : Exp. g))
< in show (eval test) -- return 42


\paragraph{Higher-kinded Types}
Higher-kinded types are types that take other types and produce a new
type. To support higher-kinded types, languages like Haskell use
core languages that account for kind expressions.
The existing core language of Haskell, System $F_{C}$, is an extension of
System $F_{\omega}$~\cite{systemfw}, which natively supports
higher-kinded types. Given that \name subsumes System $F_{\omega}$, we can
easily construct higher-kinded types. We show with an example of
encoding the \emph{functor} ``type-class'' as a record:

< rcrd Functor (f : * -> *) =
<   Func {fmap : (a : *) -> (b : *) -> (a -> b) -> f a -> f b};

Here we use a record to represent a functor, whose only field is a
function called |fmap|. The functor ``instance'' of the |Maybe|
datatype is:

< let maybeInst : Functor Maybe =
<   Func Maybe (\ a : * . \ b : * . \f : a -> b . \ x : Maybe a .
<     case x of
<       Nothing => Nothing b
<    |  Just (z : a) => Just b (f z))

After the translation process, the |Functor| record is desugared into a
datatype with only one data constructor (|Func|) that has type:

< (f : * -> *) -> (a : *) -> (b : *) -> (a -> b) -> f a -> f b

Since |Maybe| has kind $[[star -> star]]$, it is legal to apply |Func|
to |Maybe|. The definition of |fmap| is straightforward.

\begin{comment}
\paragraph{Fixpoints of Functors}
Various functional programming techniques employ type-level fixpoints
to achieve additional modularity~\cite{datatype}. Thus, type-level
fixpoints are a good example to demonstrate the expressiveness of
\sufcc. The definition is:

< rcrd Fix (f : * -> *) = In {out : f (Fix f) };

Note that the record notation also introduces the selector function:

< out : (f : * -> *) -> Fix f -> f (Fix f)

The |Fix| datatype is interesting in that we can define recursive
datatypes in a non-recursive way. For instance, a non-recursive
definition for natural numbers is:

< data NatF (self : *) = Zero | Succ (n : self);

And the recursive version is just a synonym:

< let Nat : * = Fix NatF

Given |fmap|, many recursion schemes can be defined. For example we
can have a \emph{catamorphism} (or generic 
fold function)~\cite{Meijer1991}:

< letrec cata :  (f : * -> *) -> (a : *) ->
<                Functor f -> (f a -> a) -> Fix f -> a =
<   \f : * -> * . \ a : * .
<     \ m : Functor f .  \ g : f a -> a. \ t : Fix f .
<        g (fmap f m (Fix f) a (cata f a m g) (out f t))


Unfortunately, in systems like Coq, definitions like |Fix| must be
rejected. The problem is related to strictly positive
types~\cite{spt}. That is, Coq cannot determine whether |Fix f| (for
any abstract functor $f$) is strictly positive or not. For example, we
can write a non-strictly positive functor in \sufcc:

< data Bad (a : *) = B (f : (Bad a -> nat) -> nat);

Inspecting the definition of |Fix Bad| reveals that the resulting
datatype is non-strictly positive:

< data NSP = N (f : (NSP -> nat) -> nat);

Similarly to the HOAS example, this would violate the strictly
positive restrictions of Coq. Nevertheless, in \sufcc such definition
is also allowed without hindering decidability of type checking.

\end{comment}

\begin{comment}
Note that now we can use the above \emph{Nat} anywhere, including the
left-hand side of a function arrow, which is a potential source of
non-termination. The termination checker of Coq or Agda is so
conservative that it would reject the definition of
\emph{Fix} to avoid the above situation.
However in \sufcc, where type-level computation is
explicitly controlled, we can safely use \emph{Fix} in the program.
\end{comment}

\paragraph{Nested Datatypes}
A nested datatype~\cite{nesteddt}, also known as a \emph{non-regular}
datatype, is a parameterized datatype whose definition contains
different instances of the type parameters. Functions over nested
datatypes usually involve polymorphic recursion. We show that \sufcc
is capable of defining nested datatypes and functions over a nested
datatype. A simple example would be the type |Pow| of power trees,
whose size is exactly a power of two, declared as follows:

< data PairT (a : *) = P (x : a) (x : a);
< data Pow (a : *) = Zero (n : a) | Succ (t : Pow (PairT a));

Notice that the recursive occurrence of |Pow| does not hold |a|, but
|PairT a|. This means every time we use a |Succ| constructor, the size
of the pairs doubles. It is instructive to look at the encoding of
|Pow| in \name:

< let Pow : * -> * = mu X : * -> * .
<     \ a : * . (b : *) -> (a -> b) -> (X (PairT a) -> b) -> b

Notice how the higher-kinded type variable |(X : * -> *)| helps
encoding nested datatypes. Below is a polymorphic recursive function
|toList| that transforms a power tree into a list:

< letrec toList : (a : *) -> Pow a -> List a =
<   \a : * . \t : Pow a . case t of
<      Zero (x : a) => Cons a x (Nil a)
<   |  Succ (c : Pow (PairT a)) => concatMap (PairT a) a
<       (\ x : PairT a . case x of
<        P (m : a) (n : a) =>
<         Cons a m (Cons a n (Nil a))) (toList (PairT a) c)


\paragraph{Kind Polymorphism}
Previous versions of Haskell, based on System $F_{\omega}$, had a
simple kind system with a few kinds ($\star$, $\star \rightarrow
\star$ and so on).  Unfortunately, this was insufficient for kind
polymorphism. Thus, recent versions of Haskell were extended to support 
kind polymorphism, which required extending the core language as well.
Indeed, System $F_C^{\uparrow}$~\cite{fc:pro} was proposed to
support, among other things, kind polymorphism. However, System $F_C^{\uparrow}$ separates
expressions into terms, types and kinds, which complicates both the
implementation and future extensions. In contrast, without additional extensions, 
\sufcc natively supports kind polymorphism. Here is an example, taken
from~\cite{fc:pro}, of a datatype that benefits from kind polymorphism:
a higher-kinded fixpoint combinator:

< data Mu (k : *) (f : (k -> *) -> k -> *) (a : k) = Roll (g : f (Mu k f) a);

|Mu| can be used to construct polymorphic recursive types of any kind,
for instance, polymorphic lists:

< data Listf (f : * -> *) (a : *) = Nil | Cons (x : a) (xs : (f a));
< let List : * -> * = \a : * . Mu * Listf a


\paragraph{Datatype Promotion}
Recent versions of Haskell introduced datatype
promotion~\cite{fc:pro}, allowing ordinary datatypes promoted as
kinds, and data constructors as types. With the power of dependent
types, datatype promotion is made trivial in \sufcc.

As a last example, we show a representation of a labeled binary tree,
where each node is labeled with its depth in the tree. Below is the
definition:

< data PTree (n : Nat) = Empty
<   | Fork (z : int) (x : PTree (S n)) (y : PTree (S n));

Notice how the datatype |Nat| is ``promoted'' to be used in the kind
level. Next we can construct a binary tree that keeps track of
its depth statically:

< Fork Z 1 (Empty (S Z)) (Empty (S Z))

If we accidentally write the wrong depth, for example:

< Fork Z 1 (Empty (S Z)) (Empty Z)

The above will fail to pass type checking.
