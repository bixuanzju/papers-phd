%include polycode.fmt
%include format.fmt

%format tri="\triangleright"
%format family="\mathbf{family}"
%format where="\:\mathbf{where}"

\section{Related Work}
\label{sec:related}

%The study of bringing full-spectrum dependent types to the practical
%programming world opens up a wide array of related issues. 
In this paper, we give a positive answer as to whether we can find a calculus
comparable in simplicity to PTS that models key features of modern
functional languages (like Haskell and ML), while preserving type
soundness and decidable type checking. To our knowledge we are the first to do so.

% There is much work on bringing full-spectrum dependent types to the
% practical programming world.  Compared to existing work, the main
% different of our work is that we propose the use of one-step
% explicit casts to control type-level computation. Moreover we also
% unify recursion and recursive types in a single language
% construct. % To aid in comparing our work with other work on dependently typed core languages,
% Figure~\ref{fig:related:comp}\bruno{There is no figure! The text
% needs to be \emph{carefully} revised!} summarizes the key
% differences and similarities between various core languages
% discussed in this section.  The table compares a number of core
% languages with respect to whether they support decidable type
% checking, general recursion and logical consistency. Moreover it
% details what type of equality is supported and how complex the core
% language is in terms of number of syntactic sorts and language
% constructs. The main conclusion is that \name has similar properties
% to System $F_C$, but is significantly simpler.



\begin{comment}
\begin{figure*}
\begin{threeparttable}
% \renewcommand{\arraystretch}{0.5}
\small
\centering
\begin{tabularx}{\textwidth}{XXXXXXlX}
\toprule
&&&& \multicolumn{2}{c}{Complexity} & \\ \cmidrule{5-6}
Core \mbox{Language} & Surface \mbox{Language} & \mbox{Decidable Type} Checking & General \mbox{Recursion} & \# of Language Constructs\tnote{*} & \# of Syntactic Sorts & Logical Consistency & Type-equality \\ \midrule
\name & \sufcc & Yes & Yes & 8 & 1 & No & $\alpha$-equality \\
System $F_C$ & Haskell & Yes & Yes & 32\tnote{**} & 3 & No & $\alpha$-equality \\
\cc & --- & Yes & No & 6 & 1 & Yes & $\beta$-equality \\
$\lambda^\theta$ & \textsf{Zombie} & Yes & Yes & 24 & 1 & Yes, in \textsf{L} Fragment & $\beta$-equality \\
Core Cayenne & Cayenne & No & Yes & 11 & 1 & No & $\beta$-equality \\
$F^\star$ & --- & Yes & Yes & 23 & 3 & Yes, in \textit{P}-fragment & $\beta$-equality \\
$\Pi\Sigma$ & --- & Unknown\tnote{***} & Yes & 18 & 1 & No & $\beta$-equality \\ \bottomrule
% ~\cite{fc}
% ~\cite{handbook}
% ~\cite{zombie:popl14}
% ~\cite{cayenne}
% ~\cite{fstar}
% ~\cite{dep:pisigma}
\end{tabularx}
\begin{tablenotes}
\item[*] Literals such as integers are ignored.
\item[**] Conservative number due to under-specified constructs.
\item[***] No metatheory is given.
\end{tablenotes}
\end{threeparttable}
\caption{Comparison of Core Languages}
\label{fig:related:comp}
\end{figure*}
\end{comment}


\paragraph{Core calculus for functional languages}

System F~\cite{Reynolds:1974} is the simplest foundation for a polymorphic
functional language. While the simplicity of System F is appealing,
many features in use by functional languages, such as recursive
types (which can be added in standard ways) or \emph{higher-kinded
polymorphism} (which requires major changes) are missing.  \name is
comparable in simplicity to System F, while being much more
expressive. Girard's System $F_{\omega}$~\cite{systemfw} is a typed
lambda calculus with higher-kinded polymorphism. Unlike System $F$, it
introduces type operators (type-level functions). To
guarantee the well-formedness of type expressions, an extra level of
\emph{kinds} is added to the system. In comparison, \name is
considerably simpler than System $F_{\omega}$, both in terms of
language constructs and complexity of proofs.  System $F_{\omega}$
differs from \name in that it uses a conversion rule due to its
ability to perform type-level computation. \name can express 
type-computation in $F_{\omega}$, but it requires explicit casts.
Interestingly enough this feature of $F_{\omega}$ is actually not used
by core languages for Haskell, because such core languages do not
include type-level abstractions. Both System $F_{\omega}$ (with some standard extensions) 
and \name can express the key features required for the Haskell 2010 
standard~\cite{marlow2010haskell}. Nevertheless, System
$F_{\omega}$ misses several features in use by modern GHC Haskell. 
In particular, features like kind polymorphism or datatype promotion
would require non-trivial extensions to the system, complicating the
system even more. Those features can be expressed directly in \name.

\name still lacks support for some features of GHC Haskell.  The
current core language for GHC Haskell, System
$F_{C}$~\cite{Eisenberg:2014} is a significant extension of System
$F_{\omega}$, which supports GADTs~\cite{haskellgadt}, functional
dependencies~\cite{Jones00}, type families~\cite{Eisenberg:2014}, and
soon even kind equality~\cite{fc:kind}. These features use a
non-trivial form of type equality, which is currently missing from
\name. On the other hand \name is rather simple, and has only 8
language constructs, whereas System $F_C$ is significantly more
complex and has currently over 30 language constructs. A primary goal
of our future work is to investigate the addition of such forms of
non-trivial type-equality. One key challenge is how to account for
injectivity of type constructors, which is required for GADTs.
Because datatypes are not built-in \name, injectivity of type
constructors requires a different approach from System $F_C$.

% \bruno{we need to compare with System $F_{\omega}$ here; compare complexity; say that \name is already 
% considerably simpler (both in terms of language constructs and complexity of proofs). Also mention that 
% at the same time Fw is has limited expressivness for Functional Programming, as it lacks recursive types 
% and recursion (which can be added in standard ways); moreover it lacks other things like kind polymorphism 
% or datatype promotion (which would require research).  }
% \bruno{I think we should also talk about things like Haskell 2000 to say that we believe that our language 
% has all that is needed to express features in that standard. However it is still missing some features 
% from GHC Haskell; which gets discussed in the paragraph below. Namely features that use non-trivial type equalities, 
% such as GADTs or functional dependencies are still missing.}

% \bruno{Make sure the following is integrated properly with the new theme "Core Calculus for Functional Languages"}


\begin{comment}
The current core language for Haskell, System
$F_{C}$~\cite{Eisenberg:2014}, already supports GADTs~\cite{haskellgadt}, datatype
promotion~\cite{fc:pro}, type families~\cite{Eisenberg:2014}, and soon even kind
equality~\cite{fc:kind}. Nowadays System $F_{C}$ has grown to be a
relatively large and complex core language with over 30 language
constructs. Indeed, one of our primary motivations is to develop a
simpler alternative to System $F_C$. Throughout the paper, we have
shown many features that are easy to implement in \name. That being
said, there are still many important aspects of Haskell that we have
not modeled in \name. One feature that requires further study is
GADTs. Many GADT definitions require injectivity of type
constructors, as well as equality constraints~\cite{Cheney-Hinze:2003}.  Because
datatypes are not built-in to \name, injectivity of type constructors
will require a different approach from System $F_C$.
\end{comment}

\paragraph{Casts for managed type-level computation}
Type-level computation in \name is controlled by explicit casts.
Several studies~\cite{guru,sjoberg:msfp12, kimmel:plpv, zombie:popl15,
fc} also attempt to use explicit casts for managed type-level
computation. However, casts in those approaches require
\emph{equality proof terms}, while casts in \name do not. The need for
equality proof terms complicates the language design because: 1)
building equality proofs requires various other language constructs,
adding to the complexity of the language design and metatheory; 2) It
is desirable to ensure that the equality proofs are valid. Otherwise,
one can easily build bogus equality proofs with non-termination, which
could endanger type safety. To solve the later problem,
Zombie~\cite{zombie:popl14, zombie:thesis} contains a logical fragment
as a consistent sub-language that guarantees equality proofs are valid. Other approaches include
restricting valid equality proofs to be syntactic values
only~\cite{sjoberg:msfp12, zombie:popl15}, or having different
languages for proofs and terms~\cite{kimmel:plpv, guru}. 

% This
% is in the same spirit as Haskell, where System $F_C$ uses syntactic
% type-level equality and explicit equality coercions to control
% type-level computation.  This is in contrast to Coq and Agda, which
% require no coercions or casts due to the conversion rule. In the
% future we hope to investigate surface language mechanisms to express
% type-level computation conveniently, similarly to what type families
% accomplish in Haskell.

\paragraph{Unified syntax with decidable type-checking}
Pure Type Systems~\cite{pts} show how a whole family of type
systems can be implemented using just a single syntactic form. PTSs are
an obvious source of inspiration for our work. Although this paper
presents a specific system based on \coc, it should be easy to
generalize \name in the same way as PTSs and further show the
applicability of our ideas to other systems. An early attempt of using a PTS-like syntax 
for an intermediate language
for functional programming was Henk~\cite{pts:henk}. The Henk proposal
was to use the \emph{lambda cube} as a typed intermediate language,
unifying all three levels. However the authors 
have not studied the addition of general recursion nor full dependent types.

\textsf{Zombie}~\cite{zombie:popl14, zombie:thesis} is a dependently
typed language using a single syntactic category. An interesting
aspect of Zombie is that it is composed of two fragments: a logical
fragment where every expression is known to terminate, and a
programmatic fragment that allows general recursion. Even though Zombie has
one syntactic category, it is still fairly complicated (with around 24
language constructs) as it tries to be both consistent as a logic and
pragmatic as a programming language. The logical and programmatic fragments in
Zombie are \emph{tightly coupled}. Thus it's hard to remove language constructs 
even if we are only interested in modeling a programmatic fragment. For example, in Zombie, the
conversion rule (TConv) for the programmatic part depends on equality
proofs, which are only available in the logical part. In contrast to Zombie, 
\name takes another point of the design space, giving up logical consistency for
simplicity in the language design. 

\paragraph{Unified syntax with general recursion and undecidable type
checking} Cayenne~\cite{cayenne} is a programming language that
integrates the full power of dependent types with general
recursion. It bears some similarities with \name: Firstly, it also
uses one syntactic form for both terms and types. Secondly, it allows
arbitrary computation at type level. Thirdly, because of unrestricted
recursion allowed in the system, Cayenne is logically
inconsistent. However, the most crucial difference from \name is that
type checking in Cayenne is undecidable. From a pragmatic point of
view, this design choice simplifies the implementation, but the
desirable property of decidable type checking is lost. Cardelli's
Type:Type language~\cite{typeintype} also features general recursion.
He uses general recursion to implement equi-recursive types,
thus unifying recursion and recursive types in a single
construct. However, both equi-recursive types and the Type:Type axiom
make the type system undecidable. In contrast \name 
generalizes iso-recursive types to control type-level computation and
make type-checking decidable. $\Pi\Sigma$~\cite{dep:pisigma} is
another example of a language that uses one recursion mechanism for both types and
functions, but it does not support decidable type checking either.

\paragraph{Restricted recursion with termination checking}

Dependently typed languages such as Coq~\cite{coqsite} and
Adga~\cite{agda} are conservative as to what kind
of computation is allowed. Coq, as a proof system,
requires all programs to terminate by means of a termination checker,
ensuring that recursive calls are only allowed on \emph{syntactic
  subterms} of the primary argument. Thus decidable type checking, as well as logical consistency,
are also preserved. The conservative, syntactic criteria is insufficient to support a variety of important
programming paradigms. Agda and Idris~\cite{idris}, in addition, offer
an option to disable the termination checker to allow for writing
arbitrary functions. This, however, costs us both decidable
type checking and logical consistency. While logical consistency is
an appealing property, it is not a goal of \name. Instead \name 
aims at retaining (term-level) general recursion as found 
in languages like Haskell or ML, while benefiting from a unified syntax 
to simplify the implementation of the core language.

%a new programming model
%where dependent types, decidable type checking, and general recursion
%coexist. Most of the time, programmers just want to write the function
%definitions, not much of delicate reasoning and proof.

\paragraph{Stratified type system with general recursion on term level}

One way to allow general recursion and dependent types in the same
language and still have decidable type checking is to use multiple
levels of syntax. In this way it is easy to have a term language with general
recursion, but have a more restricted type and/or kind language. On
the other hand this brings complexity to the language as multiple
levels (possibly with similar constructs) have to be
managed. $F^{\star}$~\cite{Swamy2011} is a recently proposed
dependently typed language that supports writing general-purpose
programs with effects while maintaining a consistent core language. In
its core, it has several sub-languages -- for terms, proofs and so on
(more than 20 language constructs). In $F^{\star}$, the use of
recursion is restricted in specifications and proofs, but arbitrary
recursion is allowed in programs.

\begin{comment}
Several early attempts of combining general recursion with dependent
types by using stratified type systems include Twelf~\cite{lf:twelf}
and Delphin~\cite{lf:delphin}, both of which are implementations of
the Edinburgh Logical Framework (LF)~\cite{harper:lf}. In a nutshell,
the LF calculus is a three-level calculus for object, families, and
kinds, and as such, Twelf and Delphin both have multiple syntactic
levels. In this way they are able to preserve decidable type checking
under the presence of general recursion. In other words, decidable
type checking comes at a price of complexity and duplication of
language constructs. In contrast, \name unifies terms and types into a
single category, and still achieves decidable type checking (although 
logical consistency is lost).
\end{comment}



%Another difference from \name is that types
%in $F^{\star}$ can only contain values but no non-value expressions,
%leading to its less expressiveness than \name.



% \bruno{Maybe have a paragraph on recursive types?}


% \bruno{The next two paragraphs are essentially copied from the reply, 
% and not integrated well into the related work. There is more to writing a paper 
% than just copying and pasting text and dumping it somewhere. 
% Please integrate this text better with the text that is already present here and 
% think about the text and whether it is making sense, in a nice logical way!
% If this is done you'll probably realised that there is some overlap already 
% with existing text, and the text can be made shorter.
% }

% \subsubsection{Unification of recursion and recursive types}

% We are not the first to unify both recursion and recursive types. In
% Cardelli's Type:Type language~\cite{typeintype}, he used general
% recursion to implement equi-recursive types. In contrast, our claimed
% contribution is a generalization of iso-recursive types that unifies
% recursion and iso-recursive types. The whole point of using
% iso-recursive types is to obtain decidable type checking, which
% Cardelli' work does not have.


% For
% example, a type-level identity function in Haskell is defined
% using closed type families:

% < type family Id (a :: *):: * where
% <    Id a = a
% <
% < f :: Id Int -> Int
% < f x = x

% By using explicit coercions in System $F_C$, the function |f| is encoded as
%  |\ x : Id Int . x tri co|. In a similar way, \name uses
% explicit casts to type function |\x : Id Int . castdown x|.

% In \name, we believe we have found a sweet spot, where
% there are fewer language constructs and quite a number of modern
% features found in Haskell.

% \subsubsection{Unification of Terms, Types, and Kinds}
% Pure Type Systems (PTS)~\cite{pts} show how a while family of type systems
% can be implemented using just a single syntactic form. PTS are an
% obvious source of inspiration for our work. Although this paper
% presents a specific system, it should be easy to generalize \name 
% in the same way as PTS and further show the applicability of our 
% ideas to other systems. 

% An early attempt of using a single syntax for an intermediate language
% for functional programming was Henk~\cite{pts:henk}. The Henk proposal
% was to use the \emph{lambda cube} as a typed intermediate language,
% unifying all three levels. The system used in Henk
% it is not even a dependently typed
% language, as the authors intended to  disallow types to depend
% on terms. As for recursion, even though it has a full lambda calculus
% at the type level, recursion is disallowed. Moreover no meta-theoretic 
% results were proved for Henk.

% \begin{comment}
% Since the implicit conversion of the lambda
% cube is not syntax-directed, they come up with a approach to
% strategically distribute the conversion rule over the other typing
% rules. In retrospect, Henk is quite conservative in terms of
% type-level computation. Actually it is not even a dependently typed
% language, as they clearly state that they don't allow types to depend
% on terms. As for recursion, even though it has a full lambda calculus
% at the type level, recursion is disallowed. In Henk the authors have
% not attempted to prove any meta-theoretic results.
% \end{comment}

% Another recent work on dependently typed language based on the same
% syntactic category is \textsf{Zombie}~\cite{zombie:popl14,
%   zombie:thesis}, where terms, types and the single kind $\star$ all
% reside in the same level. The language is based on a call-by-value
% variant of lambda calculus. An interesting aspect of Zombie is that
% it is composed of two fragments: a logical fragment and a programmatic
% fragment, so that it supports both partial and total programming. Even
% though Zombie has one syntactic category, it is still fairly
% complicated, as it tries to be both consistent as a logic and
% pragmatic as a programming language. In constrast \name takes 
% another point of the design space, giving up logical consistency 
% for simplicity.

% $\Pi\Sigma$~\cite{dep:pisigma} is another recently proposed
% dependently typed core language that resembles \name, as there is no
% syntactic difference between terms and types.\bruno{So? What's the
%   difference?}
% \bruno{Cayenne? general recursion, but no decidable type-checking.}

% \subsubsection{General Recursion and Managed Type-level Computation}
% One way to allow general recursion and dependent types in the same
% language and still have decidable type-checking is to use multiple
% levels of syntax. In this way it is easy to have a term language with 
% powerful constructs, such as general recursion, but have a more
% restricted type and/or kind language. On the other hand this brings 
% complexity to the language as multiple levels (possibly with similar
% constructs) have to be managed.

% \bruno{Very important reference: A Framework for Defining Logics}
% \bruno{integrate paragraph I wrote above better with subsequent text.}

% \begin{comment}
% As discussed in \S\ref{sec:rec}, bringing general
% recursion blindly into the dependently typed world causes more trouble
% than convenience. There are many dependently typed languages that
% allow general recursion. Zombie approaches general recursion by
% separating a consistent sub-language, in which all expressions are
% known to terminate, from a programmatic language that supports general
% recursion. What is interesting about Zombie is that those two
% seemingly conflicting worlds can interact with each other nicely,
% without compromising the consistency property. The key idea of this is
% to distinguish between these two fragments by using a
% \emph{consistency classifier $\theta$}. When $\theta$ is \textsf{L},
% it means the logical part, and \textsf{P} the program part. Like
% \name, Zombie uses \textsf{roll} and \textsf{unroll} for iso-recursive
% types. To ensure normalization (in order for decidable type checking),
% it forbids the use of \textsf{unroll} in \textsf{P}, where the
% potential non-termination could arise.\bruno{Zombie is being discussed
% in two different places.}
% \end{comment}

% $F^{\star}$~\cite{Swamy2011} also supports writing general-purpose
% programs with effects (e.g., state, exceptions, non-terminating, etc.)
% while maintaining a consistent core language. Unlike \name, it has
% several sub-languages -- for terms, proofs and so on. The interesting
% part of $F^{\star}$ lies in its kind system, which tracks the
% sub-languages and controls the interactions between them. The idea is
% to restrict the use of recursion in specifications and proofs while
% allowing arbitrary recursion in the program. They use $\star$ to
% denote program terms that may be effectful and divergent, and
% \textsf{P} for proofs that identify pure and total functions. In this
% way, they are able to ensure that fragments in a program used for
% building proof terms are never mixed with those that are potentially
% divergent. One difference from \name is that, types in $F^{\star}$ can
% only contain values but no non-value expressions, leading to its less
% expressiveness than \name.

% $\Pi\Sigma$ has a general mechanism for recursion. Like \name, it uses
% one recursion mechanism for the definition of both types and
% programs\bruno{Oh! So they have recursive types and recursion using 
% a single construct?}. The key idea relies on lifted types and boxes: definitions
% are not unfolded inside boxes. The way they achieve decidable type
% checking is to use boxing to stop the infinite unfolding of the
% recursive call, at the cost of additional annotations stating where to
% lift, box and force. One concern of $\Pi\Sigma$ is that its metatheory
% is not yet formally developed.\bruno{Maybe have a paragraph on
%   recursive types?}

\begin{comment}
\subsubsection{Type in Type}
We are not the the first to embrace $\star : \star$ in the system. It
has been long known that systems with $\star : \star$ is inconsistent
as a logic~\cite{handbook}. The core language of the Glasgow Haskell
Compiler, System $F_{C}$~\cite{fc} has already been inconsistent,
since all kinds are inhabited. $\Pi\Sigma$ has a impredicative
universe of types with $\mathsf{Type} : \mathsf{Type}$ due to the
support of general recursion. The surface language of Zombie also has
the rule
$\Gamma \vdash \mathsf{Type} : \mathsf{Type}$~\cite{zombie:popl15}.

The $\star : \star$ axiom makes it convenient to support kind
polymorphism, among other language features. One concern is that it
often causes type checking to be undecidable in dependently typed
language.  However, as we explained in Section~\ref{sec:ecore}, this
is not the case for \name. Type checking in \name is decidable -- all
type-level computation is driven by finite cast operations, thus no
potentially infinite reductions can happen in reality.
\end{comment}


\begin{comment}
\subsubsection{Encoding Datatypes}
There is much work on encoding datatypes into various high-level
languages. The classic Church encoding of datatypes into System F is
detailed in the work of Bohm and Beraducci~\cite{Bohm1985}.  An
alternative encoding of datatypes is Scott
encoding~\cite{encoding:scott}. However Scott encoding is not typable
in System F as it needs recursive types. \name has all it requires to
represent polymorphic and recursive datatypes.

Another line of related work are the \emph{inductively defined types} in
the Calculus of Inductive Constructions (CIC)~\cite{cic}, which is the
underlying formal language of Coq. In CIC, inductively defined types can
be represented by closed types in \coc, so are the primitive recursive
functionals over elements of the type. McBride et
al.~\cite{elim:pi:pattern} show that inductive families of datatypes
with dependent pattern matching can be translated into terms in Luo's
UTT~\cite{Luo:UTT}, extended with axiom K~\cite{axiomK}. 
This line of work may help in adding some form of inductive 
families (or GADTs) to a surface language on top of \name.  
\end{comment}


%The novelty
%in his work is the introduction of \emph{splitting tree}, with which
%explicit evidence for impossible case branches is recorded.
