%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
\newcommand{\typeSrc}{T}
\newcommand{\envSrc}{G}

\newsavebox{\normalapply}
\newsavebox{\normalclosure}

\begin{lrbox}{\normalapply}
\begin{minipage}{2in} % http://tex.stackexchange.com/questions/102416/error-when-compiling-a-minted-listings-inside-a-memoir-subfloat
\begin{lstlisting}[mathescape]
  $S_3$ :=  {
	  Function $f$;
	  $f$ = $J_1$;
	  $f$.arg = $J_2$;
	  $f$.apply();
	  $\langle \type_1 \rangle~x_f$;
	  $x_f$ = ($\langle \type_1 \rangle$) $f$.res;
  }
\end{lstlisting}
\end{minipage}
\end{lrbox}

\begin{lrbox}{\normalclosure}
\begin{minipage}{3in}
\hspace{50pt}\begin{lstlisting}[mathescape]
$C_2$ := {
	class FC extends Function {
	  Function $x_1$;
	  $\langle \bar{\type} \rangle~\bar{y}$;

	  public FC($\langle \bar{\type} \rangle~\bar{y}$) {
			super();
			this.$\bar{y}$ = $\bar{y}$;
			this.$x_1$ = this;
	  }

	  void apply() {
			$\langle \type_1 \rangle ~x_2$;
			$x_2$ = ($\langle \type_1 \rangle$) $x_1$.arg;
			$S_1$;
			$x_1$.res = $J$;
	  }
	}
}
$S_2$ :=  {
	Function $f$;
	$f$ = new $FC$($\bar{y}$);
}
\end{lstlisting}
\end{minipage}
\end{lrbox}

\section{Compiling \Name}\label{sec:fcore}

This section formally presents \name and its compilation to Middleweight Java (MJ) 
\cite{bierman03imperative}, a formalized subset of Java. \Name~is an extension of System F (the polymorphic
$\lambda$-calculus)~\cite{girard72dissertation,reynolds74towards} that
can serve as a target for compiler writers. MJ is
a minimal imperative core calculus for Java that can facilitate formal reasoning.

\subsection{Syntax}

In this section, for space reasons, we cover only the \name constructs
that correspond exactly to System F. Nevertheless, the constructs in
System F represent the most relevant parts of the compilation
process. As discussed in Section~\ref{sec:implementation}, our
implementation of \name includes other constructs that are
needed to create a practical programming language.

\paragraph{System F.}
The basic syntax of System F is:


\bda{l}
\ba{lll}
    \textbf{Types} & \type  ::=  \alpha \mid \type_1 \arrow \type_2
    \mid \forall \alpha. \type & \\
	\textbf{Expressions} & e  ::=  x \mid \lambda (x:\type) . e \mid e_1\;e_2 \mid \Lambda \alpha . e \mid e\;\type &
\ea
\eda

\noindent \emph{Types} $\type$ consist of type variables $\alpha$,
function types $\type_1 \arrow \type_2$, and type abstraction $\forall
\alpha. \type$. A lambda binder $\lambda (x:\type) . e$ abstracts
expressions $e$ over values (bound by a variable $x$ of type $\type$)
and is eliminated by function application $e_1\;e_2$. An expression
$\Lambda \alpha . e$ abstracts an expression $e$ over some type
variable $\alpha$ and is eliminated by a type application $e\;\type$.

\paragraph{Middleweight Java.} MJ is a valid subset of Java, 
i.e. every MJ program is an executable Java program. 
We do not show its full syntax and rules here due to their relative verbosity. 
They can be found in MJ's technical report \cite{bierman03imperative}.

\subsection{From System F to Middleweight Java (MJ)}

\renewcommand{\tabcolsep}{1pt}
 \figtwocol{f:translation}{Type-Directed Translation from System F to Middleweight Java}{
 \vspace{-5pt}
 \small
 \bda{l}

 \ba{lc}
 \multicolumn{2}{l}{\myruleform{\Gamma \turns  e : \tau \leadsto J \textbf{~in~} \Gamma_J;C;S}} \\

 (\texttt{FJ-Var}) &
 \hspace{-30pt}\myirule{
 (x_1 : \type \mapsto x_2)  \in \Gamma
 }{
 \Gamma \turns x_1 : \type \leadsto x_2 \textbf{~in~} \{x_2 : \langle\type\rangle\};\{\};\{\}
 } \\ \\

 (\texttt{FJ-TApp}) &
 \hspace{-30pt}\myirule{
 \Gamma \turns e : \forall \alpha. \type_2  \leadsto J
 \textbf{~in~} \Gamma_J;C;S
 }{
 \Gamma \turns e \, \type_1 : \type_2[\type_1/\alpha] \leadsto J
 \textbf{~in~} \Gamma_J;C;S
 } \\ \\

 (\texttt{FJ-TAbs}) &
 \myirule{
 \Gamma, \alpha \turns e : \type \leadsto J
 \textbf{~in~} \Gamma_J;C;S
 }{
 \Gamma \turns \Lambda \alpha.e : \forall \alpha. \type \leadsto J
 \textbf{~in~} \Gamma_J;C;S
 } \\ \\

 (\texttt{FJ-App}) &
 \hspace{-10pt}\myirule{
 \Gamma \turns e_1 : \type_2 \rightarrow \type_1
 \leadsto J_1 \textbf{~in~} \Gamma_{J1};C_1;S_1 ~~~~~~~\\
 \Gamma \turns e_2 : \type_2 \leadsto J_2 \textbf{~in~} \Gamma_{J2};C_2;S_2 ~~~~~~~
 f,~x_f~fresh
 }{
 \Gamma \turns e_1 \, e_2 : \type_1 \leadsto x_f \textbf{~in~} 
 \Gamma_{J1} \uplus \Gamma_{J2} \uplus \{f : Function, 
 x_f : \langle\type_1\rangle\}; C_1~C_2;\{S_1;S_2;S_3\}
 } \\

 \multicolumn{2}{c}{\hspace{65pt}\usebox{\normalapply}}

 \\ \\

 (\texttt{FJ-Abs}) &
 \hspace{-10pt}\myirule{
 \Gamma , x : \type_1 \mapsto x_2 \turns e : \type_2 \leadsto J 
\textbf{~in~} \Gamma_J,x_2 : \langle\type_1\rangle;C_1;S_1 \\ f,~x_1~,~x_2~,~FC~fresh ~~~~~~
\Gamma \turns \bar{x} :\bar{\type} \leadsto \bar{y} \textbf{~in~} \{\bar{y} : \langle\bar{\type}\rangle\}; \{\};\{\}
 }{
 \Gamma \turns \lambda (x:\type_1).e : \type_1 \rightarrow \type_2 \leadsto f 
 \textbf{~in~} \Gamma_J \uplus \{x_2 : \langle\type_1\rangle, f : Function, 
 x_1 : Function\}; C_1~C_2; S_2
 } \\

 \multicolumn{2}{c}{\hspace{65pt}\usebox{\normalclosure}}

 \\ \\


 \ea

 \eda

%format Object = "\text{\lstinline{Object}}"
%format Function = "\text{\lstinline{Function}}"
%format translate t = "\langle" t "\rangle"
%format binder = "\forall \alpha. \tau"
%format alpha = "\alpha"
%format tau = "\tau"
%format fun = "\tau_2 \rightarrow \tau_1"


\text{Translation of System F types to Java types:}
\vspace{-5pt}

< translate alpha   = Object
< translate binder  = translate tau
< translate fun     = Function

\vspace{-10pt}

 }


Figure \ref{f:translation} shows the type-directed translation rules
that generate Java code from given System F expressions. We exploit
the fact that System F has an erasure semantics in the
translation. This means that type abstractions and type applications
do not generate any code or have any overhead at run-time.

We use two sets of rules in our translation. The first one
is translating System F expressions. The second set of rules,
 the function $\langle \tau\rangle$, describes 
 how we translate System F types into Java types.

In order to do the translation, we need \emph{translation environments}:

\hspace{-10pt}\bda{lll} & \Gamma ::=
\epsilon \mid \Gamma~(\relation{x_1}{\tau} \mapsto x_2) \mid \Gamma \alpha & \\ \eda

\noindent Translation environments have two purposes: 1) to keep track of the type
and value bindings for type-checking purposes; 2) to establish the mapping
between System F variables and Java variables in the generated code.

The translation judgment in the first set of rules adapts the typing
judgment of System F:

$\Gamma \turns  e : \tau \leadsto J \textbf{~in~} \Gamma_J;C;S$

\noindent It states that System F expression \emph{e} with type
$\tau$ (with respect to translation environments
$\Gamma$) results in MJ expression \emph{J} created after executing an
\emph{MJ program} in an MJ typing environment $\Gamma_J$. In the shown rules,
MJ expressions \emph{J} are always Java variables (to prevent overwriting, as discussed
in Section \ref{sec:overview}). As defined in the technical report \cite{bierman03imperative}, 
an \emph{MJ program} consists of a collection of class definitions (here denoted by \emph{C})
and a sequence of statements (here denoted by \emph{S}). We write $C_1~C_2$ to denote a 
collection that is composed of class definitions from $C_1$ and class definitions from $C_2$.
Similarly, a sequence $\{S_1;S_2\}$ executes first all statements in $S_1$ and then statements in $S_2$.
As the translation nests and decomposes these MJ programs, the sequence of statements
of the outermost one corresponds to the body of the \lstinline{main} method in a Java program.
An MJ typing environment, $\Gamma_J$, is a map from program variables to expression types 
\cite{bierman03imperative} (denoted as $x : cd$). We denote joined MJ typing environments
by $\uplus$, and an extended typing environment by a comma ($\Gamma_J, x : cd$).
Typing environments keep track of the generated temporary Java variables. 

As shown in Figure \ref{f:translation}, \texttt{FJ-Var} checks whether a given value-type binding
is present in an environment and generates a corresponding, previously initialized,
Java variable. \texttt{FJ-TApp} and \texttt{FJ-TAbs} do not generate any extra code.
\texttt{FJ-App} translates value applications. Given the evidence that
$e_1$ is a function type, we generate a fresh
alias \emph{f} for its corresponding Java expression $J_1$. The $S_3$
block contains statements to derive the result of the
application. As described in Section~\ref{sec:overview}, we split applications into
two parts in IFOs. We first set the argument of \emph{f} to the Java
expression $J_2$, given the evidence resulting from $e_2$. Then,
we call \emph{f}'s \lstinline{apply} method and store the output in a fresh
variable $x_f$. Before executing statements in $S_3$, we need to
execute statements $S_1$ and $S_2$ deriving $J_1$ and $J_2$ respectively.
To derive $x_f$, we need to join the typing environments $\Gamma_{J1}$ and $\Gamma_{J2}$
and the class collections $C_1$ and $C_2$, and execute all
dependent statement sequences in order: $S_1;S_2;S_3$.
\texttt{FJ-Abs} translates term abstractions. Note that we abuse overline notation here.
In the typing judgment, $\Gamma \turns \bar{x} : \bar{\type} \leadsto \bar{y} \textbf{~in~} \{\bar{y} : \langle\bar{\type}\rangle\}; \{\};\{\}$
denotes zero of more typing judgements ( $\Gamma \turns x_1 : \type_1 \leadsto y_1 
\dots \Gamma \turns x_n : \type_n \leadsto y_n \textbf{~in~} \{y_n : \langle\type_n\rangle\}; \{\};\{\}$).
In the generated code, the meaning of $\bar{y}$ and $\langle \bar{\type} \rangle$ depends on their context:
zero or more \emph{fields} named $y_1\dots y_n$ and declared with the corresponding translated types
$\langle \type_1 \rangle\dots\langle \type_n \rangle$,
or \emph{class constructor parameters}, or \emph{field assignment statements}, or \emph{class
instantiation arguments}. For translating term abstractions, we need evidence for resolving
\emph{e}, scoped variables $\bar{x}$ of types $\bar{\type}$, and a bound variable \emph{x} of type $\tau_1$.
We then wrap the generated MJ expression \emph{J} and its deriving statements
\emph{S} as follows. We create a class with a fresh name
\emph{FC}, extending the \emph{Function} class. This class contains
fields referring to all translated variables that are in scope ($\bar{y}$)
as well as a self-reference field with a fresh name $x_1$. These fields are initialized
in the constructor. In the body of \lstinline{apply}, we first create an alias for the function argument with a
fresh name $x_2$, then execute all statements $S_1$ deriving its
resulting Java expression \emph{J} that we assign as the output of
this function. 
In the sequence of statements, we create a fresh alias \emph{f} for the
instance of the mentioned function, representing the class
\emph{FC}, initialized with the translated variables in scope $\bar{y}$.
Passing all scoped variables is sub-optimal and the implementation avoids this by using
inner classes. For the sake of simplicity, we chose to use this sub-optimal version
in the formal presentation.


\subsection{Properties of the Translation}
In this section, we describe two important properties of our translation:
\emph{type preservation}; and 
\emph{semantic preservation}. For space reasons, we only show a proof sketch
of the first property.
\paragraph{Type Preservation.}
This property states that \emph{translation generates well-typed MJ programs}. Note that
all casts introduced by the translation succeed and that the type preservation is partial,
because of the property (trivial from translation): 
$if~\tau_1=\tau_2,~then~ \langle\tau_1\rangle=\langle\tau_2\rangle$ which is not true
in the opposite direction.
 
We state the partial type preservation theorem for open terms below. Every well-formed
MJ program \emph{p} induces a class table $\Delta_p$ \cite{bierman03imperative} which provides
typing information about the methods, constructors, and fields in the given program.
As we nest and decompose MJ programs in the translation, we need to express it in the
corresponding class tables. We write $\Delta_1 \uplus \Delta_2$ (assuming $\Delta_1$ and
$\Delta_2$ are disjoint) to denote a class table that provides typing information of both
$\Delta_1$ and $\Delta_2$. $\Delta \supseteq \Delta_1 \uplus \Delta_2$ denotes
that the class table $\Delta$ subsumes $\Delta_1$ and $\Delta_2$, i.e. it provides typing
information of at least what $\Delta_1$ and $\Delta_2$ provide. We express a similar notion
in typing environments, i.e. $\Gamma_J \supseteq \Gamma_{J1} \uplus \Gamma_{J2}$.
We adapt the typing judgment for MJ \cite{bierman03imperative}:

$\Delta;\Gamma_J \turns J : T$

Where $\Delta$ is a class table, $\Gamma_J$ is a typing environment, $J$ is an MJ expression,
and T is an MJ type. In the theorem below, we assume $\Delta_0$ to be a class table induced 
by the MJ program $C_0;S_0$, and $\Delta_G$ to be a valid global class table (which can be checked by MJ rules) 
that contains the \texttt{Function} class. Note we additionally abuse
overline notation in $\Delta;\Gamma_J \turns \bar{J} : \langle\bar{\tau}\rangle$ to denote
zero or more MJ typing judgments ($\Delta;\Gamma_J \turns J_1 : \langle\tau_1\rangle\dots\Delta;\Gamma_J \turns J_n : \langle\tau_n\rangle$)
and in $\Gamma = \Gamma_0 \uplus (\bar{x}:\bar{\tau}\mapsto \bar{J})$ 
to denote splitting of translation environments into $\Gamma_0$ (nothing or type variables)
 and environment mapping of all System F term variables to Java variables.  
 
\begin{theorem}
Suppose $\Gamma \turns e : \tau_0 \leadsto J_0~\textbf{~in~}~\Gamma_{J0};C_0;S_0$ with 
$\Gamma = \Gamma_0 \uplus (\bar{x}:\bar{\tau}\mapsto \bar{J})$ and 
$\Gamma \turns \bar{x}:\bar{\tau} \leadsto \bar{J} \textbf{~in~}~\{\bar{J}:\langle\bar{\tau}\rangle\};\{\};\{\}$.
For any valid class table $\Delta \supseteq \Delta_0 \uplus \Delta_G$ and typing environment
$\Gamma_J \supseteq \Gamma_{J0}$ such that 
$\Delta;\Gamma_J \turns \bar{J} : \langle\bar{\tau}\rangle$,
it is the case that $\Delta;\Gamma_J \turns J_0 : \langle\tau_0\rangle$.
\end{theorem}

\begin{proof}
The proof proceeds by the induction on the translation rules:

\begin{case}{\texttt{FJ-Var}}
 follows immediately from the assumptions about $\Delta$ and $\Gamma_J$.
\end{case}

\begin{mcase}{\texttt{FJ-TAbs} and \texttt{FJ-TApp}}
 do not generate any code. The results follow from applying the induction hypothesis
and the translation of types with type erasure.
\end{mcase}

\begin{case}{\texttt{FJ-App}}: 
Let $\Delta_1$ and $\Delta_2$ be class tables induced by the MJ programs $C_1;S_1$
and $C_2;S_2$ respectively. We assume
  $\Delta \supseteq \Delta_1 \uplus \Delta_2 \uplus \Delta_G$
and $\Gamma_J \supseteq \Gamma_{J1} \uplus \Gamma_{J2}$.
We apply the induction hypothesis to $\Gamma \turns e_1 : \type_2 \rightarrow \type_1
  \leadsto J_1 \textbf{~in~} \Gamma_{J1};C_1;S_1$, so we know 
  $\Delta_1 \uplus \Delta_G$ is a valid class table and $\Delta; \Gamma_J \turns J_1 : \langle\type_2 \rightarrow \type_1\rangle$.

We apply the induction hypothesis to $\Gamma \turns e_2 : \type_2 \leadsto J_2 \textbf{~in~} \Gamma_{J2};C_2;S_2$,
so we know $\Delta_2 \uplus \Delta_G$ is a valid class table
and $\Delta; \Gamma_J \turns J_2 : \langle\type_2\rangle$.

Assuming $\Delta_1$, $\Delta_2$, and $\Delta_G$ are distinct,  
$\Delta_1 \uplus \Delta_2 \uplus \Delta_G$ is also a valid class table.

For $\Gamma \turns e_1 \, e_2 : \type_1 \leadsto x_f \textbf{~in~} 
\Gamma_{J1} \uplus \Gamma_{J2};C_1~C_2;\{S_1;S_2;S_3\}$, we
show that $C_1~C_2;\{S_1;S_2;S_3\}$ is a valid MJ program by \texttt{T-ProgDef}.
The class collections $C_1~C_2$ contain valid class definitions by \texttt{T-CDefn}.
We can check the sequences of statements $S_1;S_2;S_3$ and $S_3$ by \texttt{TS-Seq}.
Then:

$\Delta; \Gamma_J \turns Function~f; : Function$ by \texttt{TS-Intro}

$\Delta; \Gamma_J \turns f = J_1; : void$ by \texttt{TS-Write}

$\Delta; \Gamma_J \turns f.arg = J_2; : void$ by \texttt{TS-FieldWrite}

$\Delta; \Gamma_J \turns f.apply(); : void$ by \texttt{TE-Method}

$\Delta; \Gamma_J \turns \langle\type_1\rangle~x_f; : \langle\type_1\rangle$ by \texttt{TS-Intro}

$\Delta; \Gamma_J \turns (\langle\type_1\rangle)~f.res; : \langle\type_1\rangle$ by \texttt{TE-DownCast}

$\Delta; \Gamma_J \turns x_f = (\langle\type_1\rangle)~f.res; : void$ by \texttt{TS-Write}

Hence, we have a valid MJ program, which implies
 $\Delta; \Gamma_J \turns x_f : \langle\type_1\rangle$ by \texttt{TE-Var}.

\end{case}

\begin{case}{\texttt{FJ-Abs}} 
Let $\Delta_1$ be a class table induced by the MJ program $C_1;S_1$.
We assume $\Delta_3 \supseteq \Delta_1 \uplus \Delta_G$
and $\Gamma_{J3} \supseteq \Gamma_{J}, x_2 : \langle\type_1 \rangle$.

We apply the induction hypothesis to 
$\Gamma , x : \type_1 \mapsto x_2 \turns e : \type_2 \leadsto J \textbf{~in~} \Gamma_{J};C;S$

and we have $\Delta_3; \Gamma_{J3} \turns J : \langle\type_2 \rangle$.

We apply the induction hypothesis to 
$\Gamma \turns \bar{x} : \bar{\type} \leadsto \bar{y} \textbf{~in~} \Gamma_J;$ $\{\};\{\}$

and we have $\Delta_3; \Gamma_{J3} \turns \bar{y} : \langle\bar{\type}\rangle$.

Let $\Delta_2$ be a class table induced by the MJ program $C_1~C_2;S_2$.
We assume $\Delta_4 \supseteq \Delta_2 \uplus \Delta_G$
and $\Gamma_{J4} \supseteq \Gamma_{J} \uplus \{x_2 : \langle\type_1\rangle, f : Function, 
 x_1 : Function$\}.

For  $\Gamma \turns \lambda (x:\type_1).e : \type_1 \rightarrow \type_2 \leadsto f 
 \textbf{~in~} \Gamma_J,x_2 : \langle\type_1\rangle, f : Function, 
 x_1 : Function;C_1~C_2;S_2$,
 we check that $C_1~C_2;S_2$ is a valid MJ program by \texttt{T-ProgDef}.
The class collection $C_1$ contains valid class definitions by \texttt{T-CDefn}.
 The class collection $C_2$ has a valid class definition by \texttt{T-CDefn}, \texttt{T-FieldsOk}, 
\texttt{T-ConsOK}, \texttt{T-Mbodys}, \texttt{T-MethOk1}, and we check its constructor 
 statements by \texttt{TS-Seq}:
 
 $\Delta_4; \Gamma_{J4} \turns super(); : void$ by \texttt{T-CSuper}.

 $\Delta_4; \Gamma_{J4} \turns this.\bar{y} = \bar{y}; : void$ 
 and $\Delta_4; \Gamma_{J4} \turns this.x_1 = this; : void$  by \texttt{TS-FieldWrite}
 
 We check its apply method body by \texttt{T-MDefn} and \texttt{TS-Seq}:
 
$\Delta_4; \Gamma_{J4} \turns \langle\type_1\rangle~x_2; : \langle\type_1\rangle$ by \texttt{TS-Intro}

$\Delta_4; \Gamma_{J4} \turns x_1 : Function$ by \texttt{TE-FieldAccess}

$\Delta_4; \Gamma_{J4} \turns (\langle\type_1\rangle)~x_1.arg; : \langle\type_1\rangle$ by \texttt{TE-DownCast} 

$\Delta_4; \Gamma_{J4} \turns x_2 = (\langle\type_1\rangle)~x_1.arg; : void$ by \texttt{TS-Write} 

$\Delta_4; \Gamma_{J4} \turns S_1; : void$ by \texttt{TS-Seq} 

$\Delta_4; \Gamma_{J4} \turns x_1.res = J; : void$ by \texttt{TS-FieldWrite}

Then, we check the sequence of statements $S_2$ by \texttt{TS-Seq}:

$\Delta_4; \Gamma_{J4} \turns Function~f; : Function$ by \texttt{TS-Intro}

$\Delta_4; \Gamma_{J4} \turns new~FC(\bar{y}) : Function$ by \texttt{TE-New}

$\Delta_4; \Gamma_{J4} \turns f = new~FC(\bar{y}); : void$ by \texttt{TS-Write}

Thus, $C_1~C_2;S_2$ is a valid MJ program, which implies $\Delta_4; \Gamma_{J4} \turns f : Function$
by \texttt{TE-Var}.
\end{case}

\end{proof}

The partial type preservation also holds for closed terms:

\begin{corollary}
Suppose $\turns e : \tau \leadsto J~\textbf{~in~}~\Gamma_{J};C;S$.
For a valid class table $\Delta \uplus \Delta_G$ and typing environment
$\Gamma_J$,
it is the case that $\Delta \uplus \Delta_G;\Gamma_J \turns J : \langle\tau\rangle$.
\end{corollary}

Note that even though we have empty translation environments here, we may not have
empty MJ typing environments $\Gamma_J$ due to the generation of temporary variables.

\paragraph{Semantic Preservation.} This property states that for any valid System F 
expression, the result of evaluating that expression under its standard call-by-value semantics
is the same as the result of executing the corresponding compiled code. The proof of this
property is more involved due to the lack of commutativity between the translation
and System F evaluation. It is left for future work.

%%This is something we plan to do as
%%future work, but since it is

%%We can prove the soundness of this translation by
%%the type preservation and progress proofs. This would involve
%%stating the translation with the respect to a sound formalized subset of the Java
%%language that includes mutuable fields and inner classes, such as IGJ \cite{Zibin2007}.
%%\tomas{ref to future work?}
