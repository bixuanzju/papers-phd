%include lhs2TeX.fmt
%include polycode.fmt
%include forall.fmt
\newcommand{\typeSrc}{T}
\newcommand{\envSrc}{G}

\newsavebox{\simpleapply}
\newsavebox{\normalclosure}

\begin{lrbox}{\simpleapply}
\begin{minipage}{2.5in}
\begin{lstlisting}[mathescape]
$S_3$ :=  {
   Function $f$ = $J_1$;
   $f$.arg = $J_2$;
   $f$.apply();
   $\langle T_1 \rangle~x_f$ = ($\langle T_1 \rangle$) $f$.res;}
\end{lstlisting}
\end{minipage}
\end{lrbox}

\begin{lrbox}{\normalclosure}
\begin{minipage}{2.5in}
\begin{lstlisting}[mathescape]
$S_2$ :=  {
  class FC extends Function {
     void apply() {
        $\langle T_1 \rangle ~y$ = ($\langle T_1 \rangle$) this.arg;
         $S_1$;
         $res = J$;
     }
  };
  Function f = new FC();}
\end{lstlisting}
\end{minipage}
\end{lrbox}

\section{Compiling \Name}\label{sec:fcore}

This section formally presents \name and its compilation to
Java. \Name~is an extension of System F (the polymorphic
$\lambda$-calculus)~\cite{girard72dissertation,reynolds74towards} that
can serve as a target for compiler writers.

\subsubsection{Syntax.}

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

\subsubsection{From System F to Java.}

\figtwocol{f:translation}{Type-Directed Translation from System F to Java}{
\framebox{$\Gamma \turns  e : \tau \leadsto J \textbf{~in~} S$}

\begin{mathpar}
  \inferrule* [left=(FJ-Var)]
  {(x_1 : \type \mapsto x_2)  \in \Gamma}
  {\Gamma \turns x_1 : \type \leadsto x_2 \textbf{~in~} \{\}}

  \inferrule* [left=(FJ-TApp)]
  {\Gamma \turns e : \forall \alpha. \type_2  \leadsto J \textbf{~in~} S}
  {\Gamma \turns e \, \type_1 : \type_2[\type_1/\alpha] \leadsto J
            \textbf{~in~} S}
            
  \inferrule* [left=(FJ-TAbs)]
  {\Gamma, \alpha \turns e : \type \leadsto J \textbf{~in~} S}
  {\Gamma \turns \Lambda \alpha.e : \forall \alpha. \type \leadsto J \textbf{~in~} S}
 
  \inferrule* [left=(FJ-Abs)]
  {\Gamma , x : \type_1 \mapsto y \turns e : \type_2 \leadsto J \textbf{~in~} S_1 
  \\\\ f,~y~,~FC~fresh}
  {\Gamma \turns \lambda (x:\type_1).e : \type_1 \rightarrow \type_2 \leadsto f \textbf{~in~} S_2
  \\\\ \usebox{\normalclosure}
  } 
 
   \inferrule* [left=(FJ-App)]
  {
  \Gamma \turns e_1 : \type_2 \rightarrow \type_1
  \leadsto J_1 \textbf{~in~} S_1 ~~~~~~~\\
           \Gamma \turns e_2 : \type_2 \leadsto J_2 \textbf{~in~} S_2 ~~~~~~~
     f,~x_f~fresh  
  }
  {\Gamma \turns e_1 \, e_2 : \type_1 \leadsto x_f \textbf{~in~}
           S_1 \uplus S_2 \uplus S_3
  \\\\ \usebox{\simpleapply}
  }   
          
\end{mathpar}
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

\vspace{-15pt}

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

\hspace{-7pt}\bda{lll} & \Gamma ::=
\epsilon \mid \Gamma~(\relation{x_1}{\tau} \mapsto x_2) \mid \Gamma \alpha & \\ \eda

\noindent Translation environments have two purposes: 1) to keep track of the type 
and value bindings for type-checking purposes; 2) to establish the mapping 
between System F variables and Java variables in the generated code.

% \bda{lll} \textbf{Translation Environments} & \Delta ::=
% \epsilon \mid \Delta (\relation{x}{\tau}) \mid \Delta \alpha & \\ \eda

The translation judgment in the first set of rules adapts the typing
judgment of System F:

$\Gamma \turns  e : \tau \leadsto J \textbf{~in~} S$

\noindent It states that System F expression \emph{e} with type
$\tau$ results in Java expression \emph{J} created after executing a
block of statements \emph{S} with respect to translation environments
$\Gamma$. \texttt{FJ-Var} checks whether a given value-type binding
is present in an environment and generates a corresponding, previously initialized,
Java variable. \texttt{FJ-TApp} resolves the type of an abstraction and substitutes 
the applied type in it. \texttt{FJ-TAbs} translates the body of type abstractions --
note that, in the extended language, type abstractions would need to generate suspensions. 
\texttt{FJ-Abs} translates term abstractions. For translating term abstractions, we need evidence for resolving
the body \emph{e} and a bound variable \emph{x} of type $\tau_1$.
We then wrap the generated expression \emph{J} and its deriving statements
\emph{S} as follows. We create a class with a fresh name
\emph{FC}, extending the \emph{Function} class. 
In the body of \lstinline{apply}, we first create an alias for the function argument with a
fresh name $y$, then execute all statements $S_1$ deriving its
resulting Java expression \emph{J} that we assign as the output of
this function. 
Following that, we create a fresh alias \emph{f} for the
instance of the mentioned function, representing the class
\emph{FC}.
\texttt{FJ-App} is the most vital rule. Given the evidence that
$e_1$ is a function type, we generate a fresh
alias \emph{f} for its corresponding Java expression $J_1$. The $S_3$
block contains statements to derive the result of the
application. As described in Section~\ref{sec:overview}, we split applications into
two parts in IFOs. We first set the argument of \emph{f} to the Java
expression $J_2$, given the evidence resulting from $e_2$. Then,
we call \emph{f}'s \lstinline{apply} method and store the output in a fresh
variable $x_f$. Before executing statements in $S_3$, we need to
execute statements $S_1$ and $S_2$ deriving $J_1$ and $J_2$ respectively. 
To derive $x_f$, we need to execute all
dependent statements: $S_1 \uplus S_2 \uplus S_3$.

\subsubsection{Properties of the Translation.}
Two fundamental properties are worthwhile proving for
this translation: \emph{translation generates well-typed (cast-safe) Java programs}; and \emph{semantic preservation}.
Proving these two properties requires the static and dynamic semantics
(as well as the soundness proof) of the target language (an imperative subset of
Java with inner classes in our case). Unfortunately, as far as we know, the exact subset of
Java that we use has not been completely formalized yet. Three possibilities exist: 1) choosing an existing Java subset formalization and emulating its missing features in the translation, 2) developing our own formalized Java subset, 3) relating the translation to complete Java semantics within matching logic \cite{Bogdanas2015}. Each option would require complex changes beyond this paper's scope, hence it is a part of future work.
