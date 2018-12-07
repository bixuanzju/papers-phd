%include polycode.fmt
%include format.fmt

\section{Conclusions and Future Work}

This work proposes \name: a minimal dependently typed core language
that allows the same syntax for terms and types, supports type-level
computation, and preserves decidable type checking under the presence
of general recursion. The key idea is to control type-level
computation using explicit casts.  Because each cast can only account
for one-step of type-level computation, type checking becomes
decidable without requiring strong normalization of the calculus. At
the same time explicit casts together with recursion provide a
generalization of iso-recursive types.  By demonstrating a surface
language, supporting advanced language constructs, on top of \name we
have shown the potential of \name to serve as a core for Haskell-like
languages.

In future work, we hope to make  writing type-level computation easier by
adding language constructs to the surface language. Currently intensive type-level
computation can be written in \name. However it is inconvenient to use,
because in \name  type-level computation is driven by casts, and the number of
casts needs to be specified beforehand. Nevertheless, we do not
consider this a critical weakness of our system. The design of \name is
similar to System $F_C$ which sacrifices the convenience of type-level
computation and recovers the computation by surface-level language constructs, such as closed type
families in Haskell. We plan to add new surface language constructs in
the same spirit as type families in Haskell and automatically generate casts
through the translation. We also hope to investigate how to add inductive families 
and GADTs to the surface language. 
% Currently, for simple non-recursive functions, it is easy to deduce
% how many casts needs to be introduced, but for recursive ones, it
% becomes inconvenient.

\begin{comment}
Another important form of type-level computation supported by Haskell is
GADTs. As we mentioned in the related work, currently the surface language
lacks support for GADTs, although the core language has  necessary language
features for the encoding~\cite{gadtsml}. We have succeeded in encoding
some examples of GADTs in \name, such as finite sets (see $\mathit{Fin}$ in
the appendix). The current translation  rules for datatypes can be extended to
account for GADTs by generalizing the return type to be polymorphic  instead
of $\star$.

But we are still cautious about including GADTs  in the surface
language at the moment. The issues are manifested in two strands: 1)
Injectivity of type constructors; 2) Equality proofs. Currently \name only
supports syntactic equality which is not enough to pattern match some special
GADTs.  \linus{How special: non-injective, dependent? Examples?} We hope to
resolve the issues by generalizing explicit casts with non-syntactic equality. 
Though adding non-syntactic type equality to our system would require extra effort, it
remains as compelling future work.
\end{comment}
