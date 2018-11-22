
type GExpAlg[In, Out] = {
  lit : Int -> Out,
  add : In -> In -> Out
};

type ExpAlg[E] = GExpAlg[E, E];

type Exp = { accept : forall E . ExpAlg[E] -> E };

type OExpAlg[S, E] = GExpAlg[S, S -> E];


----------------------------------------------------------------
-- fself : family self-reference
-- oself : object self-reference
----------------------------------------------------------------

type IEval = { eval : Int };

trait evalAlg => {
  lit (x : Int) (oself : IEval) = { eval = x };
  add (x : IEval) (y : IEval) (oself : IEval)  = { eval = x.eval + y.eval }
} : OExpAlg[IEval, IEval];


----------------------------------------------------------------
-- A printing operation using family and object self-references
----------------------------------------------------------------

type IPrint = { print : String };

trait printAlg [fself : OExpAlg[IEval & IPrint, IEval & IPrint] ] => {
  lit (x : Int) (osefl : IEval & IPrint) = { print = x.toString };
  add (e1 : IPrint) (e2 : IPrint) (oself : IEval & IPrint) = {
    print = let plus54 = fself.add (fself.lit 5 oself) (fself.lit 4 oself) oself
            in e1.print ++ " + " ++ e2.print ++ " = " ++ oself.eval.toString ++
                " and 5.0 + 4.0 = " ++ plus54.eval.toString
  }
} : OExpAlg[IEval & IPrint, IPrint];


-- Merge two algebras
alg = new[OExpAlg[IEval & IPrint , IEval & IPrint]] evalAlg & printAlg;


fix A (f : A -> A) = letrec s : A = f s in s;

-- This is the only boilerplate, could be eliminated?
closeAlg E (alg : OExpAlg[E,E]) = {
  lit = \(x : Int) -> fix E (alg.lit x),
  add = \(e1 : E) -> \ (e2 : E) -> fix E (alg.add e1 e2)
};


-- Guess the result?
exp : Exp = { accept E f = f.add (f.lit 4) (f.lit 7) };
o = exp.accept IEval & IPrint (closeAlg IEval & IPrint alg)
main = o.print
