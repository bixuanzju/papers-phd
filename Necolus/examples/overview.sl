--> "-2.0+3.0 = 1.0"

-- BEGIN_PRINT_INTERFACE
type IPrint = { print : String };
-- END_PRINT_INTERFACE

-- BEGIN_LANG_FAMILY
type Lang = { lit : Int -> IPrint, add : IPrint -> IPrint -> IPrint };
-- END_LANG_FAMILY


-- BEGIN_LANG_FAMILY2
type Lang = {lit : Int -> IPrint} & {add : IPrint -> IPrint -> IPrint};
-- END_LANG_FAMILY2

-- BEGIN_LANG_IMPL
implLang : Lang = {
  lit (value : Int) = { print = value.toString },
  add (left : IPrint) (right : IPrint) = {
    print = left.print ++ "+" ++ right.print
  }
};
-- END_LANG_IMPL


-- BEGIN_EVAL_INTERFACE
type IEval = { eval : Int };
-- END_EVAL_INTERFACE


-- BEGIN_EVAL_PRINT_INTERFACE
type LangEval = {
  lit : Int -> IPrint & IEval,
  add : IPrint & IEval -> IPrint & IEval -> IPrint & IEval
};
-- END_EVAL_PRINT_INTERFACE

-- BEGIN_EVAL_INTERFACE2
type EvalExt = { lit : Int -> IEval, add : IEval -> IEval -> IEval };
-- END_EVAL_INTERFACE2

-- BEGIN_EVAL_PRINT_IMPL
implEval = {
  lit (value : Int) = { eval = value },
  add (left : IEval) (right : IEval) = {
    eval = left.eval + right.eval
  }
};
implLangEval : LangEval = implLang ,, implEval;
-- END_EVAL_PRINT_IMPL

-- BEGIN_LANG_NEG
type NegPrint = { neg : IPrint -> IPrint };
type LangNeg = Lang & NegPrint;

implNegPrint : NegPrint = {
  neg (exp : IPrint) = { print = "-" ++ exp.print }
};
implLangNeg : LangNeg = implLang ,, implNegPrint;
-- END_LANG_NEG


-- BEGIN_LANG_FINAL
type NegEval = { neg : IEval -> IEval};
implNegEval : NegEval = {
  neg (exp : IEval) = { eval = 0 - exp.eval }
};

type NegEvalExt = { neg : IPrint & IEval -> IPrint & IEval };
type LangNegEval = LangEval & NegEvalExt;
implLangNegEval : LangNegEval = implLangEval ,, implNegPrint ,, implNegEval;
-- END_LANG_FINAL



-- BEGIN_LANG_EXT_INTER
type ExpAlg[E] = { lit : Int -> E, add : E -> E -> E };
type ExpAlgExt[E] = ExpAlg[E] & { sub : E -> E -> E };
-- END_LANG_EXT_INTER


-- BEGIN_LANG_EXT
e1 E (f : ExpAlg[E]) : E = f.add (f.lit 2) (f.lit 3);    -- 2 + 3
e2 E (f : ExpAlgExt[E]) : E = f.sub (f.lit 5) (e1 E f);  -- 5 - (2 + 3)
-- END_LANG_EXT


-- BEGIN_TEST
fac = implLangNegEval;
e = fac.add (fac.neg (fac.lit 2)) (fac.lit 3);
main = e.print ++ " = " ++ e.eval.toString -- Output: "-2+3 = 1"
-- END_TEST
