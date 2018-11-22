
-----------------------------------------
-- List
-----------------------------------------

type ListAlg[A, E] = {
  nilF : E,
  consF : A -> E -> E
};

type List[A] = { accept : forall E. ListAlg[A, E] -> E };

-- Constructors for int lists
nil : List[Int] = { accept E alg = alg.nilF };

cons (x : Int) (xs : List[Int]) : List[Int] = { accept E alg = alg.consF x (xs.accept E alg) };

-- Sum of lists
sumAlg = {
  nilF = 0,
  consF (x : Int) (xs : Int) = x + xs
};

sum (lst : List[Int]) : Int = lst.accept Int sumAlg;

-- Length of lists
lenAlg = {
  nilF = 0,
  consF (x : Int) (xs : Int) = 1 + xs
};

length (lst : List[Int]) : Int = lst.accept Int lenAlg;


max (x : Int) (y : Int) = if x > y then x else y;

-----------------------------------------
-- Object algebra interface of circuits
-----------------------------------------

-- BEGIN_SEDEL_DEF
type Circuit[C] = {
  identity : Int -> C, fan : Int -> C, beside : C -> C -> C,
  above : C -> C -> C, stretch : List[Int] -> C -> C
};
-- END_SEDEL_DEF


-- BEGIN_SEDEL_DEF2
type NCircuit[C] = Circuit[C] & { rstretch : List[Int] -> C -> C };
-- END_SEDEL_DEF2


----------------------------
-- Width of circuit
----------------------------


-- BEGIN_SEDEL_WIDTH
type Width = { width : Int };
language1 : Circuit[Width] = {
  identity (n : Int) = { width = n },
  fan      (n : Int) = { width = n },
  beside (c1 : Width) (c2 : Width) = { width = c1.width + c2.width },
  above  (c1 : Width) (c2 : Width) = { width = c1.width },
  stretch (ws : List[Int]) (c : Width) = { width = sum ws }
};
-- END_SEDEL_WIDTH


----------------------------
-- Depth of circuit
----------------------------

-- BEGIN_SEDEL_DEPTH
type Depth = { depth : Int };
language2 : Circuit[Depth] = {
  identity (n : Int) = { depth = 0 },
  fan      (n : Int) = { depth = 1 },
  beside (c1 : Depth) (c2 : Depth) = { depth = max c1.depth c2.depth },
  above  (c1 : Depth) (c2 : Depth) = { depth = c1.depth + c2.depth },
  stretch (ws : List[Int]) (c : Depth) = { depth = c.depth }
};
-- END_SEDEL_DEPTH


-- BEGIN_SEDEL_E1
l1 = language1;
e1 = l1.above (l1.beside (l1.fan 2) (l1.fan 2))
  (l1.above (l1.stretch (cons 2 (cons 2 nil)) (l1.fan 2))
    (l1.beside (l1.beside (l1.identity 1) (l1.fan 2)) (l1.identity 1)));
-- END_SEDEL_E1


-- BEGIN_SEDEL_FORALL
type DCircuit = { accept : forall C. Circuit[C] -> C };
-- END_SEDEL_FORALL



-- BEGIN_SEDEL_BRENT
brentKung : DCircuit = {
  accept C l = l.above (l.beside (l.fan 2) (l.fan 2))
    (l.above (l.stretch (cons 2 (cons 2 nil)) (l.fan 2))
      (l.beside (l.beside (l.identity 1) (l.fan 2)) (l.identity 1)))
};
l2 = language2;
e1 = brentKung.accept Width l1;
e2 = brentKung.accept Depth l2;
-- END_SEDEL_BRENT


-- BEGIN_SEDEL_E3
l3 : Circuit[Width & Depth] = l1 ,, l2;
e3 = brentKung.accept (Width & Depth) l3;
-- END_SEDEL_E3


----------------------------------------------------------------
-- Well-formed circuit: illustrating dependent interpretations
----------------------------------------------------------------

-- BEGIN_SEDEL_WS
type WellSized = { wS : Bool };
language3 = {
  identity (n : Int) = { wS = true },
  fan      (n : Int) = { wS = true },
  above (c1 : WellSized & Width) (c2 : WellSized & Width) =
    { wS = c1.wS && c2.wS && c1.width == c2.width },
  beside (c1 : WellSized) (c2 : WellSized) = { wS  = c1.wS && c2.wS  },
  stretch (ws : List[Int]) (c : WellSized & Width) =
    { wS = c.wS && length ws == c.width  }
};
-- END_SEDEL_WS


-- BEGIN_SEDEL_COMBINE
combine A [B * A] (x : A) (y : B) = x ,, y;
-- END_SEDEL_COMBINE


-- BEGIN_SEDEL_L3
l3 = combine Circuit[Width] Circuit[Depth] language1 language2;
-- END_SEDEL_L3


-- BEGIN_SEDEL_E4
l4   = language1 ,, language3;
e4   = brentKung.accept (WellSized & Width) l4;
main = e4.wS -- Output: true
-- END_SEDEL_E4
