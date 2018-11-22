{-# LANGUAGE ExplicitForAll  #-}
{-# LANGUAGE RankNTypes  #-}

-- BEGIN_DSL_DEF
class Circuit c where
  identity :: Int -> c
  fan      :: Int -> c
  beside   :: c -> c -> c
  above    :: c -> c -> c
  stretch  :: [Int] -> c -> c
-- END_DSL_DEF


-- BEGIN_DSL_WIDTH
data Width = W { width :: Int }
instance Circuit Width where
  identity n   = W n
  fan n        = W n
  beside c1 c2 =
    W (width c1 + width c2)
  above c1 c2  = c1
  stretch ws c = W (sum ws)
-- END_DSL_WIDTH


-- BEGIN_DSL_DEPTH
data Depth = D { depth :: Int }
instance Circuit Depth where
  identity n   = D 0
  fan n        = D 1
  beside c1 c2 =
    D (max (depth c1) (depth c2))
  above c1 c2  = D (depth c1 + depth c2)
  stretch ws c = c
-- END_DSL_DEPTH


-- BEGIN_DSL_E1
e1 :: Width
e1 = above (beside (fan 2) (fan 2))
       (above (stretch [2, 2] (fan 2))
         (beside (beside (identity 1) (fan 2)) (identity 1)))
-- END_DSL_E1


-- BEGIN_DSL_FORALL
type DCircuit = forall c. Circuit c => c
-- END_DSL_FORALL

-- BEGIN_DSL_BRENT
brentKung :: DCircuit
brentKung = above (beside (fan 2) (fan 2))
              (above (stretch [2, 2] (fan 2))
                (beside (beside (identity 1) (fan 2)) (identity 1)))
-- END_DSL_BRENT


-- BEGIN_DSL_TUPLE
instance (Circuit c1, Circuit c2) => Circuit (c1, c2) where
  identity n    = (identity n, identity n)
  fan n         = (fan n, fan n)
  beside c1 c2  = (beside (fst c1) (fst c2), beside (snd c1) (snd c2))
  above c1 c2   = (above (fst c1) (fst c2), above (snd c1) (snd c2))
  stretch ws c  = (stretch ws (fst c), stretch ws (snd c))
-- END_DSL_TUPLE

-- BEGIN_DSL_E12
e12 :: (Width, Depth)
e12 = brentKung
-- END_DSL_E12


-- BEGIN_DSL_WS
data WellSized = WS { wS :: Bool, ox :: Width }

instance Circuit WellSized where
 identity n   = WS True (identity n)
 fan n        = WS True (fan n)
 beside c1 c2 = WS (wS c1 && wS c2) (beside (ox c1) (ox c2))
 above c1 c2  = WS (wS c1 && wS c2 && width (ox c1) == width (ox c2))
                   (above (ox c1) (ox c2))
 stretch ws c = WS (wS c && length ws==width (ox c)) (stretch ws (ox c))
-- END_DSL_WS
