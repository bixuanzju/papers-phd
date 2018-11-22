-- BEGIN_DSL_FULL
{-
    Parallel Prefix Circuits DSL

    Finally Tagless Encoding

    Supporting zygo- and mutumorphisms

 -}


{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

{- Generic Definitions for Records -}

data Record :: [*] -> * where
  Nil  :: Record '[]
  Cons :: a -> Record as -> Record (a ': as)

class In a as where
  project :: Record as -> a

instance {-# OVERLAPPING #-} In a (a ': as) where
  project (Cons x _) = x

instance {-# OVERLAPPING #-} In a as => In a (b ': as) where
  project (Cons _ xs) = project xs

data All c :: [*] -> * where
  AllNil  :: All c '[]
  AllCons :: c a => All c as -> All c (a ': as)

{- Circuit DSL Infrastructure -}

class Circuit0 c where
  identity_ :: Int -> c
  fan_      :: Int -> c

class Circuit0 c => Circuit1 d c where
  beside_   :: Record d -> Record d -> c
  above_    :: Record d -> Record d -> c
  stretch_  :: [Int] -> Record d -> c

class Circuit2 d1 d2 where
  modality :: All (Circuit1 d1) d2

instance Circuit2 d1 '[] where
  modality = AllNil

instance (Circuit1 d1 a, Circuit2 d1 as) => Circuit2 d1 (a ': as) where
  modality = AllCons modality

type Circuit3 d = Circuit2 d d

identity :: forall d. Circuit3 d => Int -> Record d
identity = identity' (modality @d @d)
  where
    identity' :: All (Circuit1 d1) d2 -> Int -> Record d2
    identity' AllNil      n = Nil
    identity' (AllCons m) n = Cons (identity_ n) (identity' m n)

fan :: forall d. Circuit3 d => Int -> Record d
fan = fan' (modality @d @d)
  where
    fan' :: All (Circuit1 d1) d2 -> Int -> Record d2
    fan' AllNil      n = Nil
    fan' (AllCons m) n = Cons (fan_ n) (fan' m n)

beside :: forall d. Circuit3 d => Record d -> Record d -> Record d
beside = beside' (modality @ d @ d)
  where
    beside' :: All (Circuit1 d1) d2 -> Record d1 -> Record d1 -> Record d2
    beside' AllNil      c1 c2  =  Nil
    beside' (AllCons m) c1 c2  =  Cons (beside_ c1 c2) (beside' m c1 c2)

above :: forall d. Circuit3 d => Record d -> Record d -> Record d
above = above' (modality @ d @ d)
  where
    above' :: All (Circuit1 d1) d2 -> Record d1 -> Record d1 -> Record d2
    above' AllNil      c1 c2  =  Nil
    above' (AllCons m) c1 c2  =  Cons (above_ c1 c2) (above' m c1 c2)

stretch :: forall d. Circuit3 d => [Int] -> Record d -> Record d
stretch = stretch' (modality @ d @ d)
  where
    stretch' :: All (Circuit1 d1) d2 -> [Int] -> Record d1 -> Record d2
    stretch' AllNil      ws c  =  Nil
    stretch' (AllCons m) ws c  =  Cons (stretch_ ws$ c) (stretch' m ws c)

{- Shallow Embeddings -}

-- Width

newtype Width = Width { width :: Int }

instance Circuit0 Width where
  identity_ n    = Width n
  fan_ n         = Width n

instance In Width d => Circuit1 d Width where
  beside_ c1 c2  = Width (width (project c1) + width (project c2))
  above_ c1 c2   = project c1
  stretch_ ws c  = Width (sum ws)

-- Well-Sizedness

newtype WellSized = WellSized { wellSized :: Bool }

instance Circuit0 WellSized where
  identity_ n  =  WellSized True
  fan_ n       =  WellSized True

instance (In WellSized d, In Width d) => Circuit1 d WellSized where
  beside_ c1 c2 = WellSized (wellSized (project c1) && wellSized (project c2))
  above_ c1 c2 =
    WellSized
      (width (project c1) == width (project c2) &&
       wellSized (project c1) && wellSized (project c2))
  stretch_ ws c =
    WellSized (wellSized (project c) && length ws == width (project c))

{- Example -}

test :: Record '[Width, WellSized]
test = above (identity 5) (fan 5)

test' =
  case test of
    Cons x (Cons y Nil) -> (width x, wellSized y)
-- END_DSL_FULL
