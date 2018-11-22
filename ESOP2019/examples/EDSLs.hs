type I1 = Int

litI1 :: Int -> I1
litI1 = id

addI1 :: I1 -> I1 -> I1
addI1 = (+)

type I2 = String

litI2 :: Int -> I2
litI2 = show

addI2 :: I2 -> I2 -> I2
addI2 s1 s2 = s1 ++ " + " ++ s2

type I3 = (Int,String)

litI3 :: Int -> I3
litI3 x = (litI1 x, litI2 x)

addI3 :: I3 -> I3 -> I3
addI3 e1 e2 = (addI1 (fst e1) (fst e2), addI2 (snd e1) (snd e2))

t = addI3 (litI3 2) (litI3 5)

-- dependencies

-- Modelling an interpretation with a dependency:
-- depends on the interface, but not the implementation

litI4 :: Int -> I2
litI4 = show

addI4 :: I3 -> I3 -> I2
addI4 e1 e2 = snd e1 ++ " + " ++ snd e2 ++ " = " ++ show (fst e1)  -- wrong result, but valid dependency

-- Combined interpretation must merge the 2 implementations

litI5 :: Int -> I3
litI5 x = (litI1 x, litI4 x)

addI5 :: I3 -> I3 -> I3
addI5 e1 e2 = (addI1 (fst e1) (fst e2), addI4 e1 e2)

t2 = addI5 (litI5 2) (litI5 5)

-- Two problems here:

-- 1) "construction" code is not reusable (solved with finally tagless/object algebras)

-- 2) boilerplate needed for composition. This problem is not too serious
-- if the implementations are independent of each other, because the implementations
-- (with the help of overloaded constructors) can be run independently.
-- However it is a more serious problem with dependent interpretations,
-- since boilerplate cannot be avoided. 

