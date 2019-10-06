module Equality

%default total

data JMEq : (x : a) -> (y : b) -> Type where
  JMrefl : {x : a} -> JMEq x x

data LEq : (x : a) -> (y : a) -> Type where
  Lrefl : {x : a} -> LEq x x

jmImpliesLeibniz : {a : Type} -> {x, y : a} -> (prf : JMEq x y) -> LEq x y
jmImpliesLeibniz JMrefl = Lrefl

jmImpliesTypesEquality : {x : a} -> {y : b} -> (prf : JMEq x y) -> LEq a b
jmImpliesTypesEquality JMrefl = Lrefl

{-
We obviously can derive Streicher's K given the above on John Major equality,
but it's worth checking explicitly how hard is it to prove this.
-}
doIHaveK : {x : a} -> (prf : LEq x x) -> LEq prf Lrefl
doIHaveK Lrefl = Lrefl
