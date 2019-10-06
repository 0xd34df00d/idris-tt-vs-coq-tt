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
