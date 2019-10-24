module Codata

%default total

zeroes : Stream Int
zeroes = 0 :: zeroes

ones1 : Stream Int
ones1 = 1 :: ones1

ones2 : Stream Int
ones2 = map (+ 1) zeroes

onesEq : Codata.ones1 = Codata.ones2
onesEq = ?onesEq_rhs
