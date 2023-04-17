inductive Digit : Type
  | zero
  | one
  | two
  | three
  | four
  | five
  | six
  | seven
  | eight
  | nine
  | alpha
  | beta
  | gamma

namespace Digit

def toNat : Digit → Nat
  | zero => 0
  | one => 1
  | two => 2
  | three => 3
  | four => 4
  | five => 5
  | six => 6
  | seven => 7
  | eight => 8
  | nine => 9
  | alpha => 10
  | beta => 11
  | gamma => 12
instance : Coe (Digit) Nat where coe := toNat

def toString : Digit → String
  | zero => "0"
  | one => "1"
  | two => "2"
  | three => "3"
  | four => "4"
  | five => "5"
  | six => "6"
  | seven => "7"
  | eight => "8"
  | nine => "9"
  | alpha => "α"
  | beta => "β"
  | gamma => "γ"
instance : ToString Digit where toString := Digit.toString

#eval one
#eval beta

def ofNat (n : Nat) (_ : n ≤ 12): Digit :=
  match n with
  | 0 => zero
  | 1 => one
  | 2 => two
  | 3 => three
  | 4 => four
  | 5 => five
  | 6 => six
  | 7 => seven
  | 8 => eight
  | 9 => nine
  | 10 => alpha
  | 11 => beta
  | 12 => gamma

end Digit

abbrev Number := List Digit

def Digit.toNumber : Digit → Number := λ d => [d]
instance : Coe Digit Number where coe := Digit.toNumber

namespace Number

open Digit

def toString : Number → String
  | [] => ""
  | d :: ds => d.toString ++ (Number.toString ds)
instance : ToString Number where toString := Number.toString

def toNat (n : Number) : Nat :=
  n.foldl (λ acc d => acc * 13 + d.toNat) 0
instance : Coe Number Nat where coe := toNat

#eval ([one, two, alpha])

def ofNat : Nat → Number
  | 0 => []
  | n => (Number.ofNat (n / 13)) ++ (Digit.ofNat (n % 13) sorry: Number)
decreasing_by sorry

#eval ofNat 13

def plus : Number → Number → Number
  | n1, n2 => ofNat (n1.toNat + n2.toNat)

end Number

inductive Expr : Type
  | num (n : Number)
  | succ (e : Expr)
  | plus (e1 e2 : Expr)
  | minus (e1 e2 : Expr)
  | times (e1 e2 : Expr)
  | divide (e1 e2 : Expr)

def Number.toExpr : Number → Expr := λ n => Expr.num n
instance : Coe Number Expr where coe := Number.toExpr

namespace Expr

open Digit

def eval : Expr → Nat
  | num n => Number.toNat n
  | succ e => (eval e) + 1
  | plus e1 e2 => (eval e1) + (eval e2)
  | minus e1 e2 => (eval e1) - (eval e2)
  | times e1 e2 => (eval e1) * (eval e2)
  | divide e1 e2 => (eval e1) / (eval e2)

#eval eval (succ (num [Digit.alpha]))

def toString : Expr → String
  | num n => Number.toString n
  | succ e => s!"s{toString e}"
  | plus e1 e2 => s!"({toString e1} + {toString e2})"
  | minus e1 e2 => s!"({toString e1} - {toString e2})"
  | times e1 e2 => s!"({toString e1} * {toString e2})"
  | divide e1 e2 => s!"({toString e1} / {toString e2})"
instance : ToString Expr where toString := toString

def Formula1 := plus alpha (plus two one)

#eval Formula1
#eval Formula1.eval

end Expr
