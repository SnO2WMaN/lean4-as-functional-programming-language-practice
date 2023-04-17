import «Toyprog»

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := {x := 0.0, y := 0.0}
#eval origin

def distance (p₁ p₂ : Point) : Float := Float.sqrt (((p₁.x - p₂.x) ^ 2) + ((p₁.y - p₂.y) ^ 2))
#eval distance (Point.mk 1.0 2.0) (Point.mk 5.0 (-1.0))

def add1 (n : Nat) : Nat := n + 1 

#eval add1 2

def max₂ (n : Nat) (k : Nat) : Nat := if n < k then k else n

#eval max₂ 2 48 

#eval (·,·) 1 2

def third (xs : List α) (ok : xs.length >= 3) := xs[2]
def third? (xs : List α) := xs[2]?

#check third

#eval third [2,4,5] (by simp)
#eval third? [2,4,5]
 
class Plus (α : Type) where
  plus : α → α → α

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
deriving Repr

def six : Pos := Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one))))
def seven : Pos := Pos.succ six
#eval six
#eval seven

def Pos.plus : Pos → Pos → Pos
  | Pos.one, p => Pos.succ p
  | Pos.succ p, q => Pos.succ (plus p q) 
instance : Add Pos where add := Pos.plus

def Pos.mul : Pos → Pos → Pos
  | Pos.one, p => p
  | Pos.succ p, q => q + (mul p q)
instance : Mul Pos where mul := Pos.mul

def Pos.toString : Pos → String
  | Pos.one => "1"
  | Pos.succ p => p.toString ++ "+1"
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ p => p.toNat + 1
instance : ToString Pos where toString x := toString x.toNat

def thirteen : Pos := six + seven
def fourtynine : Pos := seven * seven
#eval thirteen
#eval Pos.toString seven
#eval s!"{seven}"
#eval s!"{thirteen}"
#eval s!"{fourtynine}"

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec loop : Nat → Pos
      | 0 => Pos.one
      | p + 1 => Pos.succ (loop p)
    loop n
def four : Pos := 4
#eval four

#check @IO.println

inductive Var : Type where
  | mk : Nat → Var

def Var.toString : Var → String
  | Var.mk n => s!"v{n}"
instance : ToString Var where toString := Var.toString

inductive Expr : Type where
  | var : Var → Expr
  | lam : Var → Expr → Expr
  | app : Expr → Expr → Expr
instance : ToString Expr where
  toString :=
    let rec loop : Expr → String
      | Expr.var v => toString v
      | Expr.lam v e => s!"λ{v}. {loop e}"
      | Expr.app e₁ e₂ => s!"({loop e₁}) ({loop e₂})"
    loop

#eval Var.mk 0
#eval Expr.var (Var.mk 0)
#eval Expr.lam (Var.mk 0) (Expr.var (Var.mk 0))
#eval Expr.app (Expr.lam (Var.mk 0) (Expr.var (Var.mk 0))) (Expr.var (Var.mk 0))

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
