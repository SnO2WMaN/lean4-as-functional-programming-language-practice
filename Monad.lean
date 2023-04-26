

def get1_3_5_7 [Monad m] (lookup: List α → Nat → m α) (xs : List α) :=
  lookup xs 1 >>= fun x1 =>
  lookup xs 3 >>= fun x3 =>
  lookup xs 5 >>= fun x5 =>
  lookup xs 7 >>= fun x7 =>
  pure (x1, x3, x5, x7)

#eval get1_3_5_7 (fun xs i => xs[i]?) [0, 1, 2, 3, 4, 5]
#eval get1_3_5_7 (fun xs i => xs[i]?) [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]

def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun y =>
    mapM f xs >>= fun ys =>
    pure (y :: ys)

#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]

namespace Arithmetic

inductive Expr (op : Type) where
| const : Int → Expr op
| prim : op → Expr op → Expr op → Expr op

inductive Arith where
| add | mul | sub | div

open Expr
open Arith

def two : Expr Arith := const 2
def three : Expr Arith := const 3

def add_two_three := prim add two three

-- 14 / (45 - 5 * 9)
def E2 : Expr Arith := prim div (const 14) (prim sub (const 45) (prim mul (const 5) (const 9)))

def applyPrimOption : Arith → Int → Int → Option Int
| Arith.add, v1, v2 => Option.some (v1 + v2)
| Arith.mul, v1, v2 => Option.some (v1 * v2)
| Arith.sub, v1, v2 => Option.some (v1 - v2)
| Arith.div, v1, v2 => if v2 == 0 then Option.none else pure (v1 / v2)

def evaluateOption : Expr Arith → Option Int
| Expr.const n => Option.some n
| Expr.prim op e1 e2 =>
  evaluateOption e1 >>= fun v1 =>
  evaluateOption e2 >>= fun v2 =>
  applyPrimOption op v1 v2

def applyPrimExcept : Arith → Int → Int → Except String Int
| Arith.add, v1, v2 => Except.ok (v1 + v2)
| Arith.mul, v1, v2 => Except.ok (v1 * v2)
| Arith.sub, v1, v2 => Except.ok (v1 - v2)
| Arith.div, v1, v2 => if v2 == 0 then Except.error s!"You can't divide {v1} by 0" else pure (v1 / v2)

def evaluateExcept : Expr Arith → Except String Int
| Expr.const n => Except.ok n
| Expr.prim op e1 e2 =>
  evaluateExcept e1 >>= fun v1 =>
  evaluateExcept e2 >>= fun v2 =>
  applyPrimExcept op v1 v2

#eval evaluateOption add_two_three
#eval evaluateExcept E2

def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int) : Expr Arith → m Int
| Expr.const n => pure n
| Expr.prim op e1 e2 =>
  evaluateM applyPrim e1 >>= fun v1 =>
  evaluateM applyPrim e2 >>= fun v2 =>
  applyPrim op v1 v2

#eval evaluateM applyPrimOption E2
#eval evaluateM applyPrimExcept E2

def applyPrimM [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
| Arith.add, v1, v2 => pure (v1 + v2)
| Arith.mul, v1, v2 => pure (v1 * v2)
| Arith.sub, v1, v2 => pure (v1 - v2)
| Arith.div, v1, v2 => applyDiv v1 v2

def applyDivOption (x y : Int) := if y == 0 then Option.none else pure (x / y)
def applyDivExcept (x y : Int) := if y == 0 then Except.error s!"You can't divide {x} by 0" else pure (x / y)

def evaluateM₂ [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
| Expr.const n => pure n
| Expr.prim op e1 e2 =>
  evaluateM₂ applyDiv e1 >>= fun v1 =>
  evaluateM₂ applyDiv e2 >>= fun v2 =>
  applyPrimM applyDiv op v1 v2

#eval evaluateM₂ applyDivOption E2
#eval evaluateM₂ applyDivExcept E2

end Arithmetic


namespace NDArithmetic

inductive Many (α : Type) where
| none : Many α
| more : α → (Unit → Many α) → Many α

def Many.one (x : α) : Many α := Many.more x (fun _ => Many.none)

def Many.union : Many α → Many α → Many α
| Many.none, ys => ys
| Many.more x xs, ys => Many.more x (fun _ => Many.union (xs ()) ys)

def Many.fromList : List α → Many α
| [] => Many.none
| x :: xs => Many.union (Many.one x) (Many.fromList xs)

def Many.take : Nat → Many α → List α
| 0, _ => []
| _ + 1, Many.none => []
| n + 1, Many.more x xs => x :: Many.take n (xs ())

def Many.takeAll : Many α → List α
| Many.none => []
| Many.more x xs => x :: Many.takeAll (xs ())

def Many.bind : Many α → (α → Many β) → Many β
| Many.none, _ => Many.none
| Many.more x xs, f => (f x).union (Many.bind (xs ()) f)

instance : Monad Many where
  pure := Many.one
  bind := Many.bind

def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] => if goal == 0 then  pure [] else Many.none
  | x :: xs =>
    if x > goal then addsTo goal xs
    else (addsTo goal xs).union (addsTo (goal - x) xs >>= fun answer => pure (x :: answer))

end NDArithmetic
