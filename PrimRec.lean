abbrev ℕ := Nat

namespace Nat

def sqrt.iter (n : ℕ) (guess : ℕ) : ℕ :=
  if (guess + n / guess) / 2 < guess
    then sqrt.iter n ((guess + n / guess) / 2)
    else guess

def sqrt (n : ℕ) : ℕ := if n ≤ 1 then n else sqrt.iter n (n / 2)

/-- Gödel's paring function -/
def pair (n₁ n₂ : ℕ) : ℕ := if n₁ < n₂ then n₁ + (n₂^2) else (n₁^2) + n₁ + n₂

theorem pair_uniq (n₁ n₂ m₁ m₂: ℕ) : (h : (n₁ ≠ m₁) ∧ (n₂ ≠ m₂)) → pair n₁ n₂ ≠ pair m₁ m₂ := sorry

def pair₂ (n : ℕ × ℕ) : ℕ := pair n.1 n.2

theorem eq_pair_pair₂ (n₁ n₂ : ℕ) : pair n₁ n₂ = pair₂ (n₁,n₂) := by simp [pair₂]

/-- Inverse of Gödel's pairing function -/
def unpair (n : ℕ) : ℕ × ℕ :=
  let s := Nat.sqrt n; if n - s^2 < s then (n - s^2, s) else (s, n - s^2 - s)

#eval pair₂ (unpair 5)

theorem eq_pair_unpaired (n : ℕ) : pair₂ (unpair n) = n := sorry
theorem eq_unpaired_pair (n₁ n₂ : ℕ) : (unpair (pair n₁ n₂)) = (n₁,n₂) := sorry

def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2

def prec (f g : ℕ → ℕ) (n : ℕ) :=
  let (x,y) := (unpair n)
  match y with
  | 0 => f x
  | n + 1 => let xn := pair x n; (g (pair xn (prec f g xn)))

inductive PrimRec : (ℕ → ℕ) → Prop
  | succ  : PrimRec λ n => n + 1
  | const : ∀ c : ℕ, PrimRec (λ _ => c)
  | left  : PrimRec λ n => (unpair n).1
  | right : PrimRec λ n => (unpair n).2
  | pair {f g} : PrimRec f → PrimRec g → PrimRec (λ n => Nat.pair (f n) (g n))
  | comp {f g} : PrimRec f → PrimRec g → PrimRec (λ n => f (g n))
  | prec {f g} : PrimRec f → PrimRec g → PrimRec (Nat.prec f g)

namespace PrimRec

def zero := λ (_ : ℕ) => 0
theorem primrec_zero : PrimRec zero := PrimRec.const 0

def one := λ (_ : ℕ) => 1
theorem primrec_one : PrimRec one := PrimRec.const 1

theorem primrec_id : PrimRec id := sorry

def paired₂ (f : ℕ → ℕ) := λ x y => f (Nat.pair x y)

def add.intr := Nat.prec id (unpaired (λ _xn hxn => hxn + 1))
def add := paired₂ add.intr
#eval add 1 3
#eval add 0 2
#eval add 2 2

theorem primrec_add : PrimRec add.intr := sorry

def sub.intr := Nat.prec id (unpaired (λ _xn hxn => hxn - 1))
def sub := paired₂ sub.intr
#eval sub 4 2
#eval sub 0 2
#eval sub 2 0

theorem primrec_sub : PrimRec sub.intr := sorry

def mul.intr := Nat.prec zero (unpaired (λ xn hxn => add (unpair xn).1 hxn))
def mul := paired₂ mul.intr
#eval mul 4 9
#eval mul 0 2
#eval mul 2 0

theorem primrec_mul : PrimRec mul.intr := sorry

def pow.intr := Nat.prec one (unpaired (λ xn hxn => mul (unpair xn).1 hxn))
def pow := paired₂ pow.intr
#eval pow 2 3
#eval pow 0 2
#eval pow 2 0
theorem primrec_pow : PrimRec pow.intr := sorry

end PrimRec

end Nat
