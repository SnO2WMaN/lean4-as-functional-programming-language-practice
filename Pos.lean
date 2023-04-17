inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos 

namespace Pos 

def two : Pos := Pos.succ Pos.one
def three : Pos := Pos.succ Pos.two

def toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ p => p.toNat + 1 

instance : ToString Pos where toString x := toString x.toNat

#eval two
#eval three

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec loop : Nat → Pos
      | 0 => Pos.one
      | p + 1 => Pos.succ (loop p)
    loop n

def four : Pos := 4
#eval four

def add : Pos → Pos → Pos
  | one, p => succ p
  | succ p, q => succ (add p q) 
instance : Add Pos where add := add

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => succ (addNatPos n p)
instance : HAdd Nat Pos Pos where hAdd := addNatPos
#eval (0 : Nat) + (5 : Pos)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => succ (addPosNat p n)
instance : HAdd Pos Nat Pos where hAdd := addPosNat
#eval (5 : Pos) + (0 : Nat)

def mul : Pos → Pos → Pos
  | one, p => p
  | succ p, q => q + (mul p q)
instance : Mul Pos where mul := mul

def comp : Pos → Pos → Ordering
  | one, one => Ordering.eq
  | one, succ _ => Ordering.lt
  | succ _, one => Ordering.gt
  | succ p, succ q => comp p q
instance : Ord Pos where compare := comp

instance : Coe Pos Nat where coe := toNat
#eval [1,2,3,4].drop (2:Pos)

def oneInt : Int := Pos.one
#check oneInt

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := (392 : Nat)
def perhapsPerhapsPerhapsNat₂ : Option (Option (Option Nat)) := ↑(392 : Nat)  
#check perhapsPerhapsPerhapsNat

end Pos