namespace Bit

-- Bools don't give us enough type safety, I think;
-- does Lean have a built-in better alternative?
inductive Bit : Type where
  | zero : Bit
  | one  : Bit
  deriving DecidableEq, Inhabited

export Bit (zero one)

instance : Repr Bit where
  reprPrec
    | zero, _ => "0"
    | one,  _ => "1"

theorem Nat.div2_lt (h : n ≠ 0) : n / 2 < n := by
  match n with
  | 1   => decide
  | 2   => decide
  | 3   => decide
  | n+4 =>
    rw [Nat.div_eq, if_pos]
    refine Nat.succ_lt_succ (Nat.lt_trans ?_ (Nat.lt_succ_self _))
    exact @div2_lt (n+2) (by simp_arith)
    simp_arith

def toBits : Nat → List Bit
  | 0 => [zero]
  | 1 => [one]
  | n + 2 => 
    have h₁ : (n + 2) ≠ 0 := by simp_arith
    toBits ((n + 2) / 2) ++ (if n % 2 = 0 then [zero] else [one])
  termination_by _ n => n
  decreasing_by exact Nat.div2_lt h₁;

def pad (n : Nat) (bs : List Bit) : List Bit :=
  let l := bs.length
  if l >= n then bs else List.replicate (n - l) zero ++ bs

def uint8ToBits (u : UInt8) : List Bit :=
  pad 8 $ toBits $ UInt8.toNat u

def byteArrayToBits (ba : ByteArray) : List Bit :=
  List.join $ List.map uint8ToBits $ ByteArray.toList ba

def List.extract (l : List α) (b : Nat) (e : Nat) : List α :=
  if b > e then l else
    let lₐ := l.drop b
    lₐ.take (e - b)