namespace Bit

inductive Endian where
  | big    : Endian
  | little : Endian
  deriving Repr, DecidableEq, Inhabited

export Endian (big little)

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

instance : ToString Bit where
  toString
    | zero => "0"
    | one => "1"

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

def natToBits : Nat → List Bit
  | 0 => [zero]
  | 1 => [one]
  | n + 2 => 
    have h₁ : (n + 2) ≠ 0 := by simp_arith
    natToBits ((n + 2) / 2) ++ (if n % 2 = 0 then [zero] else [one])
  termination_by _ n => n
  decreasing_by exact Nat.div2_lt h₁;

def pad (n : Nat) (bs : List Bit) : List Bit :=
  let l := bs.length
  if l >= n then bs else List.replicate (n - l) zero ++ bs

def uint8ToBits (u : UInt8) : List Bit :=
  pad 8 $ natToBits $ UInt8.toNat u

def byteArrayToBits (ba : ByteArray) : List Bit :=
  List.join $ List.map uint8ToBits $ ByteArray.toList ba

def List.extract (l : List α) (b : Nat) (e : Nat) : List α :=
  if b > e then l else
    let lₐ := l.drop b
    lₐ.take (e - b)

/-- Interprets a `List Bit` as a `Nat`, taking `Endian`ness into consideration. -/
def bitsToNat (l: List Bit) (en : Endian := big) : Nat :=
  let rec go
    | [], acc => acc
    | b :: bs, acc => go bs $ acc * 2 + (if b = zero then 0 else 1)
  let bits := if en = big then l else List.reverse l
  go bits default

/--
Takes first `n` elems of the `List Bit` and interprets them as a `Nat`.
Returns `none` if the list is shorter than `n`.
-/
def someBitsToNat? (n : Nat) (l: List Bit) (en : Endian := big) : Option Nat :=
  if n > l.length || n = 0 then .none else .some $ bitsToNat (l.take n) en