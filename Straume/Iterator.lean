import YatimaStdLib.Bit

namespace Straume.Iterator
universe u

/-
  We implement a `Repr` instance for `ByteArray` instead of a `ToString`
  instance for `Iterator α`. At this point, this is a deliberate choice:
  it's possible we might want to write ToString instances to only show
  the "remaining" part of the iterator, i.e. a slice of s from i to the end.

  `Repr ByteArray`, however, we need for debug.
  TODO?
-/

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; exact (h₂ rfl)

structure Iterator (α : Type u) where
  s : α
  i : Nat
  deriving DecidableEq, Repr

def iter (s : α) : Iterator α :=
  ⟨s, 0⟩

instance : Functor Iterator where
  map | f, ⟨s, i⟩ => ⟨f s, i⟩

class Iterable (α : Type u) (β : outParam (Type u)) where
  push : α → β → α
  length : α → Nat
  hasNext : Iterator α → Bool
  next : Iterator α → Iterator α
  extract : Iterator α → Iterator α → α
  curr : Iterator α → β

export Iterable (push length hasNext next extract curr)

instance : Iterable String Char where
  push := String.push
  length s := s.length
  hasNext | ⟨s, i⟩ => i < s.endPos.byteIdx
  next | ⟨s, i⟩ => if i < s.endPos.byteIdx
    then ⟨s, (s.next ⟨i⟩).byteIdx⟩
    else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract ⟨b⟩ ⟨e⟩
  curr | ⟨s, i⟩ => if i < s.endPos.byteIdx
    then s.get ⟨i⟩
    else s.get ⟨s.endPos.byteIdx - 1⟩

instance : Iterable ByteArray UInt8 where
  push := ByteArray.push
  length s := s.size
  hasNext | ⟨s, i⟩ => i < s.size
  next | ⟨s, i⟩ => if i < s.size then ⟨s, i+1⟩ else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract b e
  curr | ⟨s, i⟩ => let i' := if i < s.size then i else s.size - 1
      -- pos shouldn't increase if ¬s.hasNext, but it's possible to construct
      -- such an iterator manually, so we have to return the last byte.
    s.get! i'

instance : Iterable (List Bit) Bit where
  push := List.concat
  length s := s.length
  hasNext | ⟨s, i⟩ => i < s.length
  next | ⟨s, i⟩ => if i < s.length then ⟨s, i+1⟩ else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ then default
      else (s₁.drop b).take (e - b)
  curr | ⟨s, i⟩ => let i' := if i < s.length then i else s.length - 1
      -- pos shouldn't increase if ¬s.hasNext, but it's possible to construct
      -- such an iterator manually, so we have to return the last byte.
    if s.isEmpty then default else s.get! i'

def forward [Iterable α β] : Iterator α → Nat → Iterator α
  | it, 0   => it
  | it, n+1 => forward (next it) n

def fromList (xs : List β) [Inhabited α] [Iterable α β] : α :=
  -- TODO: Consider adding fromList to Iterable?..
  -- if (α = (List Bit)) ∧ (β = Bit)
  -- then xs
  List.foldl (fun acc x => push acc x) default xs

private partial def toList' (it : Iterator α) [Iterable α β] : List β :=
  if hasNext it then curr it :: toList' (next it) else []

def toList (src : α) [Iterable α β] : List β := toList' $ iter src

-- We define an empty class here to show Lean that the functional
-- dependency that Iterable uses also works in the other direction,
-- i.e. `Char` can only be gotten by iterating over `String`s.
class Bijection (β : Type u) (α : outParam (Type u))

set_option synthInstance.checkSynthOrder false in
instance [Iterable α β] : Bijection β α := {}
