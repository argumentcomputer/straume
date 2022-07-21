import Straume.Bit
open Bit

namespace Iterator

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

instance : Repr ByteArray where
  reprPrec ba _ := toString ba

structure Iterator (α : Type) where
  s : α
  i : Nat
  deriving DecidableEq, Repr

def iter (s : α) : Iterator α :=
  ⟨s, 0⟩

class Iterable (α : Type) (β : outParam Type) where
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
  next | ⟨s, i⟩ => ⟨s, (s.next ⟨i⟩).byteIdx⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract ⟨b⟩ ⟨e⟩
  curr | ⟨s, i⟩ => s.get ⟨i⟩

instance : Iterable ByteArray UInt8 where
  push := ByteArray.push
  length s := s.size
  hasNext | ⟨s, i⟩ => i < s.size
  next | ⟨s, i⟩ => ⟨s, i+1⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract b e
  curr | ⟨s, i⟩ => let ts := ByteArray.toList s
    match ts.get? i with
      | some curr! => curr!
      | none       => default -- unreachable: pos shouldn't increase if ¬s.hasNext

instance : Iterable (List Bit) Bit where
  push := List.concat
  length s := s.length
  hasNext | ⟨s, i⟩ => i < s.length
  next | ⟨s, i⟩ => ⟨s, i+1⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ then default
      else List.extract s₁ b e
  curr | ⟨s, i⟩ => match s.get? i with
      | some curr! => curr!
      | none       => default -- unreachable: pos shouldn't increase if ¬s.hasNext

def forward [Iterable α β] : Iterator α → Nat → Iterator α
  | it, 0   => it
  | it, n+1 => forward (next it) n