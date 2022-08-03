import Straume.Bit
open Bit

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

instance : Repr ByteArray where
  reprPrec ba _ := toString ba

structure Iterator (α : Type u) where
  s : α
  i : Nat
  deriving DecidableEq, Repr

def iter (s : α) : Iterator α :=
  ⟨s, 0⟩

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
  hasNext | ⟨s, i⟩ => i < s.endPos.byteIdx - 1
  next | ⟨s, i⟩ => if i < s.endPos.byteIdx - 1
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
  hasNext | ⟨s, i⟩ => i < s.size - 1
  next | ⟨s, i⟩ => if i < s.size - 1 then ⟨s, i+1⟩ else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract b e
  curr | ⟨s, i⟩ => let ts := ByteArray.toList s
      -- pos shouldn't increase if ¬s.hasNext, but it's possible to construct
      -- such an iterator manually, so we have to return the last byte.
    let i' := if i < s.size then i else s.size - 1
    ts.get! i'

instance : Iterable (List Bit) Bit where
  push := List.concat
  length s := s.length
  hasNext | ⟨s, i⟩ => i < s.length - 1
  next | ⟨s, i⟩ => if i < s.length - 1 then ⟨s, i+1⟩ else ⟨s, i⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ then default
      else List.extract s₁ b e
  curr | ⟨s, i⟩ => let i' := if i < s.length then i else s.length - 1
      -- pos shouldn't increase if ¬s.hasNext, but it's possible to construct
      -- such an iterator manually, so we have to return the last byte.
    s.get! i'

def forward [Iterable α β] : Iterator α → Nat → Iterator α
  | it, 0   => it
  | it, n+1 => forward (next it) n

def fromList {α β : Type u} (xs : List β) [Inhabited α] [Iterable α β] : α :=
  -- TODO: Consider adding fromList to Iterable?..
  -- if (α = (List Bit)) ∧ (β = Bit)
  -- then xs
  List.foldl (fun acc x => Iterable.push acc x) default xs