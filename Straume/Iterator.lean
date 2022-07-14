namespace Iterator

instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue h₁  => isTrue $ congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse $ fun h => by cases h; exact (h₂ rfl)


class HasTokens (α : Type _) (β : Type _) where
  tokens : α → List β
  push : α → β -> α

export HasTokens (tokens push)

instance : HasTokens String Char where
  tokens := String.data
  push := String.push

instance : HasTokens ByteArray UInt8 where
  tokens := ByteArray.toList
  push := ByteArray.push


structure Iterator (α : Type) where
  s : α
  i : Nat
  deriving DecidableEq, Repr

def iter (s : α) : Iterator α :=
  ⟨s, 0⟩


class Iterable (α : Type) where
  length : α -> Nat
  hasNext : Iterator α -> Bool
  next : Iterator α -> Iterator α
  extract : Iterator α → Iterator α → α

export Iterable (length hasNext next extract)


instance : Iterable String where
  length s := s.length 
  hasNext | ⟨s, i⟩ => i < s.endPos.byteIdx
  next | ⟨s, i⟩ => ⟨s, (s.next ⟨i⟩).byteIdx⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then ""
      else s₁.extract ⟨b⟩ ⟨e⟩

instance : Iterable ByteArray where
  length s := s.size
  hasNext | ⟨s, i⟩ => i < s.size
  next | ⟨s, i⟩ => ⟨s, i+1⟩
  extract
    | ⟨s₁, b⟩, ⟨s₂, e⟩ =>
      if s₁ ≠ s₂ || b > e then default
      else s₁.extract b e


def curr (β : Type _) [HasTokens α β] [Inhabited β] (it: Iterator α) [Iterable α] : β :=
  let ts := tokens it.s
  match ts.get? it.i with
    | some curr! => curr!
    | none       => default -- unreachable: pos shouldn't increase if ¬s.hasNext

def forward [Iterable α] : Iterator α → Nat → Iterator α
  | it, 0   => it
  | it, n+1 => forward (next it) n