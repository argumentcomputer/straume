import Straume.Iterator
open Iterator

/-

To make Zeptoparsec work on another type γ, define all the necessary
scaffolding in Iterator.lean, currently:
- instance Iterable γ μ, where μ is the type that γ semantically consists of

-/

/- TODO: somehow make most of σ's implicit -/

namespace Zeptoparsec

variable (σ : Type) [Iterable σ ε] [Inhabited σ] [DecidableEq σ] [DecidableEq ε] [Inhabited ε]

namespace Parsec
inductive ParseResult (α: Type) where
  | success (pos : Iterator σ) (res : α)
  | error (pos : Iterator σ) (err : String)
  deriving Repr

def Parsec (α : Type) : Type := Iterator σ → ParseResult σ α

end Parsec

namespace Parsec
open ParseResult

instance (α : Type) : Inhabited (Parsec σ α) :=
  ⟨λ it => error it ""⟩

@[inline]
protected def pure (a : α) : Parsec σ α := λ it =>
 success it a

@[inline]
def bind {α β : Type} (f : Parsec σ α) (g : α → Parsec σ β) : Parsec σ β := λ it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

instance : Monad (Parsec σ) :=
  { pure := Parsec.pure σ, bind := bind σ }

@[inline]
def fail (msg : String) : Parsec σ α := fun it =>
  error it msg

@[inline]
def orElse (p : Parsec σ α) (q : Unit → Parsec σ α) : Parsec σ α := fun it =>
  match p it with
  | success rem a => success rem a
  | error rem err =>
    if it = rem then q () it else error rem err

@[inline]
def attempt (p : Parsec σ α) : Parsec σ α := λ it =>
  match p it with
  | success rem res => success rem res
  | error _ err => error it err

instance : Alternative (Parsec σ) :=
{ failure := fail σ "", orElse := orElse σ }

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec σ Unit := fun it =>
  if Iterable.hasNext it then
    error it expectedEndOfInput
  else
    success it ()

@[inline]
partial def manyCore (p : Parsec σ α) (acc : Array α) : Parsec σ $ Array α :=
  (do manyCore p (acc.push $ ←p))
  <|> pure acc

@[inline]
def many (p : Parsec σ α) : Parsec σ $ Array α := manyCore σ p #[]

@[inline]
def many1 (p : Parsec σ α) : Parsec σ $ Array α := do manyCore σ p #[←p]

@[inline]
partial def manyCharsCore (p : Parsec σ ε) (acc : σ) : Parsec σ σ :=
  (do manyCharsCore p (push acc $ ←p))
  <|> pure acc

-- Parses zero or more occurrences
@[inline]
def manyChars (p : Parsec σ ε) : Parsec σ σ := manyCharsCore σ p default

-- Parses one or more occurrences
@[inline]
def many1Chars (p : Parsec σ ε) : Parsec σ σ := do
  manyCharsCore σ p $ push default (←p)

def pstring (s : σ) : Parsec σ σ := λ it =>
  let substr := extract it (forward it $ length s)
  if substr = s then
    success (forward it $ length s) substr
  else
    -- error it s!"expected: {s}" -- TODO
    error it s!"expected something else"

@[inline]
def skipString (s : σ) : Parsec σ Unit := pstring σ s *> pure ()

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec σ ε := λ it =>
  if hasNext it
  then success (next it) $ curr it
  else error it unexpectedEndOfInput

@[inline]
def pchar (c : ε) : Parsec σ ε := attempt σ do
  -- if (←anyChar σ) = c then pure c else fail σ s!"expected: '{c}'" -- TODO
  if (←anyChar σ) = c then pure c else fail σ s!"expected some other char"

@[inline]
def skipChar (c : ε) : Parsec σ Unit := pchar σ c *> pure ()

@[inline]
def satisfy (p : ε → Bool) : Parsec σ ε := attempt σ do
  let c ← anyChar σ
  if p c then return c else fail σ "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec σ α) : Parsec σ Unit := λ it =>
  match p it with
  | success _ _ => error it ""
  | error _ _ => success it ()

@[inline]
def peek? : Parsec σ (Option ε) := fun it =>
  if hasNext it then
    success it $ curr it
  else
    success it none

@[inline]
def peek! : Parsec σ ε := do
  let some c ← peek? σ | fail σ unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec σ Unit := fun it =>
  success (next it) ()

-- String-specific

@[inline]
def digit : Parsec String Char := attempt String do
  let c ← anyChar String
  if '0' ≤ c ∧ c ≤ '9' then return c else fail String s!"digit expected"

@[inline]
def hexDigit : Parsec String Char := attempt String do
  let c ← anyChar String
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'a')
   ∨ ('A' ≤ c ∧ c ≤ 'A') then return c else fail String s!"hex digit expected"

@[inline]
def asciiLetter : Parsec String Char := attempt String do
  let c ← anyChar String
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then return c else fail String s!"ASCII letter expected"

partial def skipWs (it : Iterator String) : Iterator String :=
  if hasNext it then
    let c := curr it
    if c = '\u0009' ∨ c = '\u000a' ∨ c = '\u000d' ∨ c = '\u0020' then
      skipWs $ next it
    else
      it
  else
   it

@[inline]
def ws : Parsec String Unit := fun it =>
  success (skipWs it) ()
end Parsec