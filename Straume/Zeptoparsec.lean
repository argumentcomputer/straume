import Straume.Iterator
open Straume.Iterator

/-

This is a library defining a simplistic parser, modeled after Parsec.lean.
Three type pairs are provided: String↔Char, ByteArray↔UInt8, and List Bit↔Bit.

To make Zeptoparsec work on another type γ, define all the necessary
scaffolding in Iterator.lean, currently:
- instance Iterable γ μ, where μ is the type that γ semantically consists of
- if not present, instances DecidableEq γ and DecidableEq μ
- if not present, instances Inhabited γ and Inhabited μ

To use Zeptoparsec, compose all the combinators before applying them
to the source iterator.

-/

namespace Zeptoparsec

universe u
universe v

variable {σ : Type u} [Iterable σ ε] [Inhabited σ] [DecidableEq σ] [DecidableEq ε] [Inhabited ε]

inductive ParseResult (σ α: Type u) where
  | success (it : Iterator σ) (res : α)
  | error (it : Iterator σ) (err : String)
  deriving Repr, DecidableEq

def Parsec (σ α : Type u) : Type u := Iterator σ → ParseResult σ α

open ParseResult

-- Usually, we compose parsers before applying the composition to the
-- iterator/source. However, we might want to parse out an intermediate
-- result and then continue parsing the resulting iterator. `deparse` is
-- provided for convenience.
@[inline]
def deparse : ParseResult σ α → Iterator σ
  | success it _ => it
  | error   it _ => it

instance (α : Type u) : Inhabited (Parsec σ α) :=
  ⟨λ it => error it ""⟩

@[inline]
protected def pure (a : α) : Parsec σ α := λ it =>
 success it a

@[inline]
def bind {α β : Type u} (f : Parsec σ α) (g : α → Parsec σ β) : Parsec σ β := λ it =>
  match f it with
  | success rem a => g a rem
  | error pos msg => error pos msg

instance : Monad (Parsec σ) :=
  { pure := Zeptoparsec.pure, bind }

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
{ failure := fail "", orElse := orElse }

---------------------------------
--     Semantic combinators
---------------------------------

def expectedEndOfInput := "expected end of input"

@[inline]
def eof : Parsec σ PUnit := fun it =>
  if hasNext it then
    error it expectedEndOfInput
  else
    success it PUnit.unit

@[inline]
partial def manyCore (p : Parsec σ α) (acc : Array α) : Parsec σ $ Array α :=
  (do manyCore p (acc.push $ ←p))
  <|> pure acc

@[inline]
def many (p : Parsec σ α) : Parsec σ $ Array α := manyCore p #[]

@[inline]
def many1 (p : Parsec σ α) : Parsec σ $ Array α := do manyCore p #[←p]

@[inline]
partial def someCore : Parsec σ α → Nat → Array α → Parsec σ (Array α)
  | _,   0, acc => pure acc
  | p, n+1, acc =>
    (do someCore p n (acc.push $ ←p))
    <|> pure acc

@[inline]
def some (p : Parsec σ α) (n : Nat) : Parsec σ $ Array α := someCore p n #[]

@[inline]
partial def manyCharsCore (p : Parsec σ ε) (acc : σ) : Parsec σ σ :=
  (do manyCharsCore p (push acc $ ←p))
  <|> pure acc

-- Parses zero or more occurrences
@[inline]
def manyChars (p : Parsec σ ε) : Parsec σ σ := manyCharsCore p default

-- Parses one or more occurrences
@[inline]
def many1Chars (p : Parsec σ ε) : Parsec σ σ := do
  manyCharsCore p $ push default (←p)

@[inline]
partial def someCharsCore : Parsec σ ε → Nat → σ → Parsec σ σ
  | _,   0, acc => pure acc
  | p, n+1, acc =>
    (do someCharsCore p n (push acc $ ←p))
    <|> pure acc

-- Parses one or more, up to `n`, occurrences, unless n is zero.
-- We deliberately do not allow to parse 0 characters otherwise, as that
-- will prevent composition with e.g. `many`.
@[inline]
def someChars (p : Parsec σ ε) (n : Nat) : Parsec σ σ := do
  if n = 0 then pure default else
  someCharsCore p (n-1) $ push default (←p)

def pstring (s : σ) : Parsec σ σ := λ it =>
  let substr := extract it (forward it $ length s)
  if substr = s then
    success (forward it $ length s) substr
  else
    -- error it s!"expected: {s}" -- TODO
    error it s!"expected something else"

@[inline]
def skipString (s : σ) : Parsec σ PUnit := pstring s *> pure PUnit.unit

def unexpectedEndOfInput := "unexpected end of input"

@[inline]
def anyChar : Parsec σ ε := λ it =>
  if hasNext it
  then success (next it) $ curr it
  else error it unexpectedEndOfInput

@[inline]
def pchar (c : ε) : Parsec σ ε := attempt do
  -- if (←anyChar) = c then pure c else fail s!"expected: '{c}'" -- TODO
  if (←anyChar) = c then pure c else fail s!"expected some other char"

@[inline]
def skipChar (c : ε) : Parsec σ PUnit := pchar c *> pure PUnit.unit

@[inline]
def satisfy (p : ε → Bool) : Parsec σ ε := attempt do
  let c ← anyChar
  if p c then return c else fail "condition not satisfied"

@[inline]
def notFollowedBy (p : Parsec σ α) : Parsec σ PUnit := λ it =>
  match p it with
  | success _ _ => error it ""
  | error _ _ => success it PUnit.unit

@[inline]
def peek? : Parsec σ (Option ε) := fun it =>
  if hasNext it then
    success it $ curr it
  else
    success it none

@[inline]
def peek! : Parsec σ ε := do
  let .some c ← peek? | fail unexpectedEndOfInput
  return c

@[inline]
def skip : Parsec σ PUnit := fun it =>
  if hasNext it then
    success (next it) PUnit.unit
  else
    error it unexpectedEndOfInput

---------------------------------
--       String-specific
---------------------------------

@[inline]
def digit : Parsec String Char := attempt do
  let c ← anyChar
  if '0' ≤ c ∧ c ≤ '9' then return c else fail s!"digit expected"

@[inline]
def hexDigit : Parsec String Char := attempt do
  let c ← anyChar
  if ('0' ≤ c ∧ c ≤ '9')
   ∨ ('a' ≤ c ∧ c ≤ 'a')
   ∨ ('A' ≤ c ∧ c ≤ 'A') then return c else fail s!"hex digit expected"

@[inline]
def asciiLetter : Parsec String Char := attempt do
  let c ← anyChar
  if ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') then return c else fail s!"ASCII letter expected"

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
