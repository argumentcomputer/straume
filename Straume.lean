namespace Straume
/-
     The big idea of this library

      boxed stuff is implemented

 ┌───────┐
 │  Real │             ┌──────┐
 │ World ├─Driver─┬──► │Stream│
 └───────┘        │    └──────┘
                  │
                  │
                  └──►  Async Stream



           ┌──────┐
   ┌───────┤Stream├─────────┐
   │       └───┬──┘         │
   │           │            │
   │           │            │
   │           │            │
   ▼           ▼            ▼
┌──────┐
│ Pull │     Sample        Push
│(file)│    (sensor)     (channel)
└──────┘



Every stream is laggy, samples are expected to fail, pushes are expected to be slow to present new data, if no new data has arrived yet.
Thus, every stream is equipped with a clock, as well as tracking how much data was streamed through it to the moment.
Reading from a stream implies a timeout.
It means that synchronous Stream (the only one currently implemented) is, really, a synchronous API for an async IO task.
Any read can fail with a timeout.

You can model a stream outside IO, say, for model checking and other testing approaches.
Code using Streams is be compatible with system testing if and only if the it is equpped with a facility to hoist the outer monad.
For more details on this approach, consult this exchange in haskell-cafe:

> > On Mar 31, 2016 10:10 AM, "David Turner" < redacted >
> wrote:
> >>
> >> Hi Jonn,
> >>
> >> I work on a similar-sounding system. We have arranged things so that
> each node is a pure state machine, with outputs that are a pure function of
> its inputs, with separate (and simple, obviously correct) machinery for
> connecting these state machines over the network. This makes it rather
> simple to run a bunch of these state machines in a test harness that
> simulates all sorts of network nastiness (disconnections, dropped or
> reordered messages, delays, corruption etc.) on a single thread.
> >>
> >> One trick that proved useful was to feed in the current time as an
> explicit input message. This makes it possible to test things like timeouts
> without having to actually wait for the time to pass, which speeds things
> up immensely. We also make use of ContT somewhere in the tests to
> interleave processing and assertions, and to define a 'hypothetically'
> operator that lets a test run a sequence of actions and then backtrack.
> >>
> >> I think this idea was inspired by
> https://github.com/NicolasT/paxos/blob/master/bin/synod.hs, at least the
> network nastiness simulator thing. He uses threads for that demo but the
> nodes' behaviour itself is pure:
> https://github.com/NicolasT/paxos/blob/master/src/Network/Paxos/Synod/Proposer.hs
> for example.
> >>
> >> We also have proved certain key properties of the network are implied
> by certain local invariants, which reduces the testing problem down to one
> of checking properties on each node separately. This was time consuming,
> but highlighted certain important corner cases that it's unlikely we would
> have found by random testing.
> >>
> >> If you're interested in Byzantine behaviour (the 'evil node' test) then
> you may enjoy reading James Mickens' article on the subject:
> https://www.usenix.org/publications/login-logout/may-2013/saddest-moment
> >>
> >> Hope that helps,
> >>
> >> David
> >>
> >> On 31 March 2016 at 00:41, Jonn Mostovoy < redacted > wrote:
> >>>
> >>> Dear friends,
> >>>
> >>> we have a distributed system written in Haskell, consisting of three
> >>> types of nodes with dozen of instances of each of two types and a
> >>> central node of the third type.
> >>>
> >>> Each node is started by executing a binary which sets up acid-state
> >>> persistence layer and sockets over which msgpack messages are sent
> >>> around.
> >>>
> >>> It is trivial to write low level functionality quickcheck test suites,
> >>> which test properties of functions.
> >>>
> >>> We would like, however, to have a quickcheck-esque suite which sets up
> >>> the network, then gets it to an arbitrary valid state (sending correct
> >>> messages between nodes), then rigorously testing it for three
> >>> high-level properties:
> >>>
> >>> 1. Chaos monkey test (disable random node, see if certain invariants
> hold);
> >>> 2. Evil node test (make several nodes work against the system, see if
> >>> certain properties hold);
> >>> 3. Rigorous testing of network-wide invariants, if all the nodes
> >>> operate correctly.
> >>>
> >>> The problem we're facing is the following — if we want to inspect
> >>> state of nodes in Haskell-land, we have to write a huge machinery
> >>> which emulates every launch of node via thread. There will be bugs in
> >>> this machinery, so we won't be able to get quality testing information
> >>> before we fix those; if we want to run things as processes, then the
> >>> best thing we can do is to inspect either acid-state dbs of each node
> >>> (it poses resource locking problems and forces us to dump the state on
> >>> every change, which is undesirable), or make an observer node, which
> >>> dumps the consensus as Text and then parsing the data into Haskell
> >>> terms, making decisions about the required properties based on that
> >>> (so far, it feels like the best option).
> >>>
> >>> Am I missing something? How is something like this achieved in
> >>> culture? How would you approach such a problem?
> >>>
> >>> Links to source files of test suites which do something similar are
> >>> highly appreciated.
-/

/- False positives are used to represent probabilistic results.

TODO: It's known that the runtime we're targetting at Yatima isn't well-suited for Floats. Our ProbParOrd wants Float probabilities.
Perhaps, it makes sense, for probabilistic computations, to equip those with a probability approximation facilities to convert those to some close rational number.
class ToRational.

 -/
inductive FalsePositive where
| perhaps : Float → FalsePositive
| no
  deriving Repr, BEq

/- False negatives aren't currently used and are defined just for symmetry. -/
inductive FalseNegative where
| yes
| hardly : Float → FalseNegative
  deriving Repr, BEq

def forSure (x : Bool := true) : FalsePositive := if x then .perhaps 1.0 else .no
def surelyNot (x : Bool := true) : FalseNegative := if x then .hardly 1.0 else .yes

def anti (f : α → α → α) [BEq α] : α → α → α :=
  fun x y =>
    let z := f x y
    if z == x then y else x

/- Kind of like or, keeping the false positive with higher confidence. -/
def assure (x : FalsePositive) (y : FalsePositive) : FalsePositive :=
  match (x, y) with
  | (.perhaps xₙ, .no) => x
  | (.perhaps xₙ, .perhaps yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

/- Kind of like and, keeping the false positive with the lower confidence. -/
def doubt := anti assure

/- Kind of like and, keeping the false negative with higher confidence. -/
def disprove (x : FalseNegative) (y : FalseNegative) : FalseNegative :=
  match (x, y) with
  | (.hardly xₙ, .yes) => x
  | (.hardly xₙ, .hardly yₙ) => if (xₙ > yₙ) then x else y
  | (_, _) => y

/- Kind of like or, keeping the false positive with the highest confidence. -/
def convince := anti disprove

structure Incomparable

inductive POrdering where
| incomparable
| eq -- We use eq from BEq, so it's always certain
| lt : FalsePositive → POrdering
| gt : FalsePositive → POrdering

/-
Partial probabilistic ordering for timestamped events.
The probabilistic bit is needed for the forward compatibility with Bloom Clocks.

NB!
The wording is important.
Partial probabilistic ordering means that it's certainly partial and perhaps ordered.
If something is incomparable, you can be sure that the preimages of it are incomparable, if something is less than something else, you are given a confidence in the ordering.
-/
class PartialPOrdering (α : Type u) [BEq α] where
  lt : α → α → PSum Incomparable FalsePositive
  le : α → α → PSum Incomparable FalsePositive :=
    fun x y => match lt x y with
               | .inl _ => PSum.inl Incomparable.mk
               | .inr z => PSum.inr $ assure z (forSure $ BEq.beq x y)
  compare : α → α → POrdering :=
    fun x y => match le x y with
               | .inl _ => POrdering.incomparable
               | .inr .no => match le y x with
                             | .inl _ => POrdering.incomparable
                             | .inr .no => POrdering.eq
                             | .inr z => POrdering.gt z
               | .inr z => POrdering.lt z

-- TODO: add theorems? Extend PartialOrder from mathlib? Idk.

instance ord2pord [BEq α] [Ord α] : PartialPOrdering α where
  lt x y := .inr $ forSure $ Ordering.lt == Ord.compare x y

-- TODO: Namespace Straume.Clock.Logical

class Clock (α : Type u) [BEq α] [PartialPOrdering α] where
  tick : α → α
  merge : α → α → α

/-
The simplest logical clock.
-/
structure Wristwatch where
  face : Nat
  deriving Repr, BEq, Ord

instance : PartialPOrdering Wristwatch := ord2pord

instance : Clock Wristwatch where
  tick x := Wristwatch.mk $ 1 + x.face
  merge x y := Wristwatch.mk $ 1 + max x.face y.face

/-

-/
