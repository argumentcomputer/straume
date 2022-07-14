class Time (m : Type u → Type v) (σ : Type k) (α δ : Type u) where
  stamp : σ → m α
  delta : α → α → δ

instance : Time BaseIO Unit Nat Int where
  stamp _ := IO.monoMsNow
  delta x y := y - x

structure Wall where
  colour : Nat × Nat × Nat
  m : Type u → Type v
  s : Type u
  a : Type u
  d : Type u
  sDef : s
  clock : Time m s a d
  now : m a :=