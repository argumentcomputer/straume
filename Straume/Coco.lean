namespace Straume.Coco

/- `Coco`s are `y`s that carry and allow to swap out `x`s.
So `x`s are "contained" in `y`s.
Sort of Flipped Coe with an additional `replace` method.
Preventing typeclass clashes in transient dependencies in style. -/
class Coco (x : Type u) (y : outParam (Type u)) where
  coco : y → x
  replace : y → x → y

instance : Coco String (String × IO.FS.Handle) where
  coco := Prod.fst
  replace kl k := (k, Prod.snd kl)

instance {α : Type u} : Coco α α where
  coco := id
  replace _ x := x
