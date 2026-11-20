import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.NpDescOfValRat
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions Formalism.MainNotions.G Formalism.BasicNotions Formalism.L2.Forms

def ValRatF {eps : ℝ} (Fm : FamP eps) : Prop :=
  Ev Fm fun x i => ∀ hx : Fm.x1 < x, ValRat (Fm.ex x hx i).cmp

/- English proof (translation)
Take `⟨x0, hx0⟩` from `h`. Use `⟨x0, fun x hx i hx1 => ?_⟩` and prove the remaining obligations. Use `npDesc_of_valRat _ (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK ?_ (hx0 x hx i hx1)` and prove the remaining obligations. Conclude with `(Fm.ex x hx1 i).lat.vram`.
-/
theorem npDescF_of_valRatF {eps : ℝ} (Fm : FamP eps) (h : ValRatF Fm) : NPDescF Fm := by
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx i hx1 => ?_⟩
  refine npDesc_of_valRat _ (Fm.gatT x i) (Fm.Gx x i) (Fm.Gy x i) Fm.GK ?_ (hx0 x hx i hx1)
  exact (Fm.ex x hx1 i).lat.vram

/- English proof (translation)
Introduce `u w hg x i L hL`. Conclude with `⟨_, ((K.tie u w hg).val_cmp x i L hL).symm⟩`.
-/
theorem CmpTied.valRat {D : D7} {X : Formalism.L2.Herm.Herm0 D} {T : ∀ u : D.what₂.Word, Forms0 D u} {Gt : GatTies D}
    {c : LatCmp D} (K : CmpTied D X T Gt c) : ValRat c := by
  intro u w hg x i L hL
  exact ⟨_, ((K.tie u w hg).val_cmp x i L hL).symm⟩

end Formalism.L2.G.Cmp
