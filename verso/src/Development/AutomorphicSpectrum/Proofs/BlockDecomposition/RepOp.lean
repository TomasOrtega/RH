import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeRep

/- English proof (translation)
Introduce `_ hConc hBasic hOp S R _ _ I J ρ X n x a hRep`. Take `⟨α, hα, hmk⟩` from `(hConc S I X n a).2.1 x hRep`. Establish `hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0`. Rewrite using `[ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]`. Take `⟨β, hβ⟩` from `(hConc R J X n (ρ.app X n a)).1 hcl`.

Establish `himg : ρ.IsImage α.1 β.1`. Introduce `p s h U y`. Consider the cases of `p with`. Consider the case `zero`. Establish `hs : n = s` using `by omega`.

Substitute `hs` using the available equality. Rewrite using `[hβ.1 U y, hα.1 U y]`. Conclude with `ρ.nat y n a`. Consider the case `succ p`. Rewrite using `[hβ.2 p s h U y, hα.2 p s h U y, map_zero]`.

Use `⟨β, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hOp S R I J ρ (sch.obj X) n α β himg, hmk]`. Rewrite using `[hβ.1 X (𝟙 X)]`. Express the relevant statement in the definitionally equal form `((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a`. Rewrite using `[CategoryTheory.Functor.map_id]`.

Both sides reduce to the same expression.
-/
theorem repOp : CrystallineSemistableComparison.E.EvNat → CrystallineSemistableComparison.E.RepConc → CrystallineSemistableComparison.E.RepBasic → CrystallineSemistableComparison.E.RepOp := by
  intro _ hConc hBasic hOp S R _ _ I J ρ X n x a hRep
  obtain ⟨α, hα, hmk⟩ := (hConc S I X n a).2.1 x hRep
  have hcl : Sec.map (J.d n (n + 1)) (ρ.app X n a) = 0 := by
    rw [ρ.comm X n (n + 1) a, (hBasic S I X n).2.1 x a hRep (n + 1), map_zero]
  obtain ⟨β, hβ⟩ := (hConc R J X n (ρ.app X n a)).1 hcl
  have himg : ρ.IsImage α.1 β.1 := by
    intro p s h U y
    cases p with
    | zero =>
      have hs : n = s := by omega
      subst hs
      rw [hβ.1 U y, hα.1 U y]
      exact ρ.nat y n a
    | succ p =>
      rw [hβ.2 p s h U y, hα.2 p s h U y, map_zero]
  refine ⟨β, ?_, ?_⟩
  · rw [← hOp S R I J ρ (sch.obj X) n α β himg, hmk]
  · rw [hβ.1 X (𝟙 X)]
    change ((J.X n).obj.map (𝟙 (op X))).hom (ρ.app X n a) = ρ.app X n a
    rw [CategoryTheory.Functor.map_id]
    rfl

end GlobalTheory.CompanionTheory.EdgeRep
