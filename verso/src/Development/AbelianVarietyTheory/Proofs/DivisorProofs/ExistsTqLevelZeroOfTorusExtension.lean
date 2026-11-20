import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtIsGtOfTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Raynaud

/- English proof (translation)
Introduce `R _ _ G _ _ hT`. Take `⟨E, ⟨d⟩⟩` from `exists_splitExt_isGt_of_torusExtension (ResidueField R) _ hT`. Use `E.free` as an intermediate fact. Use `E.finite` as an intermediate fact. Use `⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩` and prove the remaining obligations.

Take `⟨Q₁, -⟩` from `exists_tq_of_gtDatum _ E _ d`. Set `r : Sp (R ⧸ maximalIdeal R ^ (0 + 1)) ⟶ Sp (ResidueField R)` to `spMap (Ideal.Quotient.factor (show maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) by simp))`. Establish `hr : r ≫ spMap (residue R) = thick R (maximalIdeal R) 0`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.

Set `F : (thickObj R (maximalIdeal R) 0 G).left ⟶ ((Over.pullback (spMap (residue R))).obj G).left` to `pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)`. Take `⟨Q₀, -⟩` from `exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).congr hr.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)) Q₁`. Conclude with `⟨Q₀⟩`.
-/
theorem exists_tq_level_zero_of_torusExtension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) →
    ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X),
      Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) := by
  intro R _ _ G _ _ hT
  obtain ⟨E, ⟨d⟩⟩ := exists_splitExt_isGt_of_torusExtension (ResidueField R) _ hT
  have := E.free
  have := E.finite
  refine ⟨E.X, inferInstance, inferInstance, inferInstance, ?_⟩
  obtain ⟨Q₁, -⟩ := exists_tq_of_gtDatum _ E _ d
  let r : Sp (R ⧸ maximalIdeal R ^ (0 + 1)) ⟶ Sp (ResidueField R) :=
    spMap (Ideal.Quotient.factor (show maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) by simp))
  have hr : r ≫ spMap (residue R) = thick R (maximalIdeal R) 0 := by
    rw [← Spec.map_comp]
    rfl
  let F : (thickObj R (maximalIdeal R) 0 G).left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ r) (by rw [Category.assoc, hr]; exact pullback.condition)
  obtain ⟨Q₀, -⟩ := exists_tq_baseChange _ _ r E.X _ _ F ((isGrpPullback_pullback G _).cancel
    ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).congr hr.symm (pullback.lift_fst _ _ _).symm)
    (pullback.lift_snd _ _ _)) Q₁
  exact ⟨Q₀⟩

/- English proof (translation)
The claim follows from `exists_tq_level_zero_of_torusExtension`.
-/
example : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Nonempty (TorusExtension ((Over.pullback (spMap (residue R))).obj G)) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TQ (thickObj R (maximalIdeal R) 0 G) X) :=
  exists_tq_level_zero_of_torusExtension

end GlobalTheory.Raynaud

end
