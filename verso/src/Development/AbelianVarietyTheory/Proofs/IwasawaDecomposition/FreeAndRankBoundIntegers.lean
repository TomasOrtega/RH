import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.ZRank

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem finrank_int_eq_mul (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

end GlobalTheory.ZRank

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem GlobalTheory.ZRank.free_int_and_finrank_le : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X]
    [Module.Finite (NumberField.RingOfIntegers E) X] [Module.Projective (NumberField.RingOfIntegers E) X],
    Module.Free ℤ X ∧ Module.finrank ℤ X ≤ Module.finrank ℚ E * Module.finrank (NumberField.RingOfIntegers E) X := by
  intro E _ _ X _ _ _ _
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
    obtain ⟨h, hh⟩ := Module.projective_lifting_property r LinearMap.id hr
    exact Module.Projective.of_split (h.restrictScalars ℤ) (r.restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hh x)
  exact ⟨inferInstance, (GlobalTheory.ZRank.finrank_int_eq_mul E X).le⟩
