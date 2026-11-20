import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.RelDimOfDim

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem smoothOfRelativeDimension_of_topologicalKrullDim_eq :
    ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp F) (n : ℕ),
      Smooth q → topologicalKrullDim X = n → SmoothOfRelativeDimension n q := by
  intro F _ X _ q n hq hn
  have x₀ : X := Classical.arbitrary X
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected q x₀
  have h := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q d hd
  rw [hn] at h
  have hdn : d = n := by exact_mod_cast h.symm
  exact hdn ▸ hd

end GlobalTheory.RelDimOfDim
