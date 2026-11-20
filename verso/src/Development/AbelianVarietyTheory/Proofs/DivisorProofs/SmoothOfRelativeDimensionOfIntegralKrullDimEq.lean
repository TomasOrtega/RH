import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.RelDimOfDim

/- English proof (translation)
Introduce `F _ X _ q n hq hn`. Establish `x₀ : X` using `Classical.arbitrary X`. Take `⟨d, hd⟩` from `exists_dim_of_preconnected q x₀`. Establish `h` using `GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q d hd`. Rewrite `h` using `[hn]`.

Establish `hdn : d = n` using `by exact_mod_cast h.symm`. Conclude with `hdn ▸ hd`.
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
