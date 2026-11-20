import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FinrankOfIsStandardSmoothOfRelativeDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem locally_standardSmooth_sec (A : Over (Sp ℂ)) (g : ℕ) (h : SmoothOfRelativeDimension g A.hom) (U : A.left.affineOpens) :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension g) (algebraMap ℂ (Sec (str A) U.1)) := by
  have h' : SmoothOfRelativeDimension g (str A) := by
    simpa [str] using h
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (str A) h' ⟨⊤, isAffineOpen_top _⟩ U le_top
  have hr := RingHom.locally_respectsIso (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := g))
  exact hr.2 _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv h1

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem kaehler_sec_finite_projective_rank : ∀ (A : Over (Sp ℂ)) (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ U : A.left.affineOpens, Module.Finite (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ Module.Projective (Sec (str A) U.1) Ω[Sec (str A) U.1⁄ℂ] ∧ ∀ p : PrimeSpectrum (Sec (str A) U.1), Module.rankAtStalk Ω[Sec (str A) U.1⁄ℂ] p = g := by
  intro A g h U
  have hl := locally_standardSmooth_sec A g h U
  haveI := GlobalTheory.AugCot.smooth_of_locally hl
  exact ⟨inferInstance, inferInstance, GlobalTheory.AugCot.rankAtStalk_kaehler_of_locally hl⟩

end GlobalTheory.CechPer
