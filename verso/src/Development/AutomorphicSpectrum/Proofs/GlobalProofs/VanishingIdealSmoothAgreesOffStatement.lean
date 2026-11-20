import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.VanishingIdealSmoothAgreesOff
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FVanishingIdealSmoothAgreesOff.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.vanishing_ideal_smooth_agrees_off : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (A : Closeds X) (O : X.Opens), Smooth (Z.subschemeι ≫ g) → (A : Set X) ⊆ Z.support → (O : Set X) = ((Z.support : Set X) \ A)ᶜ → Smooth ((Scheme.IdealSheafData.vanishingIdeal A).subschemeι ≫ g) ∧ (Scheme.IdealSheafData.vanishingIdeal A).comap O.ι = Z.comap O.ι := by
  first | exact @GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | exact GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq | (intros; apply GlobalTheory.CompanionTheory.SmoothPart.smooth_and_comap_eq <;> assumption)
