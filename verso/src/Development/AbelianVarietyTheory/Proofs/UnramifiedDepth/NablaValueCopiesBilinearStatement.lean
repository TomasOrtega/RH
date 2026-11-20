import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NablaValueCopiesBilinear
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FNablaValueCopiesBilinear.lean&line=95#L95)
-/
theorem _root_.GlobalTheory.T.nablaValueCopies_bilinear : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  first | exact @GlobalTheory.nabValN_bilinear | exact GlobalTheory.nabValN_bilinear | (intros; apply GlobalTheory.nabValN_bilinear <;> assumption)
