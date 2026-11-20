import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPreirreducibleSpaceFibreHypersurfaceSpectrumIff.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff : ∀ (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔ IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  first | exact @GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | exact GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | (intros; apply GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff <;> assumption)
