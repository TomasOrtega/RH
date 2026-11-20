import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LidxBaseChange.lidx_ne_zero_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLatticeIndexNonzeroIffUnderFieldMap.lean&line=168#L168)
-/
theorem _root_.GlobalTheory.T.lattice_index_nonzero_iff_under_field_map : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  first | exact @GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | exact GlobalTheory.LidxBaseChange.lidx_ne_zero_iff | (intros; apply GlobalTheory.LidxBaseChange.lidx_ne_zero_iff <;> assumption)
