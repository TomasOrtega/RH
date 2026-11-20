import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePosStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts.
-/
theorem fdegOf_eq_of_isFdeg {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin n → Bool} (μ : Measure (Formalism.REAL.UJ ε)) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ)
    (h : IsFdeg μ σ d) (w : H) (hw : w ≠ 0) : fdegOf μ σ w = d := by
  obtain ⟨hd, h⟩ := h
  have h2 := (h w w w w).2
  have e1 : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g)) =
      fun g => (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ) := by
    funext g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e1, integral_complex_ofReal, inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    push_cast
    simp only [RCLike.ofReal, Complex.coe_algebraMap]
    ring
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  unfold fdegOf
  rw [h3]
  field_simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_isDS_isFdeg_trueDsig : DiscreteSeriesExist → FormalDegreeFormula₂ → ∀ (cd : CDHaar) (R : Ranks) (P : HCParam R), (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)), IsDS (epsSH R) (lamSH R P) σ ∧ IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ (trueDsig R P)) ∧ ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
  intro hE hF cd R P
  have hpar := (GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos R P).1
  have key : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = trueDsig R P := by
    intro H _ _ σ d hσ hd
    have : Nontrivial H := hσ.2.1
    obtain ⟨w, hw⟩ := exists_ne (0 : H)
    rw [← fdegOf_eq_of_isFdeg _ σ d hd w hw]
    exact hF cd (trueScale cd) (GlobalTheory.T.cdScaleIs_trueScale' cd) _ (epsSH R) (lamSH R P) hpar H σ w hσ hw
  refine ⟨?_, key⟩
  obtain ⟨H, i1, i2, σ, hσ⟩ := hE _ (epsSH R) (lamSH R P) hpar
  obtain ⟨d, hd⟩ := exists_isFdeg_smul_of_isDS _ (epsSH R) (lamSH R P) H σ hσ _ (trueScale_pos cd _ (epsSH R))
  refine ⟨H, i1, i2, σ, hσ, ?_⟩
  rw [← key H σ d hσ hd]
  exact hd

end GlobalTheory.Mem.Vol
