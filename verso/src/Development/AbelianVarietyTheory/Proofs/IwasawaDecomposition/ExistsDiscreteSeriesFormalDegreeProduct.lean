import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePosStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFdegSmulOfIsDS
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

/- English proof (translation)
Take `⟨hd, h⟩` from `h`. Establish `h2` using `(h w w w w).2`. Establish `e1 : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g)) = fun g => (((‖coefOn σ w w g‖ ^ 2 : ℝ)) : ℂ)`. Use function extensionality and compare the values at `g`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Rewrite `h2` using `[e1, integral_complex_ofReal, inner_self_eq_norm_sq_to_K]`. Establish `h3 : ∫ g : Formalism.REAL.UJ ε, ‖coefOn σ w w g‖ ^ 2 ∂μ = ‖w‖ ^ 4 / d`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[h2]`. Use `push_cast`.

Simplify using `only [RCLike.ofReal, Complex.coe_algebraMap]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : 0 < ‖w‖` using `norm_pos_iff.mpr hw`. Unfold `fdegOf`. Rewrite using `[h3]`.

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
Introduce `hE hF cd R P`. Establish `hpar` using `(GlobalTheory.T.rowHCParameter_isHCParam_and_formalDegree_pos R P).1`. Establish `key : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin (2 * R.rS + R.k + 1)) (Fin (2 * R.rS + R.k + 1)) ℂ → (H →L[ℂ] H)) (d : ℝ), IsDS (epsSH R) (lamSH R P) σ → IsFdeg ((trueScale cd _ (epsSH R) : ENNReal) • Formalism.REAL.muG (epsSH R)) σ d → d = true …`. Introduce `H _ _ σ d hσ hd`. Establish `: Nontrivial H` using `hσ.2.1`.

Take `⟨w, hw⟩` from `exists_ne (0 : H)`. Rewrite using `[← fdegOf_eq_of_isFdeg _ σ d hd w hw]`. Conclude with `hF cd (trueScale cd) (GlobalTheory.T.cdScaleIs_trueScale' cd) _ (epsSH R) (lamSH R P) hpar H σ w hσ hw`. Use `⟨?_, key⟩` and prove the remaining obligations. Take `⟨H, i1, i2, σ, hσ⟩` from `hE _ (epsSH R) (lamSH R P) hpar`.

Take `⟨d, hd⟩` from `exists_isFdeg_smul_of_isDS _ (epsSH R) (lamSH R P) H σ hσ _ (trueScale_pos cd _ (epsSH R))`. Use `⟨H, i1, i2, σ, hσ, ?_⟩` and prove the remaining obligations. Rewrite using `[← key H σ d hσ hd]`. Conclude with `hd`.
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
