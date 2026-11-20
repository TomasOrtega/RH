import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

namespace GlobalTheory

/- English proof (translation)
Use `set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef`. Establish `hσ : GlobalTheory.IsSiegel σ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])`. Establish `: σ.map Complex.im = τ.map Complex.im + 1`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[σ, Matrix.one_apply]`. Simplify using `[σ, Matrix.one_apply, hij]`.

Rewrite using `[this]`. Conclude with `hτ.2.add_posSemidef Matrix.PosSemidef.one`. Establish `hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))) = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ))))`. Introduce `x`. Rewrite using `[← Complex.exp_conj, mul_assoc, ← Complex.exp_add]`.

Use `congr 2`. Establish `e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))`. Simplify using `[dotProduct]`. Rewrite using `[e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]`. Simplify using `only [map_mul, map_neg, conj_ofReal, smul_eq_mul]`.

Establish `: conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))`. Simplify using `[dotProduct, map_sum]`. Rewrite using `[this]`. Put the polynomial expressions in normal form. Simplify using `[I_sq]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdet : (1 - I • τ) = -I • σ`. Rewrite using `[hσdef, smul_add, smul_smul]`. Simplify using `[neg_smul, sub_eq_add_neg, add_comm]`. Repeatedly rewrite using `[hint]`.

Rewrite using `[integral_const_mul, hdet, mul_pow, mul_assoc]`. Use `hσ.siegelGaussIntegral_sq_mul_det` as an intermediate fact. Rewrite `this` using `[siegelGaussIntegral]`. Rewrite using `[this, mul_one]`.
-/
theorem siegelGauss_pair_standard (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ) (hτ : GlobalTheory.IsSiegel τ) :
    (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  set σ : Matrix l l ℂ := τ + I • (1 : Matrix l l ℂ) with hσdef
  have hσ : GlobalTheory.IsSiegel σ := by
    refine ⟨?_, ?_⟩
    · exact hτ.1.add (by simp [Matrix.IsSymm, Matrix.transpose_smul])
    · have : σ.map Complex.im = τ.map Complex.im + 1 := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [σ, Matrix.one_apply]
        · simp [σ, Matrix.one_apply, hij]
      rw [this]
      exact hτ.2.add_posSemidef Matrix.PosSemidef.one
  have hint : ∀ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))
      = c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (σ *ᵥ fun i => (x i : ℂ)))) := by
    intro x
    rw [← Complex.exp_conj, mul_assoc, ← Complex.exp_add]
    congr 2
    have e : ((x ⬝ᵥ x : ℝ) : ℂ) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct]
    rw [e, hσdef, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [map_mul, map_neg, conj_ofReal, smul_eq_mul]
    have : conj ((fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ))) = (fun i => (x i : ℂ)) ⬝ᵥ (fun i => (x i : ℂ)) := by
      simp [dotProduct, map_sum]
    rw [this]
    ring_nf
    simp [I_sq]
    ring
  have hdet : (1 - I • τ) = -I • σ := by
    rw [hσdef, smul_add, smul_smul]
    simp [neg_smul, sub_eq_add_neg, add_comm]
  simp_rw [hint]
  rw [integral_const_mul, hdet, mul_pow, mul_assoc]
  have := hσ.siegelGaussIntegral_sq_mul_det
  rw [siegelGaussIntegral] at this
  rw [this, mul_one]

end GlobalTheory
