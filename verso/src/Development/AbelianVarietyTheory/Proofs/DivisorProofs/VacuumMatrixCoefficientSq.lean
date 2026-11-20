import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussianStatement
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

/- English proof (translation)
Introduce `l _ _ s P Q hP hQ hdet hS c hc`. Use `set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))`. Use `set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))`. Establish `h1` using `GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS`. Establish `hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ)))`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.IsSymm]`. Establish `: ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1`. Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]`. Rewrite using `[this]`.

Conclude with `Matrix.PosDef.one`. Establish `h2` using `GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI`. Establish `hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J`. Use `congr 1`. Use extensionality with `x`.

Use `congr 2`. Rewrite using `[one_mul]`. Use `congr 1`. Rewrite using `[Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]`. Simplify using `only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]`.

Rewrite using `[← mul_assoc, mul_assoc _ I I, I_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[hJ]`. Establish `hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l`. Establish `: (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ)`.

Apply the tactic sequence `rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num`. Rewrite using `[this, det_smul, det_one, mul_one]`. Rewrite `h2` using `[hdet2, one_pow]`. Establish `hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s`. Establish `hu : IsUnit P.det` using `isUnit_iff_ne_zero.mpr hdet`.

Rewrite using `[sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]`. Use extensionality with `i j`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]`. Use `push_cast`. Put the polynomial expressions in normal form.

Rewrite using `[I_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1`. Rewrite using `[← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]`. Establish `h2ne : (2:ℂ) ^ Fintype.card l ≠ 0` using `pow_ne_zero _ two_ne_zero`.

Apply `mul_left_cancel₀ h2ne` to reduce the goal to its premises. Take the linear combination `h3 - h2`.
-/
theorem GlobalTheory.vacuum_coef_sq : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → P.det ≠ 0 → GlobalTheory.IsSiegel (-(Q * P⁻¹)) → ∀ c : ℂ, c ^ 2 * P.det = 1 → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (GlobalTheory.Published.Metaplectic.holPart s).det = (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 := by
  intro l _ _ s P Q hP hQ hdet hS c hc
  set K := (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (-(Q * P⁻¹)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  set J := (∫ x : l → ℝ, cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ))))
  have h1 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (-(Q * P⁻¹)) c hS
  have hSI : GlobalTheory.IsSiegel ((I • (1 : Matrix l l ℂ))) := by
    refine ⟨?_, ?_⟩
    · simp [Matrix.IsSymm]
    · have : ((I • (1 : Matrix l l ℂ)).map Complex.im) = 1 := by
        ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]
      rw [this]; exact Matrix.PosDef.one
  have h2 := GlobalTheory.T.siegelGaussian_pair_standardGaussian l (I • (1 : Matrix l l ℂ)) 1 hSI
  have hJ : (∫ x : l → ℝ, (1:ℂ) * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ (I • (1 : Matrix l l ℂ)) *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) = J := by
    congr 1; ext x
    congr 2
    rw [one_mul]; congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
    simp only [dotProduct, smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [← mul_assoc, mul_assoc _ I I, I_mul_I]; ring
  rw [hJ] at h2
  have hdet2 : (1 - I • (I • (1 : Matrix l l ℂ))).det = 2 ^ Fintype.card l := by
    have : (1 - I • (I • (1 : Matrix l l ℂ))) = (2:ℂ) • (1 : Matrix l l ℂ) := by
      rw [smul_smul, I_mul_I]; ext i j; by_cases h : i = j <;> simp [h, Matrix.one_apply]; norm_num
    rw [this, det_smul, det_one, mul_one]
  rw [hdet2, one_pow] at h2
  have hprod : (1 - I • (-(Q * P⁻¹))) * P = (2:ℂ) • GlobalTheory.Published.Metaplectic.holPart s := by
    have hu : IsUnit P.det := isUnit_iff_ne_zero.mpr hdet
    rw [sub_mul, one_mul, smul_mul_assoc, neg_mul, Matrix.mul_assoc, nonsing_inv_mul _ hu, mul_one]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul, hP, hQ, GlobalTheory.Published.Metaplectic.holPart]
    push_cast
    ring_nf; rw [I_sq]; ring
  have h3 : K ^ 2 * ((2:ℂ) ^ Fintype.card l * (GlobalTheory.Published.Metaplectic.holPart s).det) = 1 := by
    rw [← det_smul, ← hprod, det_mul, ← mul_assoc, h1, hc]
  have h2ne : (2:ℂ) ^ Fintype.card l ≠ 0 := pow_ne_zero _ two_ne_zero
  apply mul_left_cancel₀ h2ne
  linear_combination h3 - h2
