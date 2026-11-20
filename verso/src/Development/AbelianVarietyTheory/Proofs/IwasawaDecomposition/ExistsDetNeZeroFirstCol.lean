import Mathlib

namespace GlobalTheory.FirstColumnConjugation

open Matrix

/- English proof (translation)
Take `⟨k₀, hk₀⟩` from `Function.ne_iff.1 hv`. Set `u : Fin (n + 1) → ℂ` to `v - Pi.single k₀ (1 : ℂ)`. Set `Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ` to `1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))`. Establish `hQdet : Q.det = v k₀`. Simplify using `only [Q]`.

Rewrite using `[det_one_add_replicateCol_mul_replicateRow]`. Simplify using `[u]`. Establish `hQcol : ∀ k, Q k k₀ = v k`. Introduce `k`. Simplify using `only [Q, u]`.

Apply the tactic sequence `by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]`. Use `⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[det_permute', hQdet]`. Conclude with `mul_ne_zero (by simp) hk₀`. Simplify using `[hQcol]`.
-/
theorem exists_det_ne_zero_first_col {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ ∀ k, P k 0 = v k := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hv
  let u : Fin (n + 1) → ℂ := v - Pi.single k₀ (1 : ℂ)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))
  have hQdet : Q.det = v k₀ := by
    simp only [Q]
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [u]
  have hQcol : ∀ k, Q k k₀ = v k := by
    intro k
    simp only [Q, u]
    by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]
  refine ⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩
  · rw [det_permute', hQdet]
    exact mul_ne_zero (by simp) hk₀
  · simp [hQcol]

/- English proof (translation)
Take `⟨μ, hμ⟩` from `Module.End.exists_eigenvalue (Matrix.toLin' A)`. Take `⟨v, hv⟩` from `hμ.exists_hasEigenvector`. Establish `hAv : A *ᵥ v = μ • v`. Establish `h` using `Module.End.mem_eigenspace_iff.1 hv.1`. Rewrite `h` using `[Matrix.toLin'_apply]`. Then use the resulting hypothesis.

Take `⟨P, hP, hPv⟩` from `exists_det_ne_zero_first_col v hv.2`. Establish `hu : IsUnit P` using `(Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)`. Use `⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩` and prove the remaining obligations. Establish `hPe : P *ᵥ Pi.single 0 1 = v`. Use extensionality with `k`.

Rewrite using `[mulVec_single_one]`. Conclude with `hPv k`. Establish `hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1`. Rewrite using `[← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]`. Establish `h` using `congrFun hcol (Fin.succ a)`.

Rewrite `h` using `[mulVec_single_one]`. Simplify `h` using `[Pi.single_apply, Fin.succ_ne_zero]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), Matrix.one_mul]`.
-/
theorem exists_conj_first_col_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      Matrix.det P ≠ 0 ∧ (∀ a : Fin n, B (Fin.succ a) 0 = 0) ∧ A * P = P * B := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at h
  obtain ⟨P, hP, hPv⟩ := exists_det_ne_zero_first_col v hv.2
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)
  refine ⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩
  · have hPe : P *ᵥ Pi.single 0 1 = v := by
      ext k
      rw [mulVec_single_one]
      exact hPv k
    have hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1 := by
      rw [← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]
    have h := congrFun hcol (Fin.succ a)
    rw [mulVec_single_one] at h
    simpa [Pi.single_apply, Fin.succ_ne_zero] using h
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu),
      Matrix.one_mul]

end GlobalTheory.FirstColumnConjugation
