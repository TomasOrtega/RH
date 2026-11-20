import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl

open MvPolynomial Formalism.DegreeFormula GlobalTheory.FlagPoly

namespace GlobalTheory.FlagPoly

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

/- English proof (translation)
Unfold `pSum`. Rewrite using `[map_sum]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[Finset.sum_eq_single i]`.

Rewrite using `[Derivation.leibniz_pow, pderiv_X_self]`. Simplify using `[nsmul_eq_mul]`. Introduce `b _ hb`. Rewrite using `[Derivation.leibniz_pow, pderiv_X_of_ne (by simp [hb])]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[Derivation.leibniz_pow, pderiv_X_of_ne (by simp [Ne.symm h])]`. Simplify using the standard rewrite rules.
-/
theorem pderiv_pSum_single (τ σ : ι) (i : Fin N) (k : ℕ) :
    pderiv (τ, i) (pSum σ k : Pol ι N) =
      if τ = σ then C (k : ℝ) * X (τ, i) ^ (k - 1) else 0 := by
  unfold pSum
  rw [map_sum]
  split_ifs with h
  · subst h
    rw [Finset.sum_eq_single i]
    · rw [Derivation.leibniz_pow, pderiv_X_self]
      simp [nsmul_eq_mul]
    · intro b _ hb
      rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp [hb])]
      simp
    · simp
  · apply Finset.sum_eq_zero
    intro b _
    rw [Derivation.leibniz_pow, pderiv_X_of_ne (by simp [Ne.symm h])]
    simp

/- English proof (translation)
Establish `h1 : (∑ i ∈ s, pderiv (τ, i) (pSum σ k * Q)) = (∑ i ∈ s, pderiv (τ, i) (pSum σ k : Pol ι N)) * Q + pSum σ k * ∑ i ∈ s, pderiv (τ, i) Q`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz]`. Simplify using `only [smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : degFl ι N (pSum σ k * ∑ i ∈ s, pderiv (τ, i) Q) = 0` using `degreePowerSumMulEqZero ι N σ k _ hk`. Rewrite using `[h1, PPowSum.degFl_add, h2, add_zero]`. Simplify using `only [pderiv_pSum_single]`. Use `split_ifs with h`.

Rewrite using `[← Finset.mul_sum, mul_assoc, PPowSum.degFl_C_mul]`. Simplify using `[PPowSum.degFl_zero]`.
-/
theorem degFl_sum_pderiv_pSum_mul (s : Finset (Fin N)) (k : ℕ) (Q : Pol ι N) (τ σ : ι)
    (hk : 1 ≤ k) :
    degFl ι N (∑ i ∈ s, pderiv (τ, i) (pSum σ k * Q)) =
      if τ = σ then (k : ℝ) * degFl ι N ((∑ i ∈ s, X (τ, i) ^ (k - 1)) * Q) else 0 := by
  have h1 : (∑ i ∈ s, pderiv (τ, i) (pSum σ k * Q)) =
      (∑ i ∈ s, pderiv (τ, i) (pSum σ k : Pol ι N)) * Q +
        pSum σ k * ∑ i ∈ s, pderiv (τ, i) Q := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have h2 : degFl ι N (pSum σ k * ∑ i ∈ s, pderiv (τ, i) Q) = 0 :=
    degreePowerSumMulEqZero ι N σ k _ hk
  rw [h1, PPowSum.degFl_add, h2, add_zero]
  simp only [pderiv_pSum_single]
  split_ifs with h
  · rw [← Finset.mul_sum, mul_assoc, PPowSum.degFl_C_mul]
  · simp [PPowSum.degFl_zero]

/- English proof (translation)
Introduce `ι _ _ N j k Q τ σ hk`. Use `⟨degFl_sum_pderiv_pSum_mul _ k Q τ σ hk, ?_⟩` and prove the remaining obligations. Unfold `totF`. Rewrite using `[degFl_sum_pderiv_pSum_mul _ k Q τ σ hk]`. Distinguish the cases in `h : τ = σ`.

Distinguish the cases in `h1 : k = 1`. Substitute `h1` using the available equality. Rewrite using `[if_pos h, if_pos ⟨h, rfl⟩]`. Establish `: (∑ i : Fin N, (X (τ, i) : Pol ι N) ^ (1 - 1)) = C (N : ℝ)` using `by simp`. Rewrite using `[this, PPowSum.degFl_C_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[if_pos h, if_neg (fun hh => h1 hh.2), degreePowerSumMulEqZero ι N τ (k - 1) Q (by omega), mul_zero]`. Rewrite using `[if_neg h, if_neg (fun hh => h hh.1)]`.
-/
theorem shF_totF_pSum_mul : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (j k : ℕ) (Q : Pol ι N) (τ σ : ι), 1 ≤ k → shF j τ (pSum σ k * Q) = (if τ = σ then (k : ℝ) * degFl ι N (pLow j τ (k - 1) * Q) else 0) ∧ totF τ (pSum σ k * Q) = (if τ = σ ∧ k = 1 then (N : ℝ) * degFl ι N Q else 0) := by
  intro ι _ _ N j k Q τ σ hk
  refine ⟨degFl_sum_pderiv_pSum_mul _ k Q τ σ hk, ?_⟩
  unfold totF
  rw [degFl_sum_pderiv_pSum_mul _ k Q τ σ hk]
  by_cases h : τ = σ
  · by_cases h1 : k = 1
    · subst h1
      rw [if_pos h, if_pos ⟨h, rfl⟩]
      have : (∑ i : Fin N, (X (τ, i) : Pol ι N) ^ (1 - 1)) = C (N : ℝ) := by simp
      rw [this, PPowSum.degFl_C_mul]
      simp
    · rw [if_pos h, if_neg (fun hh => h1 hh.2),
        degreePowerSumMulEqZero ι N τ (k - 1) Q (by omega), mul_zero]
  · rw [if_neg h, if_neg (fun hh => h hh.1)]

end GlobalTheory.FlagPoly
