import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

noncomputable section
open MvPolynomial

namespace GlobalTheory.CompactHowe

/- English proof (translation)
Rewrite using `[substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]`. Take `⟨a, b⟩` from `p`. Distinguish the cases in `h : a = τ₀`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Introduce `l _ hl`. Apply the tactic sequence `by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]`. Simplify using the standard rewrite rules. Introduce `k _ hk`.

Simplify using `[Matrix.one_apply_ne hk]`. Simplify using the standard rewrite rules.
-/
theorem substF_scalar_X {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (p : ι × Fin N × Fin n) :
    substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (X p)
      = C (if p.1 = τ₀ then ζ else 1) * X p := by
  rw [substF_X, Finset.sum_eq_single p.2.1, Finset.sum_eq_single p.2.2]
  · obtain ⟨a, b⟩ := p
    by_cases h : a = τ₀
    · subst h; simp
    · simp [h]
  · intro l _ hl
    by_cases h : p.1 = τ₀ <;> simp [h, Matrix.one_apply_ne hl]
  · simp
  · intro k _ hk
    simp [Matrix.one_apply_ne hk]
  · simp

/- English proof (translation)
Unfold `Finsupp.mapDomain`. Rewrite using `[Finsupp.sum_apply]`. Unfold `Finsupp.sum`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Finsupp.single_apply]`.
-/
theorem mapDomain_fst_apply {ι : Type} [DecidableEq ι] {N n : ℕ} (k : ι × Fin N × Fin n →₀ ℕ) (τ₀ : ι) :
    Finsupp.mapDomain Prod.fst k τ₀ = ∑ p ∈ k.support, if p.1 = τ₀ then k p else 0 := by
  unfold Finsupp.mapDomain
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun p _ => ?_
  dsimp only
  rw [Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]`. Simplify using `only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]`. Rewrite using `[mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← map_pow]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem substF_scalar_monomial {ι : Type} [DecidableEq ι] {N n : ℕ} (τ₀ : ι) (ζ : ℂ) (k : ι × Fin N × Fin n →₀ ℕ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) (fun τ => if τ = τ₀ then ζ • (1 : Matrix (Fin n) (Fin n) ℂ) else 1) (MvPolynomial.monomial k 1) = ζ ^ (Finsupp.mapDomain Prod.fst k τ₀) • MvPolynomial.monomial k 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, substF_scalar_X, mul_pow, Finset.prod_mul_distrib]
  rw [mapDomain_fst_apply, smul_eq_C_mul, ← Finset.prod_pow_eq_pow_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← map_pow]
  split_ifs <;> simp

end GlobalTheory.CompactHowe
