import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Set `Γ : Finset (τ →₀ ℕ)` to `P.support.biUnion (fun m => (coeff m P).support)`. Set `Q : (τ →₀ ℕ) → MvPolynomial σ k` to `fun γ => ∑ m ∈ P.support, monomial m (coeff γ (coeff m P))`. Establish `hQ : ∀ γ m, coeff m (Q γ) = coeff γ (coeff m P)`. Introduce `γ m`. Simplify using `only [Q, coeff_sum, coeff_monomial]`.

Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, coeff_zero]`. Establish `hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)`.

Use extensionality with `m : 1`. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]`. Establish `: ∀ γ, (monomial γ (1 : k) : MvPolynomial τ k) * C (coeff γ (coeff m P)) = monomial γ (coeff γ (coeff m P))`. Introduce `γ`.

Rewrite using `[mul_comm, C_mul_monomial, mul_one]`. Simplify using `only [this]`. Distinguish the cases in `hm : m ∈ P.support`. Use `conv_lhs => rw [as_sum (coeff m P)]`. Apply `Finset.sum_subset` to reduce the goal to its premises.

Introduce `γ hγ`. Conclude with `Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩`. Introduce `γ _ hγ`. Rewrite using `[notMem_support_iff.mp hγ, monomial_zero]`. Rewrite using `[notMem_support_iff.mp hm]`.

Simplify using `only [coeff_zero, monomial_zero, Finset.sum_const_zero]`. Establish `hevid : ∀ y : τ → k, (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k`. Introduce `y`. Use extensionality with `c`. Simplify using `only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]`.

Establish `hevP : ∀ y : τ → k, map (eval y) P = ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ`. Introduce `y`. Use `conv_lhs => rw [hdec]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun γ _ => ?_)` and prove the remaining obligations.

Rewrite using `[smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]`. Establish `hQM : ∀ γ ∈ Γ, Q γ ∈ M`. Introduce `β hβ`. Assume the negation of the conclusion as `hnot`. Take `⟨L, hLβ, hLM⟩` from `Submodule.exists_le_ker_of_notMem hnot`.

Set `R : MvPolynomial τ k` to `∑ γ ∈ Γ, monomial γ (L (Q γ))`. Establish `hR : ∀ y : τ → k, eval y R = L (map (eval y) P)`. Introduce `y`. Rewrite using `[hevP, map_sum, map_sum]`. Use `Finset.sum_congr rfl (fun γ _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]`. Establish `hRD : R * D = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `y`. Rewrite using `[map_mul, map_zero]`.

Distinguish the cases in `hy : eval y D = 0`. Rewrite using `[hy, mul_zero]`. Rewrite using `[hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]`. Establish `hR0 : R = 0` using `(mul_eq_zero.mp hRD).resolve_right hD`. Establish `hcoef : coeff β R = L (Q β)`.

Simplify using `only [R, coeff_sum, coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq', if_pos hβ]`. Conclude with `hLβ (by rw [← hcoef, hR0, coeff_zero])`. It suffices to establish `h : (∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)) ∈ Submodule.span (MvPolynomial τ k) (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) by`. Rewrite `h` using `[← hdec]`. Then use the resulting hypothesis.

Use `Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))` and prove the remaining obligations. Conclude with `⟨Q γ, hQM γ hγ, rfl⟩`.
-/
theorem mem_span_map_of_eval_mem (k : Type) [Field k] [Infinite k] (σ τ : Type)
    (M : Submodule k (MvPolynomial σ k)) (D : MvPolynomial τ k) (hD : D ≠ 0)
    (P : MvPolynomial σ (MvPolynomial τ k))
    (hP : ∀ y : τ → k, MvPolynomial.eval y D ≠ 0 → MvPolynomial.map (MvPolynomial.eval y) P ∈ M) :
    P ∈ Submodule.span (MvPolynomial τ k)
      (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) := by
  classical
  let Γ : Finset (τ →₀ ℕ) := P.support.biUnion (fun m => (coeff m P).support)
  let Q : (τ →₀ ℕ) → MvPolynomial σ k := fun γ =>
    ∑ m ∈ P.support, monomial m (coeff γ (coeff m P))
  have hQ : ∀ γ m, coeff m (Q γ) = coeff γ (coeff m P) := by
    intro γ m
    simp only [Q, coeff_sum, coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [notMem_support_iff.mp h, coeff_zero]
  have hdec : P = ∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ) := by
    ext m : 1
    rw [coeff_sum]
    simp only [coeff_smul, coeff_map, hQ, smul_eq_mul, MvPolynomial.algebraMap_eq]
    have : ∀ γ, (monomial γ (1 : k) : MvPolynomial τ k) * C (coeff γ (coeff m P)) = monomial γ (coeff γ (coeff m P)) := by
      intro γ; rw [mul_comm, C_mul_monomial, mul_one]
    simp only [this]
    by_cases hm : m ∈ P.support
    · conv_lhs => rw [as_sum (coeff m P)]
      apply Finset.sum_subset
      · intro γ hγ; exact Finset.mem_biUnion.mpr ⟨m, hm, hγ⟩
      · intro γ _ hγ; rw [notMem_support_iff.mp hγ, monomial_zero]
    · rw [notMem_support_iff.mp hm]
      simp only [coeff_zero, monomial_zero, Finset.sum_const_zero]
  have hevid : ∀ y : τ → k, (eval y).comp (algebraMap k (MvPolynomial τ k)) = RingHom.id k := by
    intro y; ext c; simp only [RingHom.comp_apply, MvPolynomial.algebraMap_eq, eval_C, RingHom.id_apply]
  have hevP : ∀ y : τ → k, map (eval y) P =
      ∑ γ ∈ Γ, (eval y (monomial γ (1 : k) : MvPolynomial τ k)) • Q γ := by
    intro y
    conv_lhs => rw [hdec]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun γ _ => ?_)
    rw [smul_eq_C_mul, map_mul, map_C, map_map, hevid, map_id, smul_eq_C_mul]
  have hQM : ∀ γ ∈ Γ, Q γ ∈ M := by
    intro β hβ
    by_contra hnot
    obtain ⟨L, hLβ, hLM⟩ := Submodule.exists_le_ker_of_notMem hnot
    let R : MvPolynomial τ k := ∑ γ ∈ Γ, monomial γ (L (Q γ))
    have hR : ∀ y : τ → k, eval y R = L (map (eval y) P) := by
      intro y
      rw [hevP, map_sum, map_sum]
      refine Finset.sum_congr rfl (fun γ _ => ?_)
      rw [map_smul, smul_eq_mul, eval_monomial, eval_monomial, mul_comm, one_mul]
    have hRD : R * D = 0 := by
      apply MvPolynomial.funext
      intro y
      rw [map_mul, map_zero]
      by_cases hy : eval y D = 0
      · rw [hy, mul_zero]
      · rw [hR, LinearMap.mem_ker.mp (hLM (hP y hy)), zero_mul]
    have hR0 : R = 0 := (mul_eq_zero.mp hRD).resolve_right hD
    have hcoef : coeff β R = L (Q β) := by
      simp only [R, coeff_sum, coeff_monomial]
      rw [Finset.sum_ite_eq', if_pos hβ]
    exact hLβ (by rw [← hcoef, hR0, coeff_zero])
  suffices h : (∑ γ ∈ Γ, (monomial γ (1 : k) : MvPolynomial τ k) • map (algebraMap k (MvPolynomial τ k)) (Q γ)) ∈
      Submodule.span (MvPolynomial τ k)
        (MvPolynomial.map (algebraMap k (MvPolynomial τ k)) '' (M : Set (MvPolynomial σ k))) by
    rwa [← hdec] at h
  refine Submodule.sum_mem _ (fun γ hγ => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
  exact ⟨Q γ, hQM γ hγ, rfl⟩

end GlobalTheory
