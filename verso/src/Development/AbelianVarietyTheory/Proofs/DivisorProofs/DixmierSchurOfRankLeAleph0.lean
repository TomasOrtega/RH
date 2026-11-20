import Mathlib

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hs : spectrum ℂ T = ∅`. Use extensionality with `c`. Simplify using `only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]`. Simplify using `using (h c).neg`. Distinguish the cases in `hd : 0 < q.degree`.

Establish `h1` using `spectrum.map_polynomial_aeval_of_degree_pos T q hd`. Rewrite `h1` using `[hs, Set.image_empty]`. Establish `h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q)` using `by rw [h1]; simp`. Conclude with `(spectrum.zero_notMem_iff ℂ).1 h0`. Establish `h2 : q = C (q.coeff 0)` using `eq_C_of_degree_le_zero (not_lt.1 hd)`.

Establish `h3 : q.coeff 0 ≠ 0` using `fun h => hq (by rw [h2, h, C_0])`. Rewrite using `[h2, aeval_C]`. Conclude with `(IsUnit.mk0 _ h3).map _`.
-/
theorem isUnit_aeval_of_forall_isUnit_sub {A : Type*} [Ring A] [Algebra ℂ A] (T : A)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ A c)) (q : ℂ[X]) (hq : q ≠ 0) :
    IsUnit (aeval T q) := by
  have hs : spectrum ℂ T = ∅ := by
    ext c
    simp only [Set.mem_empty_iff_false, iff_false, spectrum.notMem_iff]
    simpa using (h c).neg
  by_cases hd : 0 < q.degree
  · have h1 := spectrum.map_polynomial_aeval_of_degree_pos T q hd
    rw [hs, Set.image_empty] at h1
    have h0 : (0 : ℂ) ∉ spectrum ℂ (aeval T q) := by rw [h1]; simp
    exact (spectrum.zero_notMem_iff ℂ).1 h0
  · have h2 : q = C (q.coeff 0) := eq_C_of_degree_le_zero (not_lt.1 hd)
    have h3 : q.coeff 0 ≠ 0 := fun h => hq (by rw [h2, h, C_0])
    rw [h2, aeval_C]
    exact (IsUnit.mk0 _ h3).map _

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Use `set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef`. Establish `hq0 : aeval T q v = 0`. Establish `h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k)`.

Introduce `k hk`. Rewrite using `[← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X, aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul, map_smul]`. Rewrite using `[hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]`. Establish `hq : q = 0`. Assume the negation of the conclusion as `hne`.

Establish `hu` using `isUnit_aeval_of_forall_isUnit_sub T h q hne`. Establish `hinj` using `((Module.End.isUnit_iff _).1 hu).1`. Conclude with `hv (hinj (by rw [hq0, map_zero]))`. Establish `h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j)`. Rewrite using `[hqdef, eval_finset_sum, Finset.sum_eq_single i]`.

Simplify using `[eval_prod]`. Introduce `k _ hki`. Rewrite using `[eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩) (by simp), mul_zero]`. Introduce `h`. Conclude with `absurd hi h`.

Rewrite `h2` using `[hq, eval_zero]`. Use `(mul_eq_zero.1 h2.symm).resolve_right ?_` and prove the remaining obligations. Conclude with `Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm`.
-/
theorem linearIndependent_of_sub_apply_eq {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : Module.End ℂ V) (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c))
    (v : V) (hv : v ≠ 0) (w : ℂ → V)
    (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i hi
  set q : ℂ[X] := ∑ k ∈ s, C (g k) * ∏ j ∈ s.erase k, (X - C j) with hqdef
  have hq0 : aeval T q v = 0 := by
    have h1 : ∀ k ∈ s, aeval T (C (g k) * ∏ j ∈ s.erase k, (X - C j)) v
        = aeval T (∏ j ∈ s, (X - C j : ℂ[X])) (g k • w k) := by
      intro k hk
      rw [← Finset.prod_erase_mul s _ hk, ← hw k, map_mul, map_mul, aeval_C, map_sub, aeval_X,
        aeval_C, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
        map_smul, map_smul]
    rw [hqdef, map_sum, LinearMap.sum_apply, Finset.sum_congr rfl h1, ← map_sum, hg, map_zero]
  have hq : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval_of_forall_isUnit_sub T h q hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [hq0, map_zero]))
  have h2 : eval i q = g i * ∏ j ∈ s.erase i, (i - j) := by
    rw [hqdef, eval_finset_sum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro k _ hki
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hki.symm, hi⟩)
        (by simp), mul_zero]
    · intro h; exact absurd hi h
  rw [hq, eval_zero] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun j hj => sub_ne_zero.2 (Finset.mem_erase.1 hj).1.symm

/- English proof (translation)
Introduce `V ι _ _ ρ T hV hrank hirr hcomm`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Establish `hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)`. Introduce `c`.

Use `set S := T - algebraMap ℂ (Module.End ℂ V) c with hS`. Establish `hS0 : S ≠ 0`. Introduce `h0`. Apply `hne c` to reduce the goal to its premises. Rewrite using `[← Algebra.algebraMap_eq_smul_one]`.

Conclude with `sub_eq_zero.1 h0`. Establish `hSc : ∀ i x, S (ρ i x) = ρ i (S x)`. Introduce `i x`. Use `LinearMap.congr_fun (hcomm i) x` as an intermediate fact. Simplify using `only [Module.End.mul_apply] at this`.

Simplify using `[hS, this, Module.algebraMap_end_apply]`. Rewrite using `[Module.End.isUnit_iff]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← LinearMap.ker_eq_bot]`. Use `(hirr _ ?_).resolve_right ?_` and prove the remaining obligations.

Introduce `i x hx`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Rewrite using `[hSc, hx, map_zero]`. Rewrite using `[LinearMap.ker_eq_top]`. Conclude with `hS0`.

Rewrite using `[← LinearMap.range_eq_top]`. Use `(hirr _ ?_).resolve_left ?_` and prove the remaining obligations. Introduce and unpack `i _ ⟨x, rfl⟩`. Conclude with `⟨ρ i x, hSc i x⟩`. Rewrite using `[LinearMap.range_eq_bot]`.

Conclude with `hS0`. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Use `choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v`. Establish `hli` using `linearIndependent_of_sub_apply_eq T hunit v hv w hw`. Establish `h1` using `hli.cardinal_le_rank.trans hrank`.

Rewrite `h1` using `[Cardinal.mk_complex]`. Conclude with `absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)`.
-/
theorem dixmier_schur_of_rank_le_aleph0 :
    ∀ (V ι : Type) [AddCommGroup V] [Module ℂ V] (ρ : ι → Module.End ℂ V) (T : Module.End ℂ V),
      Nontrivial V → Module.rank ℂ V ≤ Cardinal.aleph0 →
      (∀ N : Submodule ℂ V, (∀ i, ∀ x ∈ N, ρ i x ∈ N) → N = ⊥ ∨ N = ⊤) →
      (∀ i, T * ρ i = ρ i * T) → ∃ c : ℂ, T = c • 1 := by
  intro V ι _ _ ρ T hV hrank hirr hcomm
  by_contra hne
  push_neg at hne
  have hunit : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c) := by
    intro c
    set S := T - algebraMap ℂ (Module.End ℂ V) c with hS
    have hS0 : S ≠ 0 := by
      intro h0
      apply hne c
      rw [← Algebra.algebraMap_eq_smul_one]
      exact sub_eq_zero.1 h0
    have hSc : ∀ i x, S (ρ i x) = ρ i (S x) := by
      intro i x
      have := LinearMap.congr_fun (hcomm i) x
      simp only [Module.End.mul_apply] at this
      simp [hS, this, Module.algebraMap_end_apply]
    rw [Module.End.isUnit_iff]
    constructor
    · rw [← LinearMap.ker_eq_bot]
      refine (hirr _ ?_).resolve_right ?_
      · intro i x hx
        rw [LinearMap.mem_ker] at hx ⊢
        rw [hSc, hx, map_zero]
      · rw [LinearMap.ker_eq_top]; exact hS0
    · rw [← LinearMap.range_eq_top]
      refine (hirr _ ?_).resolve_left ?_
      · rintro i _ ⟨x, rfl⟩
        exact ⟨ρ i x, hSc i x⟩
      · rw [LinearMap.range_eq_bot]; exact hS0
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  choose w hw using fun c => ((Module.End.isUnit_iff _).1 (hunit c)).2 v
  have hli := linearIndependent_of_sub_apply_eq T hunit v hv w hw
  have h1 := hli.cardinal_le_rank.trans hrank
  rw [Cardinal.mk_complex] at h1
  exact absurd h1 (not_le.2 Cardinal.aleph0_lt_continuum)

end GlobalTheory
