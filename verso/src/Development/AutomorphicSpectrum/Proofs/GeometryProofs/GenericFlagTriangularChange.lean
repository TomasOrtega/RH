import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

namespace GlobalTheory.CompanionTheory.Ar.FlagChange

open GlobalTheory.CompanionTheory.Ar

/- English proof (translation)
Unfold `flagStep at hx`. Take `⟨l, hl, rfl⟩` from `(Finsupp.mem_span_image_iff_linearCombination L).1 hx`. Use `⟨l, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `: k ∈ ({k : Fin r | (k : ℕ) < n} : Set (Fin r))` using `hl (Finsupp.mem_support_iff.2 h)`.

Conclude with `absurd this (not_lt.2 hk)`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul L (g i))]`.
-/
theorem exists_coeff_of_mem_step {L Li : Type} [Field L] [AddCommGroup Li] [Module L Li] {r : ℕ}
    (g : Fin r → Li) (n : ℕ) (x : Li) (hx : x ∈ flagStep L g n) :
    ∃ c : Fin r → L, (∀ k : Fin r, n ≤ (k : ℕ) → c k = 0) ∧ x = ∑ k, c k • g k := by
  unfold flagStep at hx
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination L).1 hx
  refine ⟨l, fun k hk => ?_, ?_⟩
  · by_contra h
    have : k ∈ ({k : Fin r | (k : ℕ) < n} : Set (Fin r)) :=
      hl (Finsupp.mem_support_iff.2 h)
    exact absurd this (not_lt.2 hk)
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (fun i => zero_smul L (g i))]

/- English proof (translation)
Establish `hC : ∀ i : Fin r, ∃ c : Fin r → L, (∀ k : Fin r, (i : ℕ) + 1 ≤ (k : ℕ) → c k = 0) ∧ b i = ∑ k, c k • g k` using `fun i => exists_coeff_of_mem_step g _ _ (by`. Rewrite using `[← hflag]`. Conclude with `Submodule.subset_span ⟨i, by simp, rfl⟩)`. Use `choose C hC0 hCb using hC`. Establish `hgW : ∀ k, g k = ∑ m, w m k • ∑ j, v j m • f j`.

Introduce `k`. Rewrite using `[hg k]`. Simplify using `only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]`.

Use `⟨Matrix.of fun i m => ∑ k, C i k * w m k, fun i => ?_, fun i m him => ?_, fun i => ?_⟩` and prove the remaining obligations. Generalize the expression as in `hW : (fun m => ∑ j, v j m • f j) = W at *`. Establish `hW' : ∀ m, ∑ j, v j m • f j = W m` using `fun m => congrFun hW m`. Simplify using `only [hW'] at hgW ⊢`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.smul_sum, Finset.sum_smul, smul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = _ := rfl`. Use `show ∑ k, C i k * w m k = 0`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hk : k ≤ i`. Rewrite using `[hw0 m k (lt_of_le_of_lt hk him), mul_zero]`. Rewrite using `[hC0 i k (not_le.1 hk), zero_mul]`. Establish `hdiag : ∑ k, C i k * w i k = C i i * w i i`. Use `Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)` and prove the remaining obligations.

Break down `lt_or_gt_of_ne hki with h | h` into its components or cases. Rewrite using `[hw0 i k h, mul_zero]`. Rewrite using `[hC0 i k h, zero_mul]`. Use `show ∑ k, C i k * w i k ≠ 0`. Rewrite using `[hdiag]`.

Use `mul_ne_zero (fun h0 => ?_) (hwd i)` and prove the remaining obligations. Establish `hmem : b i ∈ flagStep L g i`. Rewrite using `[hCb i]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < i`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`. Establish `hz : C i k = 0`. Break down `eq_or_lt_of_le (not_lt.1 hk) with h | h` into its components or cases. Rewrite using `[show k = i from Fin.ext h.symm, h0]`. Conclude with `hC0 i k h`.

Rewrite using `[hz, zero_smul]`. Conclude with `Submodule.zero_mem _`. Rewrite `hmem` using `[← hflag]`. Conclude with `hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (by simp) hmem`.
-/
theorem adapted_triangular (L Li : Type) [Field L] [AddCommGroup Li] [Module L Li] (r : ℕ)
    (f b g : Fin r → Li) (v w : Matrix (Fin r) (Fin r) L)
    (_hf : LinearIndependent L f) (hb : LinearIndependent L b)
    (_hv1 : ∀ k, v k k = 1) (_hv0 : ∀ l k, l < k → v l k = 0)
    (hw0 : ∀ l k, k < l → w l k = 0) (hwd : ∀ k, w k k ≠ 0)
    (hg : ∀ k, g k = ∑ j, (v * w) j k • f j)
    (hflag : ∀ i : ℕ, flagStep L b i = flagStep L g i) :
    ∃ Tm : Matrix (Fin r) (Fin r) L, (∀ i, b i = ∑ m, Tm i m • ∑ j, v j m • f j) ∧
      (∀ i m, i < m → Tm i m = 0) ∧ ∀ i, Tm i i ≠ 0 := by
  have hC : ∀ i : Fin r, ∃ c : Fin r → L,
      (∀ k : Fin r, (i : ℕ) + 1 ≤ (k : ℕ) → c k = 0) ∧ b i = ∑ k, c k • g k := fun i =>
    exists_coeff_of_mem_step g _ _ (by
      rw [← hflag]
      exact Submodule.subset_span ⟨i, by simp, rfl⟩)
  choose C hC0 hCb using hC
  have hgW : ∀ k, g k = ∑ m, w m k • ∑ j, v j m • f j := by
    intro k
    rw [hg k]
    simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  refine ⟨Matrix.of fun i m => ∑ k, C i k * w m k, fun i => ?_, fun i m him => ?_, fun i => ?_⟩
  · generalize hW : (fun m => ∑ j, v j m • f j) = W at *
    have hW' : ∀ m, ∑ j, v j m • f j = W m := fun m => congrFun hW m
    simp only [hW'] at hgW ⊢
    calc b i = ∑ k, C i k • ∑ m, w m k • W m :=
          (hCb i).trans (Finset.sum_congr rfl fun k _ => by rw [hgW k])
      _ = ∑ m, (∑ k, C i k * w m k) • W m := by
          simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
          exact Finset.sum_comm
      _ = _ := rfl
  · show ∑ k, C i k * w m k = 0
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ≤ i
    · rw [hw0 m k (lt_of_le_of_lt hk him), mul_zero]
    · rw [hC0 i k (not_le.1 hk), zero_mul]
  · have hdiag : ∑ k, C i k * w i k = C i i * w i i := by
      refine Finset.sum_eq_single i (fun k _ hki => ?_) (fun h => absurd (Finset.mem_univ i) h)
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hw0 i k h, mul_zero]
      · rw [hC0 i k h, zero_mul]
    show ∑ k, C i k * w i k ≠ 0
    rw [hdiag]
    refine mul_ne_zero (fun h0 => ?_) (hwd i)
    have hmem : b i ∈ flagStep L g i := by
      rw [hCb i]
      refine Submodule.sum_mem _ fun k _ => ?_
      by_cases hk : (k : ℕ) < i
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
      · have hz : C i k = 0 := by
          rcases eq_or_lt_of_le (not_lt.1 hk) with h | h
          · rw [show k = i from Fin.ext h.symm, h0]
          · exact hC0 i k h
        rw [hz, zero_smul]
        exact Submodule.zero_mem _
    rw [← hflag] at hmem
    exact hb.notMem_span_image (s := {k | (k : ℕ) < i}) (x := i) (by simp) hmem

end GlobalTheory.CompanionTheory.Ar.FlagChange
