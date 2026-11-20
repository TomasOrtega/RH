import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `x _ hx k`. Rewrite using `[hx k (by simp), Pi.single_zero]`. Conclude with `Λ.zero_mem`.

Consider the case `insert a S' ha ih`. Introduce `x hxΛ hx`. Establish `hne : ∀ k, k ≠ a → u ^ k - u ^ a ≠ 0`. Introduce `k hk h`. Apply `hr (k - a) (sub_ne_zero.mpr hk)` to reduce the goal to its premises.

Rewrite using `[zpow_sub₀ hu, sub_eq_zero.mp h, div_self (zpow_ne_zero a hu)]`. Establish `hyΛ : (fun k => u ^ k • x k) - u ^ a • x ∈ Λ` using `Λ.sub_mem (hγ x hxΛ) (Λ.smul_mem _ hxΛ)`. Establish `hyv : ∀ k, ((fun k => u ^ k • x k) - u ^ a • x) k = (u ^ k - u ^ a) • x k`. Introduce `k`. Simplify using `[sub_smul]`.

Establish `hy : ∀ k, k ∉ S' → ((fun k => u ^ k • x k) - u ^ a • x) k = 0`. Introduce `k hk`. Rewrite using `[hyv]`. Distinguish the cases in `hka : k = a`. Rewrite using `[hka, sub_self, zero_smul]`.

Rewrite using `[hx k (by simp [hka, hk]), smul_zero]`. Establish `hoff : ∀ k, k ≠ a → Pi.single k (x k) ∈ Λ`. Introduce `k hk`. Establish `h1` using `ih _ hyΛ hy k`. Rewrite `h1` using `[hyv]`.

Establish `e : Pi.single k (x k) = (u ^ k - u ^ a)⁻¹ • (Pi.single k ((u ^ k - u ^ a) • x k) : ℤ → D)`. Rewrite using `[Pi.single_smul, smul_smul, inv_mul_cancel₀ (hne k hk), one_smul]`. Rewrite using `[e]`. Conclude with `Λ.smul_mem _ h1`. Introduce `k`.

Distinguish the cases in `hka : k = a`. Rewrite using `[hka]`. Establish `hsum : (∑ j ∈ S', Pi.single j (x j)) ∈ Λ` using `Λ.sum_mem (fun j hj => hoff j (by rintro rfl; exact ha hj))`. Establish `e : Pi.single a (x a) = x - ∑ j ∈ S', Pi.single j (x j)`. Use function extensionality and compare the values at `j`.

Rewrite using `[Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single]`. Distinguish the cases in `hjS : j ∈ S'`. Establish `hja : j ≠ a` using `by rintro rfl; exact ha hjS`. Simplify using `[hjS, hja]`. Distinguish the cases in `hja : j = a`.

Rewrite using `[hja]`. Simplify using `[ha]`. Simplify using `[hjS, hja, hx j (by simp [hja, hjS])]`. Rewrite using `[e]`. Conclude with `Λ.sub_mem hxΛ hsum`.

Conclude with `hoff k hka`.
-/
theorem single_mem_of_support_subset {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]
    (u : LL) (Λ : Submodule LL (ℤ → D)) (hu : u ≠ 0) (hr : ∀ k : ℤ, k ≠ 0 → u ^ k ≠ 1)
    (hγ : ∀ x ∈ Λ, (fun k => u ^ k • x k) ∈ Λ) (S : Finset ℤ) :
    ∀ x ∈ Λ, (∀ k, k ∉ S → x k = 0) → ∀ k, Pi.single k (x k) ∈ Λ := by
  induction S using Finset.induction_on with
  | empty =>
    intro x _ hx k
    rw [hx k (by simp), Pi.single_zero]
    exact Λ.zero_mem
  | insert a S' ha ih =>
    intro x hxΛ hx

    have hne : ∀ k, k ≠ a → u ^ k - u ^ a ≠ 0 := by
      intro k hk h
      apply hr (k - a) (sub_ne_zero.mpr hk)
      rw [zpow_sub₀ hu, sub_eq_zero.mp h, div_self (zpow_ne_zero a hu)]
    have hyΛ : (fun k => u ^ k • x k) - u ^ a • x ∈ Λ := Λ.sub_mem (hγ x hxΛ) (Λ.smul_mem _ hxΛ)
    have hyv : ∀ k, ((fun k => u ^ k • x k) - u ^ a • x) k = (u ^ k - u ^ a) • x k := by
      intro k
      simp [sub_smul]
    have hy : ∀ k, k ∉ S' → ((fun k => u ^ k • x k) - u ^ a • x) k = 0 := by
      intro k hk
      rw [hyv]
      by_cases hka : k = a
      · rw [hka, sub_self, zero_smul]
      · rw [hx k (by simp [hka, hk]), smul_zero]
    have hoff : ∀ k, k ≠ a → Pi.single k (x k) ∈ Λ := by
      intro k hk
      have h1 := ih _ hyΛ hy k
      rw [hyv] at h1
      have e : Pi.single k (x k) =
          (u ^ k - u ^ a)⁻¹ • (Pi.single k ((u ^ k - u ^ a) • x k) : ℤ → D) := by
        rw [Pi.single_smul, smul_smul, inv_mul_cancel₀ (hne k hk), one_smul]
      rw [e]
      exact Λ.smul_mem _ h1
    intro k
    by_cases hka : k = a
    · rw [hka]
      have hsum : (∑ j ∈ S', Pi.single j (x j)) ∈ Λ :=
        Λ.sum_mem (fun j hj => hoff j (by rintro rfl; exact ha hj))
      have e : Pi.single a (x a) = x - ∑ j ∈ S', Pi.single j (x j) := by
        funext j
        rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_pi_single]
        by_cases hjS : j ∈ S'
        · have hja : j ≠ a := by rintro rfl; exact ha hjS
          simp [hjS, hja]
        · by_cases hja : j = a
          · rw [hja]
            simp [ha]
          · simp [hjS, hja, hx j (by simp [hja, hjS])]
      rw [e]
      exact Λ.sub_mem hxΛ hsum
    · exact hoff k hka

end GlobalTheory.Per
