import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0`. Introduce `a`. Use `split_ifs`. Establish `: ω a + e - Λ a = (ω a - Λ a) + e` using `by ring`. Rewrite using `[this]`.

Conclude with `(abs_add_le _ _).trans (by linarith)`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.
-/
theorem l1_shift_single_le {n : ℕ} (ω Λ : Fin n → ℝ) (t e : ℝ) (he : |e| ≤ 1) (c : Fin n)
    (h : ∑ a, |ω a - Λ a| ≤ t) :
    ∑ a, |(ω a + if a = c then e else 0) - Λ a| ≤ t + 1 := by
  have h1 : ∀ a, |(ω a + if a = c then e else 0) - Λ a| ≤ |ω a - Λ a| + if a = c then 1 else 0 := by
    intro a
    split_ifs
    · have : ω a + e - Λ a = (ω a - Λ a) + e := by ring
      rw [this]
      exact (abs_add_le _ _).trans (by linarith)
    · simp
  calc _ ≤ ∑ a, (|ω a - Λ a| + if a = c then 1 else 0) := Finset.sum_le_sum fun a _ => h1 a
    _ = ∑ a, |ω a - Λ a| + 1 := by rw [Finset.sum_add_distrib]; simp
    _ ≤ t + 1 := by linarith

/- English proof (translation)
Introduce `M _ _ n ε E N _ _ F io pr Λ t hT`. Use `⟨fun w hw s c => ?_, fun s y hy d => ?_⟩` and prove the remaining obligations. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨ω, hω, hx⟩` from `hx`.

Use `Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0, l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[← hT.pr_comm, ← map_smul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [dualTens, Pi.smul_apply]`.

Distinguish the cases in `hi : i = c`. Substitute `hi` using the available equality. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality. Simplify using `[hx a, add_smul, sub_eq_add_neg]`.

Establish `: ¬ i = a` using `fun h => ha h.symm`. Simplify using `[hx a, ha, this]`. Distinguish the cases in `ha : i = a`. Substitute `ha` using the available equality. Simplify using `[hi]`.

Simplify using `[hi, ha]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [Pi.single_add, map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [Pi.single_smul, map_smul]`.

Conclude with `Submodule.smul_mem _ _ hx`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨ω, hω, hx⟩` from `hx`. Use `Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0, l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩` and prove the remaining obligations.

Establish `h` using `congrFun (hT.io_comm s a a x) d`. Rewrite `h` using `[hx a, map_smul]`. Simplify using `only [dualTens, Pi.smul_apply] at h`. Rewrite `h` using `[eq_sub_iff_add_eq]`. Rewrite using `[← h]`.

Distinguish the cases in `ha : a = d`. Substitute `ha` using the available equality. Simplify using `[add_smul]`. Establish `: ¬ d = a` using `fun h => ha h.symm`. Simplify using `[ha, this]`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, Pi.add_apply]`. Conclude with `add_mem hx hy`. Consider the case `smul r x _ hx => rw [map_smul, Pi.smul_apply]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem algTens_wtNear : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (Λ : Fin n → ℝ) (t : ℝ), AlgTens ε E N F io pr → (∀ w, w ∈ WtNear E Λ t → ∀ s c, pr s (Pi.single c w) ∈ WtNear (F s) Λ (t + 1)) ∧ ∀ s (y : N s), y ∈ WtNear (F s) Λ t → ∀ d, io s y d ∈ WtNear E Λ (t + 1) := by
  intro M _ _ n ε E N _ _ F io pr Λ t hT
  refine ⟨fun w hw s c => ?_, fun s y hy d => ?_⟩
  · induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = c then -1 else 0,
        l1_shift_single_le ω Λ t (-1) (by simp) c hω, fun a => ?_⟩
      rw [← hT.pr_comm, ← map_smul]
      congr 1
      funext i
      simp only [dualTens, Pi.smul_apply]
      by_cases hi : i = c
      · subst hi
        by_cases ha : a = i
        · subst ha
          simp [hx a, add_smul, sub_eq_add_neg]
        · have : ¬ i = a := fun h => ha h.symm
          simp [hx a, ha, this]
      · by_cases ha : i = a
        · subst ha
          simp [hi]
        · simp [hi, ha]
    | zero => simp
    | add x y _ _ hx hy => rw [Pi.single_add, map_add]; exact add_mem hx hy
    | smul r x _ hx => rw [Pi.single_smul, map_smul]; exact Submodule.smul_mem _ _ hx
  · induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ω, hω, hx⟩ := hx
      refine Submodule.subset_span ⟨fun a => ω a + if a = d then 1 else 0,
        l1_shift_single_le ω Λ t 1 (by simp) d hω, fun a => ?_⟩
      have h := congrFun (hT.io_comm s a a x) d
      rw [hx a, map_smul] at h
      simp only [dualTens, Pi.smul_apply] at h
      rw [eq_sub_iff_add_eq] at h
      rw [← h]
      by_cases ha : a = d
      · subst ha
        simp [add_smul]
      · have : ¬ d = a := fun h => ha h.symm
        simp [ha, this]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, Pi.add_apply]; exact add_mem hx hy
    | smul r x _ hx => rw [map_smul, Pi.smul_apply]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
