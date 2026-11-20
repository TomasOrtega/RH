import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory.WtOrth

/- English proof (translation)
Take `⟨a, ha⟩` from `Function.ne_iff.mp hne`. Establish `h` using `hU a a x y`. Rewrite `h` using `[hx a, hy a, inner_smul_left, inner_smul_right]`. Simplify using `only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h`. Establish `h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0` using `by rw [sub_mul, h, sub_self]`.

Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha`. Conclude with `h3`.
-/
theorem inner_eq_zero_of_ne {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ} {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ M} (hU : IsUnitary ε E) {ω ω' : Fin n → ℝ} {x y : M}
    (hx : IsWeight E ω x) (hy : IsWeight E ω' y) (hne : ω ≠ ω') : ⟪x, y⟫_ℂ = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  have h := hU a a x y
  rw [hx a, hy a, inner_smul_left, inner_smul_right] at h
  simp only [Formalism.REAL.sgn, if_true, Complex.ofReal_one, one_mul, Complex.conj_ofReal] at h
  have h2 : ((ω a : ℂ) - (ω' a : ℂ)) * ⟪x, y⟫_ℂ = 0 := by rw [sub_mul, h, sub_self]
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h3)) ha
  · exact h3

/- English proof (translation)
Unfold `WtNear at hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨ω, h1, h2⟩` from `hy`. Use `⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `ω' h`. Rewrite using `[Finset.mem_singleton.mp h]`. Conclude with `h1`. Introduce `ω'`. Distinguish the cases in `h : ω' = ω`.

Simplify using `only [h, if_true]`. Conclude with `h2`. Introduce `a`. Simplify using `[h]`. Introduce `ω' h`.

Establish `: ω' ≠ ω` using `fun e => h (Finset.mem_singleton.mpr e)`. Simplify using `[this]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨T, x, h1, h2, h3, h4⟩` from `hy`. Take `⟨T', x', h1', h2', h3', h4'⟩` from `hz`. Use `⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ω h`. Break down `Finset.mem_union.mp h with h | h` into its components or cases.

Conclude with `h1 ω h`. Conclude with `h1' ω h`. Introduce `ω a`. Simplify using `only [map_add, h2 ω a, h2' ω a, smul_add]`. Introduce `ω h`.

Rewrite `h` using `[Finset.mem_union, not_or]`. Simplify using `[h3 ω h.1, h3' ω h.2]`. Rewrite using `[Finset.sum_add_distrib, h4, h4']`. Use `congr 1`. Conclude with `Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h`.

Conclude with `Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h`. Consider the case `smul c y _ hy`. Take `⟨T, x, h1, h2, h3, h4⟩` from `hy`. Use `⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ω a`.

Simplify using `only [map_smul, h2 ω a]`. Conclude with `smul_comm _ _ _`. Introduce `ω h`. Simplify using `[h3 ω h]`. Rewrite using `[h4, Finset.smul_sum]`.
-/
theorem exists_decomp {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M) (hw : w ∈ WtNear E Λ t) :
    ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t) ∧
      (∀ ω, IsWeight E ω (x ω)) ∧ (∀ ω, ω ∉ T → x ω = 0) ∧ w = ∑ ω ∈ T, x ω := by
  classical
  unfold WtNear at hw
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨ω, h1, h2⟩ := hy
    refine ⟨{ω}, fun ω' => if ω' = ω then y else 0, ?_, ?_, ?_, ?_⟩
    · intro ω' h
      rw [Finset.mem_singleton.mp h]; exact h1
    · intro ω'
      by_cases h : ω' = ω
      · simp only [h, if_true]; exact h2
      · intro a; simp [h]
    · intro ω' h
      have : ω' ≠ ω := fun e => h (Finset.mem_singleton.mpr e)
      simp [this]
    · simp
  | zero => exact ⟨∅, fun _ => 0, by simp, fun ω a => by simp, by simp, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    obtain ⟨T', x', h1', h2', h3', h4'⟩ := hz
    refine ⟨T ∪ T', fun ω => x ω + x' ω, ?_, ?_, ?_, ?_⟩
    · intro ω h
      rcases Finset.mem_union.mp h with h | h
      · exact h1 ω h
      · exact h1' ω h
    · intro ω a
      simp only [map_add, h2 ω a, h2' ω a, smul_add]
    · intro ω h
      rw [Finset.mem_union, not_or] at h
      simp [h3 ω h.1, h3' ω h.2]
    · rw [Finset.sum_add_distrib, h4, h4']
      congr 1
      · exact Finset.sum_subset Finset.subset_union_left fun ω _ h => h3 ω h
      · exact Finset.sum_subset Finset.subset_union_right fun ω _ h => h3' ω h
  | smul c y _ hy =>
    obtain ⟨T, x, h1, h2, h3, h4⟩ := hy
    refine ⟨T, fun ω => c • x ω, h1, ?_, ?_, ?_⟩
    · intro ω a
      simp only [map_smul, h2 ω a]
      exact smul_comm _ _ _
    · intro ω h
      simp [h3 ω h]
    · rw [h4, Finset.smul_sum]

/- English proof (translation)
Introduce `M _ _ n ε E Λ t w hU hw`. Take `⟨T, x, h1, h2, _, h4⟩` from `exists_decomp E Λ t w hw`. Conclude with `⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4, fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩`.
-/
theorem wtNear_orth_decomp : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (Λ : Fin n → ℝ) (t : ℝ) (w : M), IsUnitary ε E → w ∈ WtNear E Λ t → ∃ (T : Finset (Fin n → ℝ)) (x : (Fin n → ℝ) → M), (∀ ω ∈ T, ∑ a, |ω a - Λ a| ≤ t ∧ IsWeight E ω (x ω)) ∧ w = ∑ ω ∈ T, x ω ∧ ∀ ω ∈ T, ∀ ω' ∈ T, ω ≠ ω' → ⟪x ω, x ω'⟫_ℂ = 0 := by
  intro M _ _ n ε E Λ t w hU hw
  obtain ⟨T, x, h1, h2, _, h4⟩ := exists_decomp E Λ t w hw
  exact ⟨T, x, fun ω h => ⟨h1 ω h, h2 ω⟩, h4,
    fun ω _ ω' _ hne => inner_eq_zero_of_ne hU (h2 ω) (h2 ω') hne⟩

end GlobalTheory.WtOrth
