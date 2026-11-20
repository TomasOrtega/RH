import Mathlib

namespace GlobalTheory.NonzeroMultipleInSpan

open NumberField

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Establish `h : (a * b) • (y + z) = b • (a • y) + a • (b • z)`. Rewrite using `[smul_add, ← mul_smul, ← mul_smul, mul_comm b a]`.

Rewrite using `[h]`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)`. Consider the case `smul c y _ hy`. Take `⟨a, ha, hay⟩` from `hy`. Take `⟨⟨p, q⟩, hpq⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c`.

Use `⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩` and prove the remaining obligations. Establish `h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y)`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Simplify using `only [Algebra.smul_def, map_mul]`.

Simplify using `only at hpq`. Rewrite using `[← hpq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `Submodule.smul_mem _ p hay`.
-/
theorem exists_ne_zero_smul_mem_span {LL : Type} [Field LL] [NumberField LL] {n : ℕ}
    (T : Set (Fin n → LL)) :
    ∀ x ∈ Submodule.span LL T, ∃ d : 𝓞 LL, d ≠ 0 ∧ d • x ∈ Submodule.span (𝓞 LL) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using Submodule.subset_span hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h : (a * b) • (y + z) = b • (a • y) + a • (b • z) := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm b a]
    rw [h]
    exact Submodule.add_mem _ (Submodule.smul_mem _ b hay) (Submodule.smul_mem _ a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 LL)) c
    refine ⟨(q : 𝓞 LL) * a, mul_ne_zero (nonZeroDivisors.ne_zero q.2) ha, ?_⟩
    have h : ((q : 𝓞 LL) * a) • (c • y) = p • (a • y) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul]
      simp only at hpq
      rw [← hpq]
      ring
    rw [h]
    exact Submodule.smul_mem _ p hay

end GlobalTheory.NonzeroMultipleInSpan
