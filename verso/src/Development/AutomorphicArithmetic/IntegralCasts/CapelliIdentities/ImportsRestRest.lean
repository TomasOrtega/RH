import Mathlib

namespace ZbYhc5Helpers

/- English proof (translation)
Use function extensionality and compare the values at `i`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.real_smul] <;> ring`.
-/
private lemma key {g : ℕ} (c : ℂ) (u u' : Fin g → ℂ) :
    c • (u + Complex.I • u') = (c.re • u - c.im • u') + Complex.I • (c.im • u + c.re • u') := by
  funext i
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

end ZbYhc5Helpers

/- English proof (translation)
Introduce `g T w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, a', ha', rfl⟩` from `hx`. Take `⟨b, hb, b', hb', rfl⟩` from `hy`. Conclude with `⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by`. Rewrite using `[smul_add]`. Use the proof step `abel⟩`.

Consider the case `smul c x _ hx`. Take `⟨a, ha, a', ha', rfl⟩` from `hx`. Use `⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩` and prove the remaining obligations. Conclude with `Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')`. Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')`.
-/
theorem UpperTheory.Reformulated.B.Yhc5.main :
    ∀ {g : ℕ} {T : Set (Fin g → ℂ)} {w : Fin g → ℂ},
      w ∈ Submodule.span ℂ T → ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' := by
  intro g T w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    obtain ⟨b, hb, b', hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by
      rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    refine ⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
