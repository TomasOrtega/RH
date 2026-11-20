import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange

namespace UpperTheory.Gal.W2

/- English proof (translation)
Unfold `IntMult`. Introduce `O _ bar D' ga r hr h`. Set `Iv : Ideal ℤ` to `Ideal.span {x | ∃ u u', D'.EF u u' = x}`. Establish `hval : ∀ u u', D'.EF u u' ∈ Iv` using `fun u u' => Ideal.subset_span ⟨u, u', rfl⟩`. Take `⟨c, hc⟩` from `(IsPrincipalIdealRing.principal Iv).principal`.

Establish `hc' : Iv = Ideal.span {c}` using `hc`. Establish `key : ∀ x ∈ Iv, ∃ y ∈ Iv, (y : ℚ) = r * x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨u, u', rfl⟩` from `hx`. Conclude with `⟨_, hval (ga u) (ga u'), h u u'⟩`. Consider the case `zero => exact ⟨0, Iv.zero_mem, by simp⟩`. Consider the case `add a b _ _ iha ihb`. Take `⟨y, hy, e⟩` from `iha`.

Take `⟨z, hz, e'⟩` from `ihb`. Conclude with `⟨y + z, Iv.add_mem hy hz, by push_cast; rw [e, e']; ring⟩`. Consider the case `smul a x _ ih`. Take `⟨y, hy, e⟩` from `ih`. Conclude with `⟨a * y, Iv.mul_mem_left a hy, by simp only [smul_eq_mul]; push_cast; rw [e]; ring⟩`.

Distinguish the cases in `hc0 : c = 0`. Use `⟨1, one_pos, fun u u' => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ u u', D'.EF u u' = 0` using `fun u u' => by`. Use `hval u u'` as an intermediate fact. Rewrite `this` using `[hc', hc0, Ideal.mem_span_singleton]`.

Simplify using `using this`. Rewrite using `[hz, hz, mul_zero]`. Establish `hcI : c ∈ Iv` using `by rw [hc']; exact Ideal.mem_span_singleton_self c`. Take `⟨y, hy, e⟩` from `key c hcI`. Rewrite `hy` using `[hc', Ideal.mem_span_singleton]`.

Take `⟨m, rfl⟩` from `hy`. Establish `hcq : (c : ℚ) ≠ 0` using `by exact_mod_cast hc0`. Establish `hm : (m : ℚ) = r`. Move the coercions through the operations in `at e`. Establish `: (c : ℚ) * m = c * r` using `by rw [e]; ring`.

Conclude with `mul_left_cancel₀ hcq this`. Use `⟨m, ?_, fun u u' => ?_⟩` and prove the remaining obligations. Establish `: (0 : ℚ) < m` using `hm ▸ hr`. Conclude with `this` after adjusting the coercions. Use `h u u'` as an intermediate fact.

Rewrite `this` using `[← hm]`. Conclude with `this` after adjusting the coercions.
-/
theorem intMult_of : IntMult := by
  unfold IntMult
  intro O _ bar D' ga r hr h
  let Iv : Ideal ℤ := Ideal.span {x | ∃ u u', D'.EF u u' = x}
  have hval : ∀ u u', D'.EF u u' ∈ Iv := fun u u' => Ideal.subset_span ⟨u, u', rfl⟩
  obtain ⟨c, hc⟩ := (IsPrincipalIdealRing.principal Iv).principal
  have hc' : Iv = Ideal.span {c} := hc
  have key : ∀ x ∈ Iv, ∃ y ∈ Iv, (y : ℚ) = r * x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, u', rfl⟩ := hx
      exact ⟨_, hval (ga u) (ga u'), h u u'⟩
    | zero => exact ⟨0, Iv.zero_mem, by simp⟩
    | add a b _ _ iha ihb =>
      obtain ⟨y, hy, e⟩ := iha
      obtain ⟨z, hz, e'⟩ := ihb
      exact ⟨y + z, Iv.add_mem hy hz, by push_cast; rw [e, e']; ring⟩
    | smul a x _ ih =>
      obtain ⟨y, hy, e⟩ := ih
      exact ⟨a * y, Iv.mul_mem_left a hy, by simp only [smul_eq_mul]; push_cast; rw [e]; ring⟩
  by_cases hc0 : c = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have hz : ∀ u u', D'.EF u u' = 0 := fun u u' => by
      have := hval u u'
      rw [hc', hc0, Ideal.mem_span_singleton] at this
      simpa using this
    rw [hz, hz, mul_zero]
  · have hcI : c ∈ Iv := by rw [hc']; exact Ideal.mem_span_singleton_self c
    obtain ⟨y, hy, e⟩ := key c hcI
    rw [hc', Ideal.mem_span_singleton] at hy
    obtain ⟨m, rfl⟩ := hy
    have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc0
    have hm : (m : ℚ) = r := by
      push_cast at e
      have : (c : ℚ) * m = c * r := by rw [e]; ring
      exact mul_left_cancel₀ hcq this
    refine ⟨m, ?_, fun u u' => ?_⟩
    · have : (0 : ℚ) < m := hm ▸ hr
      exact_mod_cast this
    · have := h u u'
      rw [← hm] at this
      exact_mod_cast this

end UpperTheory.Gal.W2
