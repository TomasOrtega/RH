import Mathlib

/- English proof (translation)
Introduce `V _ _ s w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩`. Consider the case `zero => exact ⟨1, Nat.one_pos, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hx⟩` from `hx`. Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, Nat.mul_pos ha hb, ?_⟩` and prove the remaining obligations. Establish `h : (a * b) • (x + y) = b • (a • x) + a • (b • y)`. Rewrite using `[smul_add, smul_smul, smul_smul, mul_comm b a]`.

Rewrite using `[h]`. Conclude with `add_mem (nsmul_mem hx b) (nsmul_mem hy a)`. Consider the case `smul q x _ hx`. Take `⟨a, ha, hx⟩` from `hx`. Use `⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩` and prove the remaining obligations.

Establish `h : (q.den * a) • (q • x) = q.num • (a • x)`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x, ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[← Rat.mul_den_eq_num q]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Conclude with `zsmul_mem hx _`.
-/
theorem UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℚ V] (s : Set V),
    ∀ w ∈ Submodule.span ℚ s, ∃ (k : ℕ), (0 : ℕ) < k ∧ k • w ∈ AddSubgroup.closure s := by
  intro V _ _ s w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact add_mem (nsmul_mem hx b) (nsmul_mem hy a)
  | smul q x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩
    have h : (q.den * a) • (q • x) = q.num • (a • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
      congr 1
      rw [← Rat.mul_den_eq_num q]
      push_cast
      ring
    rw [h]
    exact zsmul_mem hx _
