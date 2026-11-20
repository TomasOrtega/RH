import Mathlib

/- English proof (translation)
Introduce `K _ _ V _ _ _ _ M x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨b, hb, hbz⟩` from `hz`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `M.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `M.smul_mem b hay`. Rewrite using `[mul_smul]`. Conclude with `M.smul_mem a hbz`. Consider the case `smul c y _ hy`.

Take `⟨a, ha, hay⟩` from `hy`. Take `⟨⟨p, q⟩, hpq⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c`. Use `⟨a * (q : NumberField.RingOfIntegers K), mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩` and prove the remaining obligations. Establish `h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y`. Rewrite using `[← algebraMap_smul K (q : NumberField.RingOfIntegers K), ← mul_smul, mul_comm]`.

Simplify using `only at hpq`. Rewrite using `[hpq, algebraMap_smul]`. Rewrite using `[mul_smul, h1, ← mul_smul, mul_comm, mul_smul]`. Conclude with `M.smul_mem p hay`.
-/
theorem UpperTheory.Reformulated.B.ExistsSmulMemTer.exists_smul_mem :
    ∀ {K : Type} [inst : Field K] [NumberField K] {V : Type} [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (M : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑M : Set V),
      ∃ (a : NumberField.RingOfIntegers K), a ≠ (0 : NumberField.RingOfIntegers K) ∧ a • x ∈ M := by
  intro K _ _ V _ _ _ _ M x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact M.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨p, q⟩, hpq⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) c
    refine ⟨a * (q : NumberField.RingOfIntegers K),
      mul_ne_zero ha (nonZeroDivisors.coe_ne_zero q), ?_⟩
    have h1 : (q : NumberField.RingOfIntegers K) • c • y = p • y := by
      rw [← algebraMap_smul K (q : NumberField.RingOfIntegers K), ← mul_smul, mul_comm]
      simp only at hpq
      rw [hpq, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay
