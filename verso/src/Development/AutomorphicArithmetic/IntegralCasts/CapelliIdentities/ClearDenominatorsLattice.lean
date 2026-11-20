import Mathlib

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ L hL x`. Establish `hx : x ∈ Submodule.span K (↑L : Set V)` using `hL ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩`.

Consider the case `add y z _ _ hy hz`. Take `⟨r, hr, hry⟩` from `hy`. Take `⟨s, hs, hsz⟩` from `hz`. Use `⟨r * s, mul_ne_zero hr hs, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`.

Use `L.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `L.smul_mem _ hry`. Rewrite using `[mul_smul]`. Conclude with `L.smul_mem _ hsz`.

Consider the case `smul a y _ hy`. Take `⟨r, hr, hry⟩` from `hy`. Take `⟨⟨n, d⟩, hnd⟩` from `IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a`. Use `⟨r * d, mul_ne_zero hr (nonZeroDivisors.ne_zero d.2), ?_⟩` and prove the remaining obligations. Establish `h1 : (d : NumberField.RingOfIntegers K) • (a • y) = n • y`.

Rewrite using `[← algebraMap_smul K (d : NumberField.RingOfIntegers K) (a • y), ← mul_smul, mul_comm, hnd, algebraMap_smul]`. Rewrite using `[mul_smul, h1, ← mul_smul, mul_comm, mul_smul]`. Conclude with `L.smul_mem _ hry`.
-/
theorem UpperTheory.Reformulated.B.ClearDenominatorsLattice.exists_integer_smul_mem_of_span_top :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : _root_.Module K V] [inst_4 : _root_.Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    Submodule.span K (↑L : Set V) = ⊤ →
      ∀ (x : V), ∃ (r : NumberField.RingOfIntegers K), r ≠ (0 : NumberField.RingOfIntegers K) ∧ r • x ∈ L := by
  intro K V _ _ _ _ _ _ L hL x
  have hx : x ∈ Submodule.span K (↑L : Set V) := hL ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact L.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨r * s, mul_ne_zero hr hs, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact L.smul_mem _ hry
    · rw [mul_smul]
      exact L.smul_mem _ hsz
  | smul a y _ hy =>
    obtain ⟨r, hr, hry⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers K)) a
    refine ⟨r * d, mul_ne_zero hr (nonZeroDivisors.ne_zero d.2), ?_⟩
    have h1 : (d : NumberField.RingOfIntegers K) • (a • y) = n • y := by
      rw [← algebraMap_smul K (d : NumberField.RingOfIntegers K) (a • y), ← mul_smul, mul_comm,
        hnd, algebraMap_smul]
    rw [mul_smul, h1, ← mul_smul, mul_comm, mul_smul]
    exact L.smul_mem _ hry
