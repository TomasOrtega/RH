import Mathlib

/- English proof (translation)
Introduce `G V ι _ _ _ _ l hl T hT L`. Establish `hL : L ∈ Submodule.span ℂ (Set.range l)`. Apply `FiniteDimensional.mem_span_of_iInf_ker_le_ker` to reduce the goal to its premises. Introduce `a ha`. Establish `h0 : a = 0` using `hl a fun y => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ha y)`.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Proceed by induction on `hL using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨y, rfl⟩` from `hx`.

Conclude with `hT y`. Consider the case `zero => exact measurable_const`. Consider the case `add x y _ _ hx hy => exact hx.add hy`. Consider the case `smul c x _ hx => exact hx.const_mul c`.
-/
theorem UpperTheory.Reformulated.B.Qk65.measurable_of_separating_functionals :
    ∀ {G V ι : Type} [inst : MeasurableSpace G] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (l : ι → V →ₗ[ℂ] ℂ),
    (∀ (a : V), (∀ (y : ι), (l y : V → ℂ) a = (0 : ℂ)) → a = (0 : V)) →
      ∀ (T : G → V),
        (∀ (y : ι), Measurable fun (g : G) ↦ (l y : V → ℂ) (T g)) →
          ∀ (L : V →ₗ[ℂ] ℂ), Measurable fun (g : G) ↦ (L : V → ℂ) (T g) := by
  intro G V ι _ _ _ _ l hl T hT L
  have hL : L ∈ Submodule.span ℂ (Set.range l) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro a ha
    have h0 : a = 0 := hl a fun y => LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp ha y)
    rw [h0]
    exact Submodule.zero_mem _
  induction hL using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    exact hT y
  | zero => exact measurable_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.const_mul c
