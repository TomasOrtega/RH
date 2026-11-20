import Mathlib

noncomputable def UpperTheory.Reformulated.B.Qh31.vR :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → K → WithTop ℝ :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (x : K) ↦
      WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ)) ((v : K → WithTop ℚ) x)

noncomputable def UpperTheory.Reformulated.B.Qh31.vge :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → ℝ → K → Prop :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) ↦ (↑a : WithTop ℝ) ≤ UpperTheory.Reformulated.B.Qh31.vR v x

/- English proof (translation)
The claim follows from `Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)`.
-/
private theorem UpperTheory.Reformulated.B.Qh31.map_cast_mono :
    Monotone (WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ))) :=
  Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)

/- English proof (translation)
Introduce `K _ v ι a s f h`. Use `Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h` and prove the remaining obligations. Introduce `x y hx hy`. Unfold `UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *`. Break down `min_le_iff.mp (v.map_add x y) with hxy | hxy` into its components or cases.

Conclude with `hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)`. Conclude with `hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)`. Unfold `UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR`. Rewrite using `[v.map_zero, WithTop.map_top]`. Conclude with `le_top`.
-/
theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by
  intro K _ v ι a s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h
  · intro x y hx hy
    unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *
    rcases min_le_iff.mp (v.map_add x y) with hxy | hxy
    · exact hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
    · exact hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
  · unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR
    rw [v.map_zero, WithTop.map_top]
    exact le_top
