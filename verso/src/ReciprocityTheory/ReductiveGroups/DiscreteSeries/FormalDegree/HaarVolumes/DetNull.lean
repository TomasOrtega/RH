import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

/- English proof (translation)
Establish `h : {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) | p.1 ∈ Submodule.span ℂ (Set.range p.2)} = Set.range (fun q : (Fin n → ℂ) × (Fin n → Fin m → ℂ) => (∑ j, q.1 j • q.2 j, q.2))`. Use extensionality with `⟨x, W⟩`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq, Prod.exists]`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, W, hc, rfl⟩`. Introduce and unpack `⟨c, W', hc, rfl⟩`. Conclude with `⟨c, hc⟩`. Rewrite using `[h]`.

Take `⟨K, hK, hKe⟩` from `isSigmaCompact_range (X := (Fin n → ℂ) × (Fin n → Fin m → ℂ)) (f := fun q => (∑ j, q.1 j • q.2 j, q.2)) (by fun_prop)`. Rewrite using `[← hKe]`. Conclude with `MeasurableSet.iUnion fun k => (hK k).measurableSet`.
-/
theorem measurableSet_mem_span_range (n m : ℕ) :
    MeasurableSet {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) |
      p.1 ∈ Submodule.span ℂ (Set.range p.2)} := by
  have h : {p : (Fin m → ℂ) × (Fin n → Fin m → ℂ) | p.1 ∈ Submodule.span ℂ (Set.range p.2)} =
      Set.range (fun q : (Fin n → ℂ) × (Fin n → Fin m → ℂ) => (∑ j, q.1 j • q.2 j, q.2)) := by
    ext ⟨x, W⟩
    simp only [Set.mem_ofPred_eq, Set.mem_range, Prod.mk.injEq, Prod.exists]
    rw [Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, W, hc, rfl⟩
    · rintro ⟨c, W', hc, rfl⟩
      exact ⟨c, hc⟩
  rw [h]
  obtain ⟨K, hK, hKe⟩ := isSigmaCompact_range (X := (Fin n → ℂ) × (Fin n → Fin m → ℂ))
    (f := fun q => (∑ j, q.1 j • q.2 j, q.2)) (by fun_prop)
  rw [← hKe]
  exact MeasurableSet.iUnion fun k => (hK k).measurableSet

/- English proof (translation)
Establish `h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range W)) ≤ n` using `by first`. Consider the case `simpa using finrank_span_range_le_card (R := ℂ) W`. Consider the case `simpa using Submodule.finrank_span_range_le_card (R := ℂ) W`. Consider the case `simpa using finrank_range_le_card (R := ℂ) W`. Consider the case `(have h2 := finrank_range_le_card (R := ℂ) W`.

Unfold `Set.finrank at h2`. Simplify using `using h2)`. Consider the case `(have h2 := finrank_range_le_card (K := ℂ) W`. Unfold `Set.finrank at h2`. Simplify using `using h2)`.

Consider the case `(have h2 := rank_span_le_of_finite (R := ℂ) (Set.finite_range W)`. Conclude with `absurd h2 (by simp))`. Establish `hne : (Submodule.span ℂ (Set.range W)) ≠ ⊤`. Introduce `htop`. Rewrite `h1` using `[htop, finrank_top, Module.finrank_fin_fun]`.

Use linear arithmetic over natural numbers and integers. Establish `hne' : (Submodule.span ℂ (Set.range W)).restrictScalars ℝ ≠ ⊤`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Use `first`.

Consider the case `exact (Submodule.restrictScalars_eq_top_iff ℝ ℂ _).mp h`. Consider the case `exact Submodule.restrictScalars_injective ℝ ℂ (Fin (n + 1) → ℂ) (by rw [h]; rfl)`. Conclude with `MeasureTheory.Measure.addHaar_submodule volume _ hne'`.
-/
theorem volume_span_range_eq_zero (n : ℕ) (W : Fin n → Fin (n + 1) → ℂ) :
    volume ((Submodule.span ℂ (Set.range W) : Submodule ℂ (Fin (n + 1) → ℂ)) :
      Set (Fin (n + 1) → ℂ)) = 0 := by
  have h1 : Module.finrank ℂ (Submodule.span ℂ (Set.range W)) ≤ n := by
    first
    | simpa using finrank_span_range_le_card (R := ℂ) W
    | simpa using Submodule.finrank_span_range_le_card (R := ℂ) W
    | simpa using finrank_range_le_card (R := ℂ) W
    | (have h2 := finrank_range_le_card (R := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := finrank_range_le_card (K := ℂ) W
       unfold Set.finrank at h2
       simpa using h2)
    | (have h2 := rank_span_le_of_finite (R := ℂ) (Set.finite_range W)
       exact absurd h2 (by simp))
  have hne : (Submodule.span ℂ (Set.range W)) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, Module.finrank_fin_fun] at h1
    omega
  have hne' : (Submodule.span ℂ (Set.range W)).restrictScalars ℝ ≠ ⊤ := by
    intro h
    apply hne
    first
    | exact (Submodule.restrictScalars_eq_top_iff ℝ ℂ _).mp h
    | exact Submodule.restrictScalars_injective ℝ ℂ (Fin (n + 1) → ℂ) (by rw [h]; rfl)
  exact MeasureTheory.Measure.addHaar_submodule volume _ hne'

/- English proof (translation)
Establish `hli : ¬ LinearIndependent ℂ Z`. Introduce `h`. Establish `hu : IsUnit (Matrix.of Z)` using `Matrix.linearIndependent_rows_iff_isUnit.mp h`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hZ`. Establish `hex : ∃ i, Z i ∈ Submodule.span ℂ (Z '' (Set.univ \ {i}))`.

Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Apply `hli` to reduce the goal to its premises. Use `first`. Consider the case `exact linearIndependent_iff_not_mem_span.mpr hno`.

Consider the case `exact linearIndependent_iff_notMem_span.mpr hno`. Take `⟨i, hi⟩` from `hex`. Use `⟨i, ?_⟩` and prove the remaining obligations. Establish `himg : Z '' (Set.univ \ {i}) = Set.range fun j : Fin n => Z (i.succAbove j)`. Rewrite using `[show (fun j : Fin n => Z (i.succAbove j)) = Z ∘ i.succAbove from rfl, Set.range_comp, Fin.range_succAbove, Set.compl_eq_univ_diff]`.

Rewrite `hi` using `[himg]`. Conclude with `hi`.
-/
theorem exists_row_mem_span_of_det_eq_zero {n : ℕ} (Z : Fin (n + 1) → Fin (n + 1) → ℂ)
    (hZ : (Matrix.of Z).det = 0) :
    ∃ i : Fin (n + 1), Z i ∈ Submodule.span ℂ (Set.range fun j : Fin n => Z (i.succAbove j)) := by
  have hli : ¬ LinearIndependent ℂ Z := by
    intro h
    have hu : IsUnit (Matrix.of Z) := Matrix.linearIndependent_rows_iff_isUnit.mp h
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero hZ
  have hex : ∃ i, Z i ∈ Submodule.span ℂ (Z '' (Set.univ \ {i})) := by
    by_contra hno
    push_neg at hno
    apply hli
    first
    | exact linearIndependent_iff_not_mem_span.mpr hno
    | exact linearIndependent_iff_notMem_span.mpr hno
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  have himg : Z '' (Set.univ \ {i}) = Set.range fun j : Fin n => Z (i.succAbove j) := by
    rw [show (fun j : Fin n => Z (i.succAbove j)) = Z ∘ i.succAbove from rfl, Set.range_comp,
      Fin.range_succAbove, Set.compl_eq_univ_diff]
  rw [himg] at hi
  exact hi

/- English proof (translation)
Consider the cases of `N with`. Consider the case `zero`. Establish `h : {Z : Fin 0 → Fin 0 → ℂ | (Matrix.of Z).det = 0} = ∅`. Use extensionality with `Z`. Simplify using `[Matrix.det_isEmpty]`.

Rewrite using `[h, measure_empty]`. Consider the case `succ n`. Set `T : Set ((Fin (n + 1) → ℂ) × (Fin n → Fin (n + 1) → ℂ))` to `{p | p.1 ∈ Submodule.span ℂ (Set.range p.2)}`. Establish `hT : MeasurableSet T` using `measurableSet_mem_span_range n (n + 1)`. Establish `hsub : {Z : Fin (n + 1) → Fin (n + 1) → ℂ | (Matrix.of Z).det = 0} ⊆ ⋃ i : Fin (n + 1), (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℂ) i) ⁻¹' T`.

Introduce `Z hZ`. Take `⟨i, hi⟩` from `exists_row_mem_span_of_det_eq_zero Z hZ`. Conclude with `Set.mem_iUnion.2 ⟨i, hi⟩`. Use `measure_mono_null hsub (measure_iUnion_null fun i => ?_)` and prove the remaining obligations. Establish `mp` using `measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) i`.

Establish `h1` using `mp.measure_preimage hT.nullMeasurableSet`. Express the relevant statement in the definitionally equal form `(Measure.pi fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) _ = 0`. Rewrite using `[h1, Measure.prod_apply_symm hT]`. Conclude with `(lintegral_congr fun W => volume_span_range_eq_zero n W).trans lintegral_zero`.
-/
theorem volume_det_eq_zero :
    volume {Z : Fin N → Fin N → ℂ | (Matrix.of Z).det = 0} = 0 := by
  cases N with
  | zero =>
    have h : {Z : Fin 0 → Fin 0 → ℂ | (Matrix.of Z).det = 0} = ∅ := by
      ext Z
      simp [Matrix.det_isEmpty]
    rw [h, measure_empty]
  | succ n =>
    let T : Set ((Fin (n + 1) → ℂ) × (Fin n → Fin (n + 1) → ℂ)) :=
      {p | p.1 ∈ Submodule.span ℂ (Set.range p.2)}
    have hT : MeasurableSet T := measurableSet_mem_span_range n (n + 1)
    have hsub : {Z : Fin (n + 1) → Fin (n + 1) → ℂ | (Matrix.of Z).det = 0} ⊆
        ⋃ i : Fin (n + 1),
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Fin (n + 1) → ℂ) i) ⁻¹' T := by
      intro Z hZ
      obtain ⟨i, hi⟩ := exists_row_mem_span_of_det_eq_zero Z hZ
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
    have mp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) i
    have h1 := mp.measure_preimage hT.nullMeasurableSet
    change (Measure.pi fun _ : Fin (n + 1) => (volume : Measure (Fin (n + 1) → ℂ))) _ = 0
    rw [h1, Measure.prod_apply_symm hT]
    exact (lintegral_congr fun W => volume_span_range_eq_zero n W).trans lintegral_zero

end ReciprocityTheory.ChartRestriction.DS
