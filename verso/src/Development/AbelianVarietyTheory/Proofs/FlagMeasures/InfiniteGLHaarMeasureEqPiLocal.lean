import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
open scoped ENNReal

noncomputable section

namespace GlobalTheory.HaarPi

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hp` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm`. Rewrite using `[← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`.

Establish `hrw : ∀ z : E × (Fin n → E), ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm z i) = f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)`. Introduce `z`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[MeasurableEquiv.piFinSuccAbove_symm_apply]`. Repeatedly rewrite using `[hrw]`.

Rewrite using `[lintegral_prod_mul (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i)) (hf 0).aemeasurable, ih (fun i => f i.succ) (fun i => hf i.succ), Fin.prod_univ_succ]`. Conclude with `(Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable`.
-/
theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
    have hrw : ∀ z : E × (Fin n → E),
        ∏ i, f i ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm z i) =
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i) := by
      intro z
      rw [Fin.prod_univ_succ]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp_rw [hrw]
    rw [lintegral_prod_mul (f := f 0) (g := fun y : Fin n → E => ∏ i : Fin n, f i.succ (y i))
      (hf 0).aemeasurable, ih (fun i => f i.succ) (fun i => hf i.succ),
      Fin.prod_univ_succ]
    · exact (Finset.measurable_prod _ fun i _ =>
        (hf i.succ).comp (measurable_pi_apply i)).aemeasurable

/- English proof (translation)
Use `set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm`. Establish `hp` using `measurePreserving_piCongrLeft (fun _ : ι => μ) e`. Rewrite using `[← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]`. Establish `hrw : ∀ y : Fin (Fintype.card ι) → E, ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k)`. Introduce `y`.

Rewrite using `[← e.prod_comp]`. Simplify using `[MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]`. Repeatedly rewrite using `[hrw]`. Rewrite using `[lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]`. Conclude with `e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)`.
-/
theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  set e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  have hrw : ∀ y : Fin (Fintype.card ι) → E,
      ∏ i, f i (MeasurableEquiv.piCongrLeft (fun _ : ι => E) e y i) = ∏ k, f (e k) (y k) := by
    intro y
    rw [← e.prod_comp]
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp_rw [hrw]
  rw [lintegral_pi_fin _ μ (fun k => f (e k)) (fun k => hf (e k))]
  exact e.prod_comp (fun i => ∫⁻ t, f i t ∂μ)

/- English proof (translation)
Use `Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_` and prove the remaining obligations. Establish `hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x = ∏ i, (s i).indicator f (x i)`. Introduce `x`. Distinguish the cases in `hx : x ∈ Set.univ.pi s`. Rewrite using `[Set.indicator_of_mem hx]`.

Conclude with `Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) f).symm`. Rewrite using `[Set.indicator_of_notMem hx]`. Simplify using `only [Set.mem_univ_pi, not_forall] at hx`. Take `⟨i, hi⟩` from `hx`. Conclude with `(Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm`.

Rewrite using `[withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]`. Repeatedly rewrite using `[hind]`. Rewrite using `[lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator (hs i), withDensity_apply _ (hs i)]`.
-/
theorem pi_withDensity {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : E → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_
  have hind : ∀ x : ι → E, (Set.univ.pi s).indicator (fun x => ∏ i, f (x i)) x =
      ∏ i, (s i).indicator f (x i) := by
    intro x
    by_cases hx : x ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ =>
        (Set.indicator_of_mem (Set.mem_univ_pi.1 hx i) f).symm
    · rw [Set.indicator_of_notMem hx]
      simp only [Set.mem_univ_pi, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi f)).symm
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hind]
  rw [lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/- English proof (translation)
Introduce `E _ _ j`. Use `set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)`. Establish `hF : Measurable F`. Establish `hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det` using `continuous_id.matrix_det`. Conclude with `ENNReal.measurable_ofReal.comp (((hc.norm.pow 2).measurable.inv).pow_const j)`.

Establish `: SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F)` using `inferInstanceAs (SigmaFinite (haarLoc j))`. Establish `hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F` using `rfl`. Simplify using `only [hloc]`. Rewrite using `[pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Simplify using `only [F, detNorm]`. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]`. Use `congr 1`. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_pow]`.
-/
theorem haarGL_eq_pi : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ), haarGL E j = (Measure.pi fun _ : InfinitePlace E => haarLoc j : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) := by
  intro E _ _ j
  set F : (Fin j → Fin j → ℂ) → ℝ≥0∞ := fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)
  have hF : Measurable F := by
    have hc : Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := continuous_id.matrix_det
    exact ENNReal.measurable_ofReal.comp
      (((hc.norm.pow 2).measurable.inv).pow_const j)
  have : SigmaFinite ((volume : Measure (Fin j → Fin j → ℂ)).withDensity F) :=
    inferInstanceAs (SigmaFinite (haarLoc j))
  have hloc : haarLoc j = (volume : Measure (Fin j → Fin j → ℂ)).withDensity F := rfl
  simp only [hloc]
  rw [pi_withDensity (ι := InfinitePlace E) volume F hF, ← volume_pi, haarGL]
  congr 1
  funext x
  simp only [F, detNorm]
  rw [← ENNReal.ofReal_prod_of_nonneg fun w _ => by positivity]
  congr 1
  rw [← Finset.prod_inv_distrib, ← Finset.prod_pow]

end GlobalTheory.HaarPi
