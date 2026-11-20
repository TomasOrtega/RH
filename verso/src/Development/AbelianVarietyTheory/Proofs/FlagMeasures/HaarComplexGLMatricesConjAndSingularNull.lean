import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
Use `fun_prop`.
-/
private lemma continuous_det_of' (j : ℕ) :
    Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := by
  fun_prop

/- English proof (translation)
Establish `hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det` using `(continuous_det_of' j).measurable`. Conclude with `ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)`.
-/
theorem measurable_haarLoc_density (j : ℕ) :
    Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) := by
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_det_of' j).measurable
  exact ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)

/- English proof (translation)
Use `⟨hf.measurable, ?_⟩` and prove the remaining obligations. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs]`. Use `conv_rhs => rw [← hf.map_eq]`. Rewrite using `[setLIntegral_map hs hg hf.measurable]`.

Simplify using `only [hfg]`.
-/
theorem measurePreserving_withDensity_of_invariant {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) {g : X → ENNReal} (hg : Measurable g) (hfg : ∀ x, g (f x) = g x) :
    MeasurePreserving f (μ.withDensity g) (μ.withDensity g) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs, withDensity_apply _ (hf.measurable hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← hf.map_eq]
  rw [setLIntegral_map hs hg hf.measurable]
  simp only [hfg]

/- English proof (translation)
Introduce `j`. Establish `hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det` using `(show Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det by fun_prop).measurable`. Prove the components needed by the constructor for the conclusion. Establish `hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume`. Establish `h` using `Complex.conjLIE.measurePreserving`.

Establish `e : (⇑Complex.conjLIE : ℂ → ℂ) = ⇑(starRingEnd ℂ)` using `funext Complex.conjLIE_apply`. Rewrite `h` using `[e]`. Then use the resulting hypothesis. Establish `hv : MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (volume : Measure (Fin j → Fin j → ℂ)) volume` using `volume_preserving_pi fun _ => volume_preserving_pi fun _ => hc`. Use `measurePreserving_withDensity_of_invariant hv (measurable_haarLoc_density j) ?_` and prove the remaining obligations. Introduce `x`.

Establish `hdet : (Matrix.of fun r s => starRingEnd ℂ (x r s)).det = starRingEnd ℂ (Matrix.of x).det` using `((starRingEnd ℂ).map_det (Matrix.of x)).symm`. Simplify using `only [hdet, Complex.norm_conj]`. Establish `hS : MeasurableSet {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}` using `measurableSet_eq_fun hd measurable_const`. Rewrite using `[haarLoc, withDensity_apply _ hS, ← lintegral_indicator hS]`. Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases.

Simplify using the standard rewrite rules. Establish `: ({x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}.indicator fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)) = 0`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : (Matrix.of x).det = 0`. Simplify using `[hx, zero_pow hj.ne']`.

Simplify using `[Set.indicator_of_notMem (show x ∉ {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} from hx)]`. Rewrite using `[this, Pi.zero_def, lintegral_zero]`.
-/
theorem haarLoc_conj_and_null : ∀ j : ℕ, MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s)) (haarLoc j) (haarLoc j) ∧ haarLoc j {x | (Matrix.of x).det = 0} = 0 := by
  intro j
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (show Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det by fun_prop).measurable
  constructor
  ·
    have hc : MeasurePreserving (starRingEnd ℂ) (volume : Measure ℂ) volume := by
      have h := Complex.conjLIE.measurePreserving
      have e : (⇑Complex.conjLIE : ℂ → ℂ) = ⇑(starRingEnd ℂ) := funext Complex.conjLIE_apply
      rwa [e] at h
    have hv : MeasurePreserving (fun (x : Fin j → Fin j → ℂ) (r s : Fin j) => starRingEnd ℂ (x r s))
        (volume : Measure (Fin j → Fin j → ℂ)) volume :=
      volume_preserving_pi fun _ => volume_preserving_pi fun _ => hc
    refine measurePreserving_withDensity_of_invariant hv (measurable_haarLoc_density j) ?_
    intro x
    have hdet : (Matrix.of fun r s => starRingEnd ℂ (x r s)).det = starRingEnd ℂ (Matrix.of x).det :=
      ((starRingEnd ℂ).map_det (Matrix.of x)).symm
    simp only [hdet, Complex.norm_conj]
  ·
    have hS : MeasurableSet {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} :=
      measurableSet_eq_fun hd measurable_const
    rw [haarLoc, withDensity_apply _ hS, ← lintegral_indicator hS]
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have : ({x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0}.indicator
          fun x => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j)) = 0 := by
        funext x
        by_cases hx : (Matrix.of x).det = 0
        · simp [hx, zero_pow hj.ne']
        · simp [Set.indicator_of_notMem (show x ∉ {x : Fin j → Fin j → ℂ | (Matrix.of x).det = 0} from hx)]
      rw [this, Pi.zero_def, lintegral_zero]

end GlobalTheory.LeviIso
