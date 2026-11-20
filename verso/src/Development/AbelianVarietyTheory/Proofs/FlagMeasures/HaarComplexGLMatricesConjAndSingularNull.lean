import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
A detailed English derivation is pending.
-/
private lemma continuous_det_of' (j : ℕ) :
    Continuous fun x : Fin j → Fin j → ℂ => (Matrix.of x).det := by
  fun_prop

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem measurable_haarLoc_density (j : ℕ) :
    Measurable fun x : Fin j → Fin j → ℂ => ENNReal.ofReal ((‖(Matrix.of x).det‖ ^ 2)⁻¹ ^ j) := by
  have hd : Measurable fun x : Fin j → Fin j → ℂ => (Matrix.of x).det :=
    (continuous_det_of' j).measurable
  exact ENNReal.measurable_ofReal.comp ((hd.norm.pow_const 2).inv.pow_const j)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
