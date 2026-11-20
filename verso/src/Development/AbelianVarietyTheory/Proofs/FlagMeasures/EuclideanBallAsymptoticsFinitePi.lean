import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasEuclideanBallVolumeSublevelAsymptoticsProdStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem IsRadial.comp_measurableEquiv {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) {q : X → ℝ} {p : Y → ℝ} {d : ℕ}
    (hq : ∀ x, q x = p (e x)) (h : IsRadial ν p d) : IsRadial μ q d := by
  unfold IsRadial at *
  refine h.congr fun r => ?_
  rw [← he.measure_preimage_equiv]
  simp only [hq, Set.preimage_ofPred_eq]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isRadial_pi : ∀ (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i))
    [∀ i, SigmaFinite (μ i)] (q : ∀ i, X i → ℝ) (d : Fin a → ℕ), (∀ i, Measurable (q i)) →
    (∀ i x, 0 ≤ q i x) → (∀ i, IsRadial (μ i) (q i) (d i)) →
    IsRadial (Measure.pi μ) (fun x => ∑ i, q i (x i)) (∑ i, d i) := by
  intro a
  induction a with
  | zero =>
    intro X _ μ _ q d _ _ _
    rw [Fin.sum_univ_zero]
    unfold IsRadial
    rw [volume_euclideanSpace_eq_dirac, Measure.dirac_apply_of_mem (Metric.mem_ball_self one_pos)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : (0 : ℝ) ≤ r := le_of_lt hr
    rw [Measure.pi_of_empty, Measure.dirac_apply_of_mem (by simpa using hr')]
    simp
  | succ a ih =>
    intro X _ μ _ q d hm h0 hr
    have h := GlobalTheory.T.hasEuclideanBallVolumeSublevelAsymptotics_prod _ _ (μ 0) (Measure.pi fun j => μ (Fin.succAbove 0 j)) (q 0)
      (fun x => ∑ j, q (Fin.succAbove 0 j) (x j)) (d 0) (∑ j, d (Fin.succAbove 0 j)) (hm 0)
      (Finset.measurable_sum _ fun j _ => (hm _).comp (measurable_pi_apply j)) (h0 0)
      (fun y => Finset.sum_nonneg fun j _ => h0 _ _) (hr 0)
      (ih _ _ _ _ (fun j => hm _) (fun j => h0 _) fun j => hr _)
    rw [Fin.sum_univ_succAbove d 0]
    exact h.comp_measurableEquiv _ (measurePreserving_piFinSuccAbove μ 0)
      fun x => Fin.sum_univ_succAbove (fun i => q i (x i)) 0

end GlobalTheory.LeviIso
