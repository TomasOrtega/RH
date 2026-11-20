import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

/- English proof (translation)
Use `conv_lhs => rw [← h]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]`.
-/
theorem inv_fix {b : Mat k r} (hb : IsUnit b.det) {v : Fin (2 * r + k + 1) → ℂ} (h : b *ᵥ v = v) :
    b⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← h]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hb, Matrix.one_mulVec]

/- English proof (translation)
Take `⟨hU, hfix, hz⟩` from `hb`. Establish `hu` using `HU.isUnit_of_uh hU`. Conclude with `⟨HU.uh_inv hU, fun a => ⟨inv_fix hu (hfix a).1, inv_fix hu (hfix a).2⟩, inv_fix hu hz⟩`.
-/
theorem uwset_inv {b : Mat k r} (hb : b ∈ UWset k r z') : b⁻¹ ∈ UWset k r z' := by
  obtain ⟨hU, hfix, hz⟩ := hb
  have hu := HU.isUnit_of_uh hU
  exact ⟨HU.uh_inv hU, fun a => ⟨inv_fix hu (hfix a).1, inv_fix hu (hfix a).2⟩, inv_fix hu hz⟩

/- English proof (translation)
Establish `hbi : b⁻¹ ∈ UWset k r z'` using `uwset_inv hb`. Establish `hu : IsUnit (b⁻¹).det` using `HU.isUnit_of_uh hbi.1`. Establish `hbu : IsUnit b.det` using `HU.isUnit_of_uh hb.1`. Establish `hmap : μW'.map (lmulM b⁻¹) = μW'` using `hW.2.2.2 _ hbi`. Establish `key : ∀ h' : Mt k r, M * (Matrix.of h')⁻¹ * b = M * (Matrix.of (lmulE b⁻¹ hu h'))⁻¹`.

Introduce `h'`. Express the relevant statement in the definitionally equal form `M * (Matrix.of h')⁻¹ * b = M * (b⁻¹ * Matrix.of h')⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hbu, mul_assoc]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun h' => ?_` and prove the remaining obligations.

Simplify using `only [key h']`. Use `_ = ∫⁻ y, φ (fun i j => (M * (Matrix.of y)⁻¹) i j) ∂(μW'.map (lmulE b⁻¹ hu)) := by rw [lintegral_map_equiv]`. Use `_ = ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by`. Rewrite using `[show ⇑(lmulE b⁻¹ hu) = lmulM b⁻¹ from rfl, hmap]`.
-/
theorem inner_r (hW : IsHaarOn (UWset k r z') μW') (M : Mat k r) (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ)
    (b : Mat k r) (hb : b ∈ UWset k r z') :
    ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW' =
      ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
  have hbi : b⁻¹ ∈ UWset k r z' := uwset_inv hb
  have hu : IsUnit (b⁻¹).det := HU.isUnit_of_uh hbi.1
  have hbu : IsUnit b.det := HU.isUnit_of_uh hb.1
  have hmap : μW'.map (lmulM b⁻¹) = μW' := hW.2.2.2 _ hbi
  have key : ∀ h' : Mt k r, M * (Matrix.of h')⁻¹ * b = M * (Matrix.of (lmulE b⁻¹ hu h'))⁻¹ := by
    intro h'
    change M * (Matrix.of h')⁻¹ * b = M * (b⁻¹ * Matrix.of h')⁻¹
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hbu, mul_assoc]
  calc ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹ * b) i j) ∂μW'
      = ∫⁻ h', (fun y : Mt k r => φ (fun i j => (M * (Matrix.of y)⁻¹) i j)) (lmulE b⁻¹ hu h') ∂μW' := by
        refine lintegral_congr fun h' => ?_
        simp only [key h']
    _ = ∫⁻ y, φ (fun i j => (M * (Matrix.of y)⁻¹) i j) ∂(μW'.map (lmulE b⁻¹ hu)) :=
        by rw [lintegral_map_equiv]
    _ = ∫⁻ h', φ (fun i j => (M * (Matrix.of h')⁻¹) i j) ∂μW' := by
        rw [show ⇑(lmulE b⁻¹ hu) = lmulM b⁻¹ from rfl, hmap]

/- English proof (translation)
Unfold `rhsW`. Use `lintegral_congr fun ζ => ?_` and prove the remaining obligations. Use `congr 1`. Use `lintegral_congr fun h => ?_` and prove the remaining obligations. Conclude with `inner_r hd.haarW' _ φ hφ b hb`.
-/
theorem rhsW_rmul (hd : WbData k r z z' μW μW' a a' μsec) (b : Mat k r) (hb : b ∈ UWset k r z')
    (φ : Mt k r → ℝ≥0∞) (hφ : Measurable φ) :
    rhsW k r z z' μW μW' μsec (fun x => φ (rmulM b x)) = rhsW k r z z' μW μW' μsec φ := by
  unfold rhsW
  refine lintegral_congr fun ζ => ?_
  congr 1
  refine lintegral_congr fun h => ?_
  exact inner_r hd.haarW' _ φ hφ b hb

/- English proof (translation)
Introduce `k r z z' μW μW' a a' μsec hd b hb`. Establish `hm : Measurable (rmulM b : Mt k r → Mt k r)` using `(rmulM_cont b).measurable`. Use extensionality with `s hs`. Rewrite using `[Measure.map_apply hm hs]`. Establish `hi : Measurable (s.indicator (1 : Mt k r → ℝ≥0∞))` using `measurable_one.indicator hs`.

Establish `e1` using `ZetaZeros.repr hd (s.indicator 1) hi`. Establish `e2` using `ZetaZeros.repr hd (fun x => s.indicator 1 (rmulM b x)) (hi.comp hm)`. Establish `e3` using `rhsW_rmul hd b hb (s.indicator 1) hi`. Rewrite `e1` using `[lintegral_indicator_one hs]`. Establish `e4 : ∫⁻ x, s.indicator 1 (rmulM b x) ∂(nuR k r z z' μW μW' μsec) = nuR k r z z' μW μW' μsec (rmulM b ⁻¹' s)`.

Rewrite using `[← lintegral_indicator_one (hm hs)]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Simplify using `only [Set.indicator, Pi.one_apply]`. Both sides reduce to the same expression. Rewrite using `[← e4, ← e2, e3, e1]`.
-/
theorem rInvNu : RInvNu := by
  intro k r z z' μW μW' a a' μsec hd b hb
  have hm : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
  ext s hs
  rw [Measure.map_apply hm hs]
  have hi : Measurable (s.indicator (1 : Mt k r → ℝ≥0∞)) := measurable_one.indicator hs
  have e1 := ZetaZeros.repr hd (s.indicator 1) hi
  have e2 := ZetaZeros.repr hd (fun x => s.indicator 1 (rmulM b x)) (hi.comp hm)
  have e3 := rhsW_rmul hd b hb (s.indicator 1) hi
  rw [lintegral_indicator_one hs] at e1
  have e4 : ∫⁻ x, s.indicator 1 (rmulM b x) ∂(nuR k r z z' μW μW' μsec) =
      nuR k r z z' μW μW' μsec (rmulM b ⁻¹' s) := by
    rw [← lintegral_indicator_one (hm hs)]
    refine lintegral_congr fun x => ?_
    simp only [Set.indicator, Pi.one_apply]
    rfl
  rw [← e4, ← e2, e3, e1]

end PI.RhsWLim.W.RI
