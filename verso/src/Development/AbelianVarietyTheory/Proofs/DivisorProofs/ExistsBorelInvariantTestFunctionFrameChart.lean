import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarChart
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume GlobalTheory.FlagQuotHaar
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar.TestFn

/- English proof (translation)
Introduce `E _ _ _ r X`. Establish `ho : IsOrth X (baseFr X)` using `fun τ => baseFr_mem X τ`. Establish `h0` using `IW.zero_mem_OmF X (baseFr X) ho`. Take `⟨ε, hε, hball⟩` from `Metric.nhds_basis_closedBall.mem_iff.mp ((OntoB.isOpen_OmF X (baseFr X)).mem_nhds h0)`. Use `set A : Set (V (nd X)) := Metric.closedBall 0 ε with hAdef`.

Establish `hA : MeasurableSet A` using `measurableSet_closedBall`. Establish `hS` using `GlobalTheory.Unfold.measurableSet_satFrames X ho hA hball`. Use `⟨(GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator 1, measurable_one.indicator hS, ?_, ?_⟩` and prove the remaining obligations. Introduce `x _ b hb`. Distinguish the cases in `hx : x ∈ GlobalTheory.Unfold.satFrames X (baseFr X) A`.

Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mpr hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem fun h => hx ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mp h)]`. Establish `heq : (fun z => (GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X (baseFr X) z)) = A.indicator 1`. Use function extensionality and compare the values at `z`.

Distinguish the cases in `hz : z ∈ A`. Rewrite using `[Set.indicator_of_mem hz, Set.indicator_of_mem ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mpr hz)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem hz, Set.indicator_of_notMem fun h => hz ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mp h)]`. Rewrite using `[heq, lintegral_indicator_one hA]`.

Use `⟨?_, (GlobalTheory.SatFin.muF_lt_top_of_isCompact X (baseFr X) (isCompact_closedBall _ _) hball).ne⟩` and prove the remaining obligations. Unfold `muF`. Establish `hmeas : AEMeasurable (fun z => ENNReal.ofReal (densF X (baseFr X) z)) (volume.restrict (OmF X (baseFr X)))` using `ENNReal.measurable_ofReal.comp_aemeasurable (OntoB.densF_continuousOn.aemeasurable (OntoB.isOpen_OmF X (baseFr X)).measurableSet)`. Rewrite using `[Ne, withDensity_apply_eq_zero' hmeas]`. Establish `hset : {z | ENNReal.ofReal (densF X (baseFr X) z) ≠ 0} ∩ A = A`.

Use `Set.inter_eq_right.mpr fun z hz => ?_` and prove the remaining obligations. Use `show ENNReal.ofReal (densF X (baseFr X) z) ≠ 0`. Conclude with `(ENNReal.ofReal_pos.mpr (OntoB.densF_pos (hball hz))).ne'`. Rewrite using `[hset, Measure.restrict_apply hA, Set.inter_eq_left.mpr hball]`. Conclude with `(Metric.measure_closedBall_pos volume 0 hε).ne'`.
-/
theorem exists_invariant_test : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r), ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ := by
  intro E _ _ _ r X
  have ho : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  have h0 := IW.zero_mem_OmF X (baseFr X) ho
  obtain ⟨ε, hε, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((OntoB.isOpen_OmF X (baseFr X)).mem_nhds h0)
  set A : Set (V (nd X)) := Metric.closedBall 0 ε with hAdef
  have hA : MeasurableSet A := measurableSet_closedBall
  have hS := GlobalTheory.Unfold.measurableSet_satFrames X ho hA hball
  refine ⟨(GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator 1, measurable_one.indicator hS, ?_, ?_⟩
  · intro x _ b hb
    by_cases hx : x ∈ GlobalTheory.Unfold.satFrames X (baseFr X) A
    · rw [Set.indicator_of_mem hx,
        Set.indicator_of_mem ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mpr hx)]
      rfl
    · rw [Set.indicator_of_notMem hx,
        Set.indicator_of_notMem fun h => hx ((GlobalTheory.Unfold.rmul_mem_satFrames_iff X _ A x hb).mp h)]
  have heq : (fun z => (GlobalTheory.Unfold.satFrames X (baseFr X) A).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (cpt X (baseFr X) z)) = A.indicator 1 := by
    funext z
    by_cases hz : z ∈ A
    · rw [Set.indicator_of_mem hz,
        Set.indicator_of_mem ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mpr hz)]
      rfl
    · rw [Set.indicator_of_notMem hz,
        Set.indicator_of_notMem fun h => hz ((GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho A z).mp h)]
  rw [heq, lintegral_indicator_one hA]
  refine ⟨?_, (GlobalTheory.SatFin.muF_lt_top_of_isCompact X (baseFr X) (isCompact_closedBall _ _) hball).ne⟩
  unfold muF
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (densF X (baseFr X) z))
      (volume.restrict (OmF X (baseFr X))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (OntoB.densF_continuousOn.aemeasurable (OntoB.isOpen_OmF X (baseFr X)).measurableSet)
  rw [Ne, withDensity_apply_eq_zero' hmeas]
  have hset : {z | ENNReal.ofReal (densF X (baseFr X) z) ≠ 0} ∩ A = A := by
    refine Set.inter_eq_right.mpr fun z hz => ?_
    show ENNReal.ofReal (densF X (baseFr X) z) ≠ 0
    exact (ENNReal.ofReal_pos.mpr (OntoB.densF_pos (hball hz))).ne'
  rw [hset, Measure.restrict_apply hA, Set.inter_eq_left.mpr hball]
  exact (Metric.measure_closedBall_pos volume 0 hε).ne'

end GlobalTheory.FlagQuotHaar.TestFn
