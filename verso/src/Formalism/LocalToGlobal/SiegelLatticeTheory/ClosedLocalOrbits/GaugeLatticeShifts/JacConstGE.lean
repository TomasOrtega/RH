import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGEB
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstWb
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBH
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

/- English proof (translation)
Take `⟨hσ, h0, hconc, hl⟩` from `h`. Use `hσ` as an intermediate fact. Use `⟨inferInstance, ?_, ?_, fun s hs => ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `h0` to reduce the goal to its premises.

Conclude with `(smul_eq_zero.1 h).resolve_left hc.ne'`. Rewrite using `[Measure.smul_apply, hconc, smul_zero]`. Rewrite using `[Measure.map_smul, hl s hs]`.
-/
theorem isHaarOn_smul {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {ν : Measure (Mt k r)} (h : Formalism.MainNotions.S.IsHaarOn S ν) {c : NNReal} (hc : 0 < c) :
    Formalism.MainNotions.S.IsHaarOn S (c • ν) := by
  obtain ⟨hσ, h0, hconc, hl⟩ := h
  have := hσ
  refine ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩
  · intro h
    apply h0
    exact (smul_eq_zero.1 h).resolve_left hc.ne'
  · rw [Measure.smul_apply, hconc, smul_zero]
  · rw [Measure.map_smul, hl s hs]

/- English proof (translation)
Rewrite using `[Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]`.
-/
theorem toReal_smul_apply {α : Type*} [MeasurableSpace α] (c : NNReal) (ν : Measure α) (A : Set α) :
    ((c • ν) A).toReal = (c : ℝ) * (ν A).toReal := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

/- English proof (translation)
Introduce `k r`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Conclude with `hU r`. Take `⟨z, z', μW, μW', a, a', μsec, D⟩` from `hD k r hk`. Take `⟨ν, hν, hνφ⟩` from `hRW k r z z' μW μW' a a' μsec D`.

Establish `hw` using `wbConst_pos (k := k) D.T_pos D.T'_pos D.a_pos D.a'_pos`. Use `set w := wbConst k (Tz k r z) (Tz k r z') a a' with hwdef`. Use `⟨(Real.toNNReal w) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 hw), ?_⟩` and prove the remaining obligations. Establish `hlim` using `(hLW k r z z' μW μW' a a' μsec D).const_mul w`. Rewrite `hlim` using `[mul_inv_cancel₀ hw.ne']`.

Use `hlim.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ρ hρ`. Take `⟨hm, he⟩` from `hSW k r z z' ν μW μW' a a' μsec D hν ρ hρ`. Establish `h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂ν = ν (mBall k r z z' μsec ρ)` using `lintegral_indicator_one hm`. Establish `h2` using `hνφ _ (measurable_one.indicator hm)`.

Rewrite `h2` using `[h1, he]`. Use `show _ = ((Real.toNNReal w • ν) (bBall k r ρ)).toReal / bVol k r ρ`. Rewrite using `[toReal_smul_apply, h2, Real.coe_toNNReal _ hw.le, mul_div_assoc]`.
-/
theorem gaugeWb_of (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hSW : GaugeShiftW) (hLW : RhsWLim) :
    ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μ := by
  intro k r
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hU r
  obtain ⟨z, z', μW, μW', a, a', μsec, D⟩ := hD k r hk
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  have hw := wbConst_pos (k := k) D.T_pos D.T'_pos D.a_pos D.a'_pos
  set w := wbConst k (Tz k r z) (Tz k r z') a a' with hwdef
  refine ⟨(Real.toNNReal w) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 hw), ?_⟩
  have hlim := (hLW k r z z' μW μW' a a' μsec D).const_mul w
  rw [mul_inv_cancel₀ hw.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hSW k r z z' ν μW μW' a a' μsec D hν ρ hρ
  have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂ν = ν (mBall k r z z' μsec ρ) :=
    lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal w • ν) (bBall k r ρ)).toReal / bVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ hw.le, mul_div_assoc]

/- English proof (translation)
Introduce `k r`. Establish `hb` using `gaugeWb_of hRW hD hU hSW hLW k r`. Use `⟨?_, hb⟩` and prove the remaining obligations. Take `⟨μb, hμb⟩` from `hb`. Take `⟨ν, hν, hνφ⟩` from `hR k r μb hμb`.

Establish `h2r : (0 : ℝ) < 2 ^ r` using `by positivity`. Use `⟨(Real.toNNReal (2 ^ r)) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 h2r), ?_⟩` and prove the remaining obligations. Establish `hlim` using `(hL k r μb hμb).const_mul ((2 : ℝ) ^ r)`. Rewrite `hlim` using `[mul_inv_cancel₀ h2r.ne']`. Use `hlim.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [self_mem_nhdsWithin] with ρ hρ`. Take `⟨hm, he⟩` from `hS k r ν hν ρ hρ`. Establish `h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂ν = ν (wBall k r ρ)` using `lintegral_indicator_one hm`. Establish `h2` using `hνφ _ (measurable_one.indicator hm)`. Rewrite `h2` using `[h1, he]`.

Use `show _ = ((Real.toNNReal (2 ^ r) • ν) (gBall k r ρ)).toReal / gVol k r ρ`. Rewrite using `[toReal_smul_apply, h2, Real.coe_toNNReal _ h2r.le, mul_div_assoc]`.
-/
theorem gaugeExists_of (hR : RhsHaar) (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hS : GaugeShift)
    (hSW : GaugeShiftW) (hL : RhsLim) (hLW : RhsWLim) : GaugeExists := by
  intro k r
  have hb := gaugeWb_of hRW hD hU hSW hLW k r
  refine ⟨?_, hb⟩
  obtain ⟨μb, hμb⟩ := hb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  refine ⟨(Real.toNNReal (2 ^ r)) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 h2r), ?_⟩
  have hlim := (hL k r μb hμb).const_mul ((2 : ℝ) ^ r)
  rw [mul_inv_cancel₀ h2r.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hS k r ν hν ρ hρ
  have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂ν = ν (wBall k r ρ) := lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal (2 ^ r) • ν) (gBall k r ρ)).toReal / gVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ h2r.le, mul_div_assoc]

/- English proof (translation)
Introduce `k r μ μb hμ hμb`. Take `⟨ν, hν, hνφ⟩` from `hR k r μb hμb`. Take `⟨ν0, h0⟩` from `Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r`. Take `⟨c1, hc1, hc1', e1⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hμ.1`. Take `⟨c2, hc2, hc2', e2⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hν`.

Establish `hne : c1 / c2 ≠ ∞` using `(ENNReal.div_lt_top hc1' hc2).ne`. Use `⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.div_mul_cancel hc2 hc2']`.
-/
theorem iterGauge_of (hR : RhsHaar) : IterGauge := by
  intro k r μ μb hμ hμb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hμ.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

/- English proof (translation)
Introduce `k r z z' μb μW μW' a a' μsec D hμb`. Take `⟨ν, hν, hνφ⟩` from `hRW k r z z' μW μW' a a' μsec D`. Take `⟨ν0, h0⟩` from `Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r`. Take `⟨c1, hc1, hc1', e1⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hμb.1`. Take `⟨c2, hc2, hc2', e2⟩` from `Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hν`.

Establish `hne : c1 / c2 ≠ ∞` using `(ENNReal.div_lt_top hc1' hc2).ne`. Use `⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne, fun φ hφ => ?_⟩` and prove the remaining obligations. Rewrite using `[ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc, ENNReal.div_mul_cancel hc2 hc2']`.
-/
theorem rankGauge_of (hRW : RhsWHaar) : RankGauge := by
  intro k r z z' μb μW μW' a a' μsec D hμb
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hμb.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

/- English proof (translation)
The claim follows from `bruhatHaar_of_iterGauge (iterGauge_of hR) hS hW hV`.
-/
theorem bruhatHaar_of_rhsHaar (hR : RhsHaar) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_iterGauge (iterGauge_of hR) hS hW hV

/- English proof (translation)
The claim follows from `wbHaar_of (rankGauge_of hRW) hSW hLW`.
-/
theorem wbHaar_of_rhsWHaar (hRW : RhsWHaar) (hSW : GaugeShiftW) (hLW : RhsWLim) : WbHaar :=
  wbHaar_of (rankGauge_of hRW) hSW hLW

end Formalism.L2.SG.Pf.GE
