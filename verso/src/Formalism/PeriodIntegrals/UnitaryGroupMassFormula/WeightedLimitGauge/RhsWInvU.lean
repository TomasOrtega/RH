import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvR
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvD
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsWInvO

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

/- English proof (translation)
Establish `hg : Measurable (· * g : G → G)` using `measurable_mul_const g`. Establish `hL : (ν.map (· * g)).IsMulLeftInvariant`. Use `⟨fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_map (measurable_const_mul h) hg]`. Establish `e : ((h * ·) ∘ (· * g) : G → G) = (· * g) ∘ (h * ·)` using `funext fun x => (mul_assoc h x g).symm`.

Rewrite using `[e, ← Measure.map_map hg (measurable_const_mul h), map_mul_left_eq_self]`. Establish `hU : (ν.map (· * g)) univ = ν univ`. Rewrite using `[Measure.map_apply hg MeasurableSet.univ, preimage_univ]`. Establish `hu0 : ν univ ≠ 0` using `fun h => h0 (Measure.measure_univ_eq_zero.1 h)`. Establish `hfin : IsFiniteMeasure (ν.map (· * g))` using `inferInstance`.

Rewrite using `[measure_eq_div_smul (ν.map (· * g)) ν (s := univ) hu0 (measure_ne_top ν univ), hU, ENNReal.div_self hu0 (measure_ne_top ν univ), one_smul]`.
-/
theorem fin_right {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [IsFiniteMeasure ν] [ν.IsMulLeftInvariant] (h0 : ν ≠ 0)
    (g : G) : ν.map (· * g) = ν := by
  have hg : Measurable (· * g : G → G) := measurable_mul_const g
  have hL : (ν.map (· * g)).IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    rw [Measure.map_map (measurable_const_mul h) hg]
    have e : ((h * ·) ∘ (· * g) : G → G) = (· * g) ∘ (h * ·) := funext fun x => (mul_assoc h x g).symm
    rw [e, ← Measure.map_map hg (measurable_const_mul h), map_mul_left_eq_self]
  have hU : (ν.map (· * g)) univ = ν univ := by
    rw [Measure.map_apply hg MeasurableSet.univ, preimage_univ]
  have hu0 : ν univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 h)
  have hfin : IsFiniteMeasure (ν.map (· * g)) := inferInstance
  rw [measure_eq_div_smul (ν.map (· * g)) ν (s := univ) hu0 (measure_ne_top ν univ), hU,
    ENNReal.div_self hu0 (measure_ne_top ν univ), one_smul]

/- English proof (translation)
Introduce `k r z μ hW hfin b hb`. Establish `: SigmaFinite μ` using `hW.1`. Establish `hl` using `nuH_left hW`. Establish `hmass : (μ.comap (jH z)) univ = μ univ` using `by conv_rhs => rw [← map_jH hW]`. Rewrite using `[Measure.map_apply (jH_memb z).measurable MeasurableSet.univ, preimage_univ]`.

Establish `: IsFiniteMeasure (μ.comap (jH z))` using `⟨by rw [hmass]; exact lt_top_iff_ne_top.2 hfin⟩`. Establish `h0 : μ.comap (jH z) ≠ 0`. Introduce `h`. Apply `hW.2.1` to reduce the goal to its premises. Rewrite using `[← map_jH hW, h, Measure.map_zero]`.

Establish `: SecondCountableTopology (stabH k r z)` using `inferInstanceAs (SecondCountableTopology ((stabH k r z : Set (HU.Gp k r))))`. Establish `: BorelSpace (stabH k r z)` using `inferInstanceAs (BorelSpace ((stabH k r z : Set (HU.Gp k r))))`. Set `g : stabH k r z` to `⟨⟨fun i j => b i j, ⟨hb.1, hb.2.1⟩⟩, hb.2.2⟩`. Establish `hR` using `fin_right (μ.comap (jH z)) h0 g`. Establish `e : rmulM b ∘ jH z = jH z ∘ (· * g)` using `funext fun x => rfl`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.map_map (rmulM_cont b).measurable (jH_memb z).measurable, e, ← Measure.map_map (jH_memb z).measurable (measurable_mul_const g)]`. Use `_ = μ := by rw [hR, map_jH hW]`.
-/
theorem unimodK : UnimodK := by
  intro k r z μ hW hfin b hb
  have : SigmaFinite μ := hW.1
  have hl := nuH_left hW
  have hmass : (μ.comap (jH z)) univ = μ univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z).measurable MeasurableSet.univ, preimage_univ]
  have : IsFiniteMeasure (μ.comap (jH z)) := ⟨by rw [hmass]; exact lt_top_iff_ne_top.2 hfin⟩
  have h0 : μ.comap (jH z) ≠ 0 := by
    intro h
    apply hW.2.1
    rw [← map_jH hW, h, Measure.map_zero]
  have : SecondCountableTopology (stabH k r z) :=
    inferInstanceAs (SecondCountableTopology ((stabH k r z : Set (HU.Gp k r))))
  have : BorelSpace (stabH k r z) := inferInstanceAs (BorelSpace ((stabH k r z : Set (HU.Gp k r))))
  let g : stabH k r z := ⟨⟨fun i j => b i j, ⟨hb.1, hb.2.1⟩⟩, hb.2.2⟩
  have hR := fin_right (μ.comap (jH z)) h0 g
  have e : rmulM b ∘ jH z = jH z ∘ (· * g) := funext fun x => rfl
  calc μ.map (rmulM b) = ((μ.comap (jH z)).map (jH z)).map (rmulM b) := by rw [map_jH hW]
    _ = ((μ.comap (jH z)).map (· * g)).map (jH z) := by
        rw [Measure.map_map (rmulM_cont b).measurable (jH_memb z).measurable, e,
          ← Measure.map_map (jH_memb z).measurable (measurable_mul_const g)]
    _ = μ := by rw [hR, map_jH hW]

end PI.RhsWLim.W.RI
