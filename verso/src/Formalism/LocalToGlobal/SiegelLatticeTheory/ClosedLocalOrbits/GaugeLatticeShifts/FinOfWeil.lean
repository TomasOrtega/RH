import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyConvClose
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.QuotIndepPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightInvOfModular

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.S.Pv.ConvG
open scoped InnerProductSpace ENNReal Pointwise

namespace Formalism.L2.SG.RealObj.EnergyConvJ

section Gen

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses repeatedly using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem fin_of_weil (μ μS ν : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : μ ≠ 0)
    (hW : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μ = ∫⁻ x, ∫⁻ s, f (s * x) ∂μS ∂ν) :
    IsFiniteMeasureOnCompacts μS := by
  refine ⟨fun K hK => ?_⟩
  have hν : ν ≠ 0 := by
    rintro rfl
    apply hμ
    have := hW (fun _ => 1) measurable_const
    simpa using this
  obtain ⟨C, hC, hνC⟩ : ∃ C : Set G, IsCompact C ∧ ν C ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_compactCovering G]
      exact measure_iUnion_null fun n => hcon _ (isCompact_compactCovering G n)
    exact Measure.measure_univ_eq_zero.mp this
  have hWc : IsCompact (K * C) := hK.mul hC
  have hWm : MeasurableSet (K * C) := hWc.isClosed.measurableSet
  have hf := hW ((K * C).indicator 1) (measurable_one.indicator hWm)
  rw [lintegral_indicator_one hWm] at hf
  have hinner : ∀ x, ∫⁻ s, (K * C).indicator 1 (s * x) ∂μS = μS ((· * x) ⁻¹' (K * C)) := fun x => by
    rw [← lintegral_indicator_one ((measurable_mul_const x) hWm)]
    rfl
  simp_rw [hinner] at hf
  have hbound : μS K * ν C ≤ μ (K * C) := by
    rw [hf, ← lintegral_indicator_const hC.isClosed.measurableSet]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ C
    · rw [Set.indicator_of_mem hx]
      exact measure_mono fun k hk => Set.mul_mem_mul hk hx
    · simp [hx]
  have hμW : μ (K * C) < ⊤ := hWc.measure_lt_top
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  rw [htop, ENNReal.top_mul hνC] at hbound
  exact absurd (lt_of_le_of_lt hbound hμW) (lt_irrefl _)

end Gen

variable {D : D7}

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem sloc_sub_NH (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) {x : Formalism.REAL.UJ (X.B.I.ε v)}
    (hx : x ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v) : x ∈ Formalism.L2.SG.Pf.WuDec.NHloc X u v := by
  classical
  set s : X.B.I.Ginf := Function.update 1 v x with hsdef
  have hs : s ∈ X.SinfU u := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hsdef, Function.update_self]
      exact hx
    · rw [hsdef, Function.update_of_ne hw]
      exact Formalism.L2.SG.Pf.WuDec.one_mem_Sloc X u w
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩ := Formalism.L2.S.Pv.HaarSubS.sDecomp_holds D X u
  obtain ⟨n, hn, h, hh, he⟩ := hdec s hs
  have hxv : x = n v * h v := by
    have := congrFun he v
    rw [hsdef, Function.update_self] at this
    exact this
  exact ⟨n v, hn v, h v, hh v, hxv⟩

end Formalism.L2.SG.RealObj.EnergyConvJ
