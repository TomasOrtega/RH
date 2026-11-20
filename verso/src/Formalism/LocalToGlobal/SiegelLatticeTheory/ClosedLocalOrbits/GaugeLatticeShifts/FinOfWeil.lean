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
Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Establish `hν : ν ≠ 0`. Introduce and unpack `rfl`. Apply `hμ` to reduce the goal to its premises. Use `hW (fun _ => 1) measurable_const` as an intermediate fact.

Simplify using `using this`. Choose the witnesses or unpack the hypotheses as in `⟨C, hC, hνC⟩ : ∃ C : Set G, IsCompact C ∧ ν C ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hν` to reduce the goal to its premises.

Establish `: ν Set.univ = 0`. Rewrite using `[← iUnion_compactCovering G]`. Conclude with `measure_iUnion_null fun n => hcon _ (isCompact_compactCovering G n)`. Conclude with `Measure.measure_univ_eq_zero.mp this`. Establish `hWc : IsCompact (K * C)` using `hK.mul hC`.

Establish `hWm : MeasurableSet (K * C)` using `hWc.isClosed.measurableSet`. Establish `hf` using `hW ((K * C).indicator 1) (measurable_one.indicator hWm)`. Rewrite `hf` using `[lintegral_indicator_one hWm]`. Establish `hinner : ∀ x, ∫⁻ s, (K * C).indicator 1 (s * x) ∂μS = μS ((· * x) ⁻¹' (K * C))` using `fun x => by`. Rewrite using `[← lintegral_indicator_one ((measurable_mul_const x) hWm)]`.

Both sides reduce to the same expression. Rewrite `hf` using `[hinner]`. Establish `hbound : μS K * ν C ≤ μ (K * C)`. Rewrite using `[hf, ← lintegral_indicator_const hC.isClosed.measurableSet]`. Apply `lintegral_mono` to reduce the goal to its premises.

Introduce `x`. Distinguish the cases in `hx : x ∈ C`. Rewrite using `[Set.indicator_of_mem hx]`. Conclude with `measure_mono fun k hk => Set.mul_mem_mul hk hx`. Simplify using `[hx]`.

Establish `hμW : μ (K * C) < ⊤` using `hWc.measure_lt_top`. Assume the negation of the conclusion as `htop`. Rewrite `htop` using `[not_lt, top_le_iff]`. Rewrite `hbound` using `[htop, ENNReal.top_mul hνC]`. Conclude with `absurd (lt_of_le_of_lt hbound hμW) (lt_irrefl _)`.
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
Use `set s : X.B.I.Ginf := Function.update 1 v x with hsdef`. Establish `hs : s ∈ X.SinfU u`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[hsdef, Function.update_self]`. Conclude with `hx`. Rewrite using `[hsdef, Function.update_of_ne hw]`. Conclude with `Formalism.L2.SG.Pf.WuDec.one_mem_Sloc X u w`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hdec⟩` from `Formalism.L2.S.Pv.HaarSubS.sDecomp_holds D X u`.

Take `⟨n, hn, h, hh, he⟩` from `hdec s hs`. Establish `hxv : x = n v * h v`. Use `congrFun he v` as an intermediate fact. Rewrite `this` using `[hsdef, Function.update_self]`. Conclude with `this`.

Conclude with `⟨n v, hn v, h v, hh v, hxv⟩`.
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
