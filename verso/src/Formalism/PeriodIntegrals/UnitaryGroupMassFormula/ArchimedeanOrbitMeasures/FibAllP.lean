import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.OrbPol
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushLF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.FibInvT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Introduce `K hK hKU`. Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Take `⟨k, -, hkcl, hKk, hkU⟩` from `exists_compact_closed_between hK (isOpen_IndI X) hKU`. Take `⟨f, hf1, hf0, hfc, -⟩` from `exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKk)`. Establish `hts : tsupport f ⊆ IndI X`.

Use `(closure_minimal ?_ hkcl).trans hkU` and prove the remaining obligations. Introduce `y hy`. Assume the negation of the conclusion as `h`. Conclude with `hy (hf0 (fun h' => h (interior_subset h')))`. Establish `hI` using `((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[hf1 hy]`. Simplify using the standard rewrite rules. Use `_ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm`.

Use `_ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) := mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1`. Use `_ < ⊤ := hI.lintegral_lt_top`.
-/
theorem lfFib_at {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf
    (hP : PushHyp X u' ψ hT μinf νinf fibInf) (T : HmI X) : LFI X (fibInf T) := by
  intro K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 T (Set.mem_univ _)
  calc fibInf T K ≤ fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf T {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf T) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP T`. Use `⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩` and prove the remaining obligations. Establish `hfib` using `hP.2.2.2.2.2.2`. Establish `h` using `fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1 (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib`. Conclude with `congrFun h T`.
-/
theorem fibAllT_holds : FibAllT := by
  intro D X u' ψ hT μinf νinf fibInf hP T
  refine ⟨fun g => ?_, lfFib_at X u' ψ hT μinf νinf fibInf hP T⟩
  have hfib := hP.2.2.2.2.2.2
  have h := fibEqI X ψ μinf νinf _ _ hP.2.2.2.2.1 hP.2.2.2.2.2.1
    (fibTrans X μinf νinf fibInf hfib g (sdInvG_of sdTestI_holds X u' ψ hT μinf νinf fibInf hP g)) hfib
  exact congrFun h T

end PI.AprimeInfW
