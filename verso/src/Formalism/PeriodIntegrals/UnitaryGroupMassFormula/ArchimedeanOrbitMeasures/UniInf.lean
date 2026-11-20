import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.EqOneOfToHAFin

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP f h`. Take `⟨hb, FdN, FdN', u, hX⟩` from `hP.1`. Establish `hG : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb)` using `hX.1.2.1`. Take `⟨s, rfl⟩` from `PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds h`. Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`.

Use `haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩`. Use `haveI : ContinuousMul (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := inferInstanceAs (ContinuousMul (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))`. Establish `hmT : Measurable (X.toInf hb)` using `MassDataMassesW.measurable_toInf X hb`. Establish `hms : Measurable fun x : X.B.I.Ginf => x * s` using `measurable_mul_const s`. Establish `hpi : (Formalism.L2.SG.ProjRows.muInf X.B.I).map (fun x : X.B.I.Ginf => x * s) = Formalism.L2.SG.ProjRows.muInf X.B.I`.

Establish `hv : ∀ v, (Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v) = Formalism.REAL.muG (X.B.I.ε v)` using `fun v => Formalism.REAL.indefinite_unitary_unimodular _ (X.B.I.ε v) (s v)`. Use `haveI : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v)) := fun v => by`. Rewrite using `[hv v]`. Use `infer_instance`. Establish `e` using `Measure.pi_map_pi (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (f := fun v y => y * s v) (fun v => (measurable_mul_const (s v)).aemeasurable)`.

Simplify using `only [hv] at e`. Conclude with `e`. Establish `hm : X.measG.μGinf.map (fun g => g * X.toInf hb s) = X.measG.μGinf`. Rewrite using `[hG, Measure.map_map (measurable_mul_const _) hmT]`. Establish `e : (fun g => g * X.toInf hb s) ∘ X.toInf hb = X.toInf hb ∘ (fun x : X.B.I.Ginf => x * s)`.

Use function extensionality and compare the values at `fun g => (PI.AprimeInfU.toInf_mul X hb g s).symm`. Rewrite using `[e, ← Measure.map_map hmT hms, hpi]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[MeasurableEquiv.coe_mulRight, hm]`.
-/
theorem unimodInf_holds : UnimodInf := by
  intro D X u' ψ hT μinf νinf fibInf hP f h
  obtain ⟨hb, FdN, FdN', u, hX⟩ := hP.1
  have hG : X.measG.μGinf = (Formalism.L2.SG.ProjRows.muInf X.B.I).map (X.toInf hb) := hX.1.2.1
  obtain ⟨s, rfl⟩ := PI.AprimeInfU.toInf_surjective X hb MassDataMassesW.splitIso_holds h
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  haveI : BorelSpace (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) := ⟨rfl⟩
  haveI : ContinuousMul (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
    inferInstanceAs (ContinuousMul (HR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J))
  have hmT : Measurable (X.toInf hb) := MassDataMassesW.measurable_toInf X hb
  have hms : Measurable fun x : X.B.I.Ginf => x * s := measurable_mul_const s
  have hpi : (Formalism.L2.SG.ProjRows.muInf X.B.I).map (fun x : X.B.I.Ginf => x * s) =
      Formalism.L2.SG.ProjRows.muInf X.B.I := by
    have hv : ∀ v, (Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v) = Formalism.REAL.muG (X.B.I.ε v) :=
      fun v => Formalism.REAL.indefinite_unitary_unimodular _ (X.B.I.ε v) (s v)
    haveI : ∀ v, SigmaFinite ((Formalism.REAL.muG (X.B.I.ε v)).map (fun y => y * s v)) := fun v => by
      rw [hv v]; infer_instance
    have e := Measure.pi_map_pi (μ := fun v => Formalism.REAL.muG (X.B.I.ε v)) (f := fun v y => y * s v)
      (fun v => (measurable_mul_const (s v)).aemeasurable)
    simp only [hv] at e
    exact e
  have hm : X.measG.μGinf.map (fun g => g * X.toInf hb s) = X.measG.μGinf := by
    rw [hG, Measure.map_map (measurable_mul_const _) hmT]
    have e : (fun g => g * X.toInf hb s) ∘ X.toInf hb = X.toInf hb ∘ (fun x : X.B.I.Ginf => x * s) :=
      funext fun g => (PI.AprimeInfU.toInf_mul X hb g s).symm
    rw [e, ← Measure.map_map hmT hms, hpi]
  calc ∫⁻ g, f (g * X.toInf hb s) ∂X.measG.μGinf
      = ∫⁻ g, f g ∂(X.measG.μGinf.map (MeasurableEquiv.mulRight (X.toInf hb s))) :=
        (lintegral_map_equiv f (MeasurableEquiv.mulRight (X.toInf hb s))).symm
    _ = ∫⁻ g, f g ∂X.measG.μGinf := by
        rw [MeasurableEquiv.coe_mulRight, hm]

/- English proof (translation)
The claim follows from `jacOne_of_good hK unimodInf_holds hG`.
-/
theorem jacOne_of_goodChart (hK : KPos) (hG : GoodChartEx) : JacOne :=
  jacOne_of_good hK unimodInf_holds hG

end PI.AprimeInfW
