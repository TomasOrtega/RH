import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

open MeasureTheory

/- English proof (translation)
Introduce `X ι _`. Use `haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩`. Use `haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩`. Use `haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance`. Use `haveI : IsSeparable X.ν := inferInstance`.

Use `haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance`. Use `infer_instance`.
-/
theorem hssep : HsSep := by
  intro X ι _
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  haveI : IsSeparable X.ν := inferInstance
  haveI : SecondCountableTopology (Lp ℂ 2 X.ν) := inferInstance
  infer_instance

end PositivityTheory.Rg.BcB.E2.P
