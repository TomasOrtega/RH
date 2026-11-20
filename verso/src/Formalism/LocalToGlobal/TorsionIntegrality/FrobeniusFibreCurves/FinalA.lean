import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassReducedEquations
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RestrictSecondZeroInVarOne
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PderivZeroZeroWeierstrassDifference
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSig1S

namespace Formalism.L2.Th1.B

/- English proof (translation)
Introduce `K _ _ ι`. Conclude with `⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩, fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩`.
-/
theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
/- English proof (translation)
Introduce `K _ _ ι _ i`. Conclude with `⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩`.
-/
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  exact ⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩
/- English proof (translation)
Introduce `K _ _ ι κ _ φ hφ`. Conclude with `⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩`.
-/
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
/- English proof (translation)
Introduce `K _ _ f`. Conclude with `⟨dz_prim f, constantCoeff_prim f⟩`.
-/
theorem primRules : PrimRules := by
  intro K _ _ f
  exact ⟨dz_prim f, constantCoeff_prim f⟩
/- English proof (translation)
The claim follows from `wave_equation_unique`.
-/
theorem waveUnique : WaveUnique := wave_equation_unique
/- English proof (translation)
The claim follows from `wave_operator_kills`.
-/
theorem waveKills : WaveKills := wave_operator_kills
/- English proof (translation)
The claim follows from `parallelogram_cauchy_equation`.
-/
theorem parCauchy : ParCauchy := parallelogram_cauchy_equation
/- English proof (translation)
The claim follows from `difference_quotient_rule_holds`.
-/
theorem dqRule : DqRule := difference_quotient_rule_holds
/- English proof (translation)
The claim follows from `weierstrassReducedEquations`.
-/
theorem wpReduced : WpReduced := weierstrassReducedEquations
/- English proof (translation)
The claim follows from `invertedSecondDeriv`.
-/
theorem wSecond : WSecond := invertedSecondDeriv
/- English proof (translation)
The claim follows from `invertedEven`.
-/
theorem wEven : WEven := invertedEven
/- English proof (translation)
The claim follows from `shiftedReciprocalInverted`.
-/
theorem wOfWp : WOfWp := shiftedReciprocalInverted
/- English proof (translation)
The claim follows from `Add1.AddSigma1Log_of expLogRules expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wSecond`.
-/
theorem addSigma1Log : AddSigma1Log :=
  Add1.AddSigma1Log_of expLogRules expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy
    wSecond
/- English proof (translation)
The claim follows from `AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule`.
-/
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule
/- English proof (translation)
The claim follows from `AddSigma_of addSigmaLog expLogRules expLogSubst dqRule`.
-/
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst dqRule
/- English proof (translation)
The claim follows from `AddSgStar_of addSigma expLogRules expLogSubst`.
-/
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst
/- English proof (translation)
The claim follows from `Sq.sigmaOneSquare`.
-/
theorem sigma1Sq : Sigma1Sq := Sq.sigmaOneSquare

end Formalism.L2.Th1.B
