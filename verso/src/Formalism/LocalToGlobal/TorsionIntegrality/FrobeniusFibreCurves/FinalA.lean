import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.EvalSecondZeroAtVariableZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassReducedEquations
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.RestrictSecondZeroInVarOne
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.PderivZeroZeroWeierstrassDifference
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSig1S

namespace Formalism.L2.Th1.B

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem expLogRules : ExpLogRules := by
  intro K _ _ ι
  exact ⟨fun f g hf hg => fExp_add hf hg, fun f hf => ⟨constantCoeff_fExp hf, fLog_fExp hf⟩,
    fun g hg => ⟨constantCoeff_fLog hg, fExp_fLog hg⟩⟩
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem expLogDeriv : ExpLogDeriv := by
  intro K _ _ ι _ i
  exact ⟨fun f hf => pd_fExp i hf, fun g hg => mul_pd_fLog i hg⟩
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem expLogSubst : ExpLogSubst := by
  intro K _ _ ι κ _ φ hφ
  exact ⟨fun f hf => subst_fExp hφ hf, fun g hg => subst_fLog hφ hg⟩
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem primRules : PrimRules := by
  intro K _ _ f
  exact ⟨dz_prim f, constantCoeff_prim f⟩
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem waveUnique : WaveUnique := wave_equation_unique
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem waveKills : WaveKills := wave_operator_kills
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parCauchy : ParCauchy := parallelogram_cauchy_equation
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dqRule : DqRule := difference_quotient_rule_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpReduced : WpReduced := weierstrassReducedEquations
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wSecond : WSecond := invertedSecondDeriv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wEven : WEven := invertedEven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wOfWp : WOfWp := shiftedReciprocalInverted
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addSigma1Log : AddSigma1Log :=
  Add1.AddSigma1Log_of expLogRules expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy
    wSecond
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addSigmaLog : AddSigmaLog :=
  AddSigmaLog_of expLogDeriv expLogSubst primRules waveUnique waveKills parCauchy wpReduced dqRule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addSigma : AddSigma := AddSigma_of addSigmaLog expLogRules expLogSubst dqRule
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addSgStar : AddSgStar := AddSgStar_of addSigma expLogRules expLogSubst
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigma1Sq : Sigma1Sq := Sq.sigmaOneSquare

end Formalism.L2.Th1.B
