import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalA
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.SimeqPadicIntegers
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.LogSigmaOnePullbackSpec
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InvariantDerivationSubstLawThree

namespace Formalism.L2.Th1.B

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem invExists : InvExists := by
  exact formal_inverse_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem halfExists : HalfExists := by
  exact formal_halving_exists
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem simeqHalf : SimeqHalf := by
  exact Sim.simeq_halving
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phOEven : PhOEven := by
  exact Ph.logSigmaPullbackEven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phEEven : PhEEven := by
  exact Ph.logSigmaOnePullbackEven
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parEFormula : ParEFormula := by
  exact ParE.ParEFormula_of addSigma1Log
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parE : ParE := by
  exact ParE.ParE_of parEFormula simeqLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem diagTwo : DiagTwo := by
  exact DiagTwo_of simeqInt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Supply the required witnesses or components.
-/
theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem f1E : LogSigmaOnePullbackCocycle := by
  intro K _ _ _ A kap e1 s2 w l i F hw hF hi hk hI h2
  have h0 := (phEDef K s2 e1 kap w l hF.2.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phE s2 e1 kap w l) hF h0
  have hd := cube K F l i (phE s2 e1 kap w l) hF hi h2 (parE K A kap e1 s2 w l i F hw hF hi hk hI)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
