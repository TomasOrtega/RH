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
Conclude with `formal_inverse_exists`.
-/
theorem invExists : InvExists := by
  exact formal_inverse_exists
/- English proof (translation)
Conclude with `formal_halving_exists`.
-/
theorem halfExists : HalfExists := by
  exact formal_halving_exists
/- English proof (translation)
Conclude with `coboundary_rules_hold`.
-/
theorem cobRules : CobRules := by
  exact coboundary_rules_hold
/- English proof (translation)
Conclude with `Sim.simeq_integral_series`.
-/
theorem simeqInt : SimeqInt := by
  exact Sim.simeq_integral_series
/- English proof (translation)
Conclude with `Sim.simeq_halving`.
-/
theorem simeqHalf : SimeqHalf := by
  exact Sim.simeq_halving
/- English proof (translation)
Conclude with `Sim.simeq_formal_log`.
-/
theorem simeqLog : SimeqLog := by
  exact Sim.simeq_formal_log
/- English proof (translation)
Conclude with `Ph.logSigmaPullbackSpec`.
-/
theorem phODef : PhODef := by
  exact Ph.logSigmaPullbackSpec
/- English proof (translation)
Conclude with `Ph.logSigmaOnePullbackSpec`.
-/
theorem phEDef : PhEDef := by
  exact Ph.logSigmaOnePullbackSpec
/- English proof (translation)
Conclude with `Ph.logSigmaPullbackEven`.
-/
theorem phOEven : PhOEven := by
  exact Ph.logSigmaPullbackEven
/- English proof (translation)
Conclude with `Ph.logSigmaOnePullbackEven`.
-/
theorem phEEven : PhEEven := by
  exact Ph.logSigmaOnePullbackEven
/- English proof (translation)
Conclude with `ParE.ParEFormula_of addSigma1Log`.
-/
theorem parEFormula : ParEFormula := by
  exact ParE.ParEFormula_of addSigma1Log
/- English proof (translation)
Conclude with `ParE.ParE_of parEFormula simeqLog`.
-/
theorem parE : ParE := by
  exact ParE.ParE_of parEFormula simeqLog
/- English proof (translation)
Conclude with `ParE.weierstrass_series_integral`.
-/
theorem wIntegral : WIntegral := by
  exact ParE.weierstrass_series_integral
/- English proof (translation)
Conclude with `ParO.ParO_of addSgStar phODef simeqLog`.
-/
theorem parO : ParO := by
  exact ParO.ParO_of addSgStar phODef simeqLog
/- English proof (translation)
Conclude with `ParO.DiffPh_of sigma1Sq simeqLog`.
-/
theorem diffPh : DiffPh := by
  exact ParO.DiffPh_of sigma1Sq simeqLog
/- English proof (translation)
Conclude with `Cube_of halfExists simeqInt`.
-/
theorem cube : Cube := by
  exact Cube_of halfExists simeqInt
/- English proof (translation)
Conclude with `DiagTwo_of simeqInt`.
-/
theorem diagTwo : DiagTwo := by
  exact DiagTwo_of simeqInt
/- English proof (translation)
Conclude with `Jets.jets_three_variables_holds`.
-/
theorem jetsThree : JetsThree := by
  exact Jets.jets_three_variables_holds

/- English proof (translation)
Introduce `K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2`. Establish `hl` using `hF.2.2`. Establish `h0` using `(phODef K s2 P l hl.1 hl.2.1).1`. Take `⟨hdiv, hsw⟩` from `cobRules K F l (phO s2 P l) hF h0`. Establish `hd` using `cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)`.

Conclude with `⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩`.
-/
theorem f1O : LogSigmaPullbackCocycle := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2
  have hl := hF.2.2
  have h0 := (phODef K s2 P l hl.1 hl.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phO s2 P l) hF h0
  have hd := cube K F l i (phO s2 P l) hF hi h2 (parO K g2 g3 s2 c0 P l i ep F hP hF hi hC)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

/- English proof (translation)
Introduce `K _ _ _ A kap e1 s2 w l i F hw hF hi hk hI h2`. Establish `h0` using `(phEDef K s2 e1 kap w l hF.2.2.1).1`. Take `⟨hdiv, hsw⟩` from `cobRules K F l (phE s2 e1 kap w l) hF h0`. Establish `hd` using `cube K F l i (phE s2 e1 kap w l) hF hi h2 (parE K A kap e1 s2 w l i F hw hF hi hk hI)`. Conclude with `⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩`.
-/
theorem f1E : LogSigmaOnePullbackCocycle := by
  intro K _ _ _ A kap e1 s2 w l i F hw hF hi hk hI h2
  have h0 := (phEDef K s2 e1 kap w l hF.2.2.1).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l (phE s2 e1 kap w l) hF h0
  have hd := cube K F l i (phE s2 e1 kap w l) hF hi h2 (parE K A kap e1 s2 w l i F hw hF hi hk hI)
  exact ⟨hdiv, hsw, hd, by rw [hsw]; exact hd⟩

end Formalism.L2.Th1.B
