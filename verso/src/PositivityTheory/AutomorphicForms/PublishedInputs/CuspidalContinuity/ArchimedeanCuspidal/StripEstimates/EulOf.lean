import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImPosScaledUpperHalfPlane
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootOfUnityCharacterPeriodic
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.ScalarIntegralEstimates
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussSumConjugation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NeZeroOfRePos
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsWeightGamma0NeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentsTransferOneOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.B1
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeGaussLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StripTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOnTranslateFd
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.SecondDifferenceCpowBound
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountEqCardZmod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootCountOfNotDvdJacobi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareEuler
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharpolyFactorCoeffZeroValuationEqProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSumFloorHalf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierIntegrationByParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierContinuationDecay
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableOneAddSq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCuspZeroFourierExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HalfIntegralEisensteinContinuation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormZInvLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphyIntegralParam
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldedIdentityOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurableSetTranslate
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrdUniformizerEqOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsNormEqPrimesEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsumSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSymCoeffLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lf3
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLFactorRankThreeUnramified
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulOfOfFaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCharacterInv

namespace Ad3.S

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfTheta.t1 : T1)`.
-/
theorem t1 : T1 := (@GlobalTheory.CompanionTheory.HalfTheta.t1 : T1)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeight.finite_sum_splitting : T2)`.
-/
theorem t2 : T2 := (@GlobalTheory.CompanionTheory.HalfWeight.finite_sum_splitting : T2)

/- English proof (translation)
The claim follows from `(@Ad3.S.third_estimate_of_first_two : T1 → T2 → T3) t1 t2`.
-/
theorem t3 : T3 := (@Ad3.S.third_estimate_of_first_two : T1 → T2 → T3) t1 t2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeight.gauss_sum_conjugation : T4)`.
-/
theorem t4 : T4 := (@GlobalTheory.CompanionTheory.HalfWeight.gauss_sum_conjugation : T4)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeightUnfold.term_of_theta : T3 → T4 → T5) t3 t4`.
-/
theorem t5 : T5 := (@GlobalTheory.CompanionTheory.HalfWeightUnfold.term_of_theta : T3 → T4 → T5) t3 t4

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.ModularTiling.exists_weight_Gamma0 : U0)`.
-/
theorem u0 : U0 := (@GlobalTheory.CompanionTheory.ModularTiling.exists_weight_Gamma0 : U0)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.Unfolding.unfolding_strip : U1)`.
-/
theorem u1 : U1 := (@GlobalTheory.CompanionTheory.Unfolding.unfolding_strip : U1)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.CuspDecay.b1 : B1)`.
-/
theorem b1 : B1 := (@GlobalTheory.CompanionTheory.CuspDecay.b1 : B1)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.ThetaBound.b2 : B2)`.
-/
theorem b2 : B2 := (@GlobalTheory.CompanionTheory.ThetaBound.b2 : B2)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntegralWeight.unfolding_of_bound : B2 → HorizontalIntegralTwisted) b2`.
-/
theorem u2a : HorizontalIntegralTwisted := (@GlobalTheory.CompanionTheory.HalfIntegralWeight.unfolding_of_bound : B2 → HorizontalIntegralTwisted) b2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWt.strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2) b1 b2 u2a`.
-/
theorem u2 : U2 := (@GlobalTheory.CompanionTheory.HalfWt.strip_integral : B1 → B2 → HorizontalIntegralTwisted → U2) b1 b2 u2a

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.CuspHeight.integrableOn_translate_fd : D1)`.
-/
theorem d1 : D1 := (@GlobalTheory.CompanionTheory.CuspHeight.integrableOn_translate_fd : D1)

/- English proof (translation)
The claim follows from `(@Ad3.S.lB_of : LB)`.
-/
theorem lB : LB := (@Ad3.S.lB_of : LB)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.SquareRootCount.rr_eq : N1)`.
-/
theorem n1 : N1 := (@GlobalTheory.CompanionTheory.SquareRootCount.rr_eq : N1)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.SqrtCount.countingSquareRoots : N2)`.
-/
theorem n2 : N2 := (@GlobalTheory.CompanionTheory.SqrtCount.countingSquareRoots : N2)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.SquareEuler.euler_coeff : N1 → N2 → A2) n1 n2`.
-/
theorem a2 : A2 := (@GlobalTheory.CompanionTheory.SquareEuler.euler_coeff : N1 → N2 → A2) n1 n2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1) lB n2 a2`.
-/
theorem a1 : A1 := (@GlobalTheory.CompanionTheory.HalfInt.charpoly_factor_coeff_zero_valuation_eq_prod : LB → N2 → A2 → A1) lB n2 a2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntZero.main : LB → N2 → A2 → A0) lB n2 a2`.
-/
theorem a0 : A0 := (@GlobalTheory.CompanionTheory.HalfIntZero.main : LB → N2 → A2 → A0) lB n2 a2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeight.w0 : W0)`.
-/
theorem w0 : W0 := (@GlobalTheory.CompanionTheory.HalfWeight.w0 : W0)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntegral.kernel_fourier_integration_by_parts : W0 → W1) w0`.
-/
theorem w1 : W1 := (@GlobalTheory.CompanionTheory.HalfIntegral.kernel_fourier_integration_by_parts : W0 → W1) w0

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeight.kernel_fourier_continuation_decay : W0 → W1 → W2) w0 w1`.
-/
theorem w2 : W2 := (@GlobalTheory.CompanionTheory.HalfWeight.kernel_fourier_continuation_decay : W0 → W1 → W2) w0 w1

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeightKernel.poisson_kernel : W0 → W2 → P1) w0 w2`.
-/
theorem p1 : P1 := (@GlobalTheory.CompanionTheory.HalfWeightKernel.poisson_kernel : W0 → W2 → P1) w0 w2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.EisensteinPoissonSummation.eisenstein_cusp_zero_fourier_expansion : P1 → P2) p1`.
-/
theorem p2 : P2 := (@GlobalTheory.CompanionTheory.EisensteinPoissonSummation.eisenstein_cusp_zero_fourier_expansion : P1 → P2) p1

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfInt.half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0) a0 a1 w0 w1 w2 p2`.
-/
theorem e0 : E0 := (@GlobalTheory.CompanionTheory.HalfInt.half_integral_eisenstein_continuation : A0 → A1 → W0 → W1 → W2 → P2 → E0) a0 a1 w0 w1 w2 p2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntPR.pr : PR)`.
-/
theorem pR : PR := (@GlobalTheory.CompanionTheory.HalfIntPR.pr : PR)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.InvGammaStrip.g0 : G0)`.
-/
theorem g0 : G0 := (@GlobalTheory.CompanionTheory.InvGammaStrip.g0 : G0)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.RgAds.holomorphy_integral_param : HI)`.
-/
theorem hI : HI := (@GlobalTheory.CompanionTheory.RgAds.holomorphy_integral_param : HI)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfWeight.unfolded_identity_of : T5 → U1 → U2 → B2 → S1) t5 u1 u2 b2`.
-/
theorem s1 : S1 := (@GlobalTheory.CompanionTheory.HalfWeight.unfolded_identity_of : T5 → U1 → U2 → B2 → S1) t5 u1 u2 b2

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.ShimStep.shim_of : U0 → B2 → D1 → E0 → PR → G0 → HI → S1 → Shim) u0 b2 d1 e0 pR g0 hI s1`.
-/
theorem shim : Shim := (@GlobalTheory.CompanionTheory.ShimStep.shim_of : U0 → B2 → D1 → E0 → PR → G0 → HI → S1 → Shim) u0 b2 d1 e0 pR g0 hI s1

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntegral.e1 : E1)`.
-/
theorem e1 : E1 := (@GlobalTheory.CompanionTheory.HalfIntegral.e1 : E1)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.Rgads.e1b : faceMap_comp_succAbove_castSucc)`.
-/
theorem e1b : faceMap_comp_succAbove_castSucc := (@GlobalTheory.CompanionTheory.Rgads.e1b : faceMap_comp_succAbove_castSucc)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HeckeEig.e2a : E2a)`.
-/
theorem e2a : E2a := (@GlobalTheory.CompanionTheory.HeckeEig.e2a : E2a)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfIntWeight.localSeries : E2b)`.
-/
theorem e2b : E2b := (@GlobalTheory.CompanionTheory.HalfIntWeight.localSeries : E2b)

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients.e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2) e1b e2a e2b`.
-/
theorem e2 : E2 := (@GlobalTheory.CompanionTheory.UnramifiedEisensteinCoefficients.e2 : faceMap_comp_succAbove_castSucc → E2a → E2b → E2) e1b e2a e2b

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.EulerThree.HalfWt.adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3) e1b`.
-/
theorem e3 : E3 := (@GlobalTheory.CompanionTheory.EulerThree.HalfWt.adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3) e1b

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.HalfInt.eulOf_of_faceMap_comp_succAbove_castSucc : E1 → faceMap_comp_succAbove_castSucc → E2 → E3 → EulOf) e1 e1b e2 e3`.
-/
theorem eulOf : EulOf := (@GlobalTheory.CompanionTheory.HalfInt.eulOf_of_faceMap_comp_succAbove_castSucc : E1 → faceMap_comp_succAbove_castSucc → E2 → E3 → EulOf) e1 e1b e2 e3

/- English proof (translation)
The claim follows from `(@GlobalTheory.CompanionTheory.AdjointLift.anOf : AnOf)`.
-/
theorem anOf : AnOf := (@GlobalTheory.CompanionTheory.AdjointLift.anOf : AnOf)

end Ad3.S
