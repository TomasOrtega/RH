import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaNetDimensionAndPointCountBoundStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPolynomialBoundRunConstantsDegreeFourStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GamAtOfLawsCore
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CmFamilyFunctionalsDetectLowCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExtendEmbedding
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProofStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QuotientBoundOfKillDetectConstantRoomStatement
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

set_option autoImplicit false

namespace GlobalTheory.RunJoin

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨C₀, hC₀, hroom⟩` from `GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four`. Use `⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩` and prove the remaining obligations. Introduce `D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc`. Establish `h3 : 3 ≤ D.R.r` using `le_trans (by norm_num) hP.r8`. Establish `hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L`.

Take `⟨Q, -, -⟩` from `hP.page`. Conclude with `Q.ccK_log`. Take `⟨hZ, hR⟩` from `hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc`. Take `⟨-, -, -, -, -, -, -, -, hdim, -⟩` from `GlobalTheory.T.thetaNet_dimension_and_pointCount_bound D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP`. Establish `hG` using `GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore`.

Establish `hK` using `GlobalTheory.T.arithmeticCMKnownTheorems_proof`. Establish `hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size`. Establish `e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3`. Unfold `WeightFamilies.PPv`. Rewrite using `[show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Establish `hZ' : (1 : ℝ) ≤ Zb D large₂` using `hZ`. Conclude with `le_mul_of_one_le_right (by positivity) ka.one_le_size`. Establish `key` using `GlobalTheory.T.quotientBound_of_kill_detect_constantRoom hK D _ h.toLawsCore j ka 7 Tn (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3 hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D _ h.toLawsCore j ka 7 Tn _ hG hj hjm) (GlobalTheory.T.cmFamilyFunctionals …`.

Establish `e4 : max (4 : ℝ) (max 4 3) = 4` using `by norm_num`. Rewrite `key` using `[e4]`. Conclude with `key hCR hO hn hlast hsz hT hc hTc`.
-/
theorem qAt_run : ∃ Cq : ℝ → ℝ → ℝ, ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → LatAt (recB h.toLawsCore) j ka → QAt large₂ (recB h.toLawsCore) j ka 7 H.CK 1 4 (Cq H.CA H.CK) 4 Tn (cc D large₂ C2 A2 7 wL) := by
  obtain ⟨C₀, hC₀, hroom⟩ := GlobalTheory.T.exists_polynomial_bound_runConstants_degree_four
  refine ⟨fun a b => 1 + 3 * C₀ a 7 b + 1041, ?_⟩
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm hL hCR hO hn hlast hsz hT hc hTc
  have h3 : 3 ≤ D.R.r := le_trans (by norm_num) hP.r8
  have hcc : Real.log (Ideal.absNorm D.host.ccK) ≤ large₂.sc.L := by
    obtain ⟨Q, -, -⟩ := hP.page
    exact Q.ccK_log
  obtain ⟨hZ, hR⟩ := hroom D large₂ j ka H.CA 7 H.CK Tn (cc D large₂ C2 A2 7 wL) hP.hyp.1 hcc hj hjm h3 hCR hsz hT hc hTc
  obtain ⟨-, -, -, -, -, -, -, -, hdim, -⟩ := GlobalTheory.T.thetaNet_dimension_and_pointCount_bound D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP
  have hG := GlobalTheory.RunIn.gamAt_of_lawsCore D _ h.toLawsCore
  have hK := GlobalTheory.T.arithmeticCMKnownTheorems_proof
  have hpp : 1041 * Zb D large₂ ^ 3 ≤ WeightFamilies.PPv D large₂ 1041 3 * ka.size := by
    have e : WeightFamilies.PPv D large₂ 1041 3 = 1041 * Zb D large₂ ^ 3 := by
      unfold WeightFamilies.PPv
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rfl
    rw [e]
    have hZ' : (1 : ℝ) ≤ Zb D large₂ := hZ
    exact le_mul_of_one_le_right (by positivity) ka.one_le_size
  have key := GlobalTheory.T.quotientBound_of_kill_detect_constantRoom hK D _ h.toLawsCore j ka 7 Tn (cc D large₂ C2 A2 7 wL) large₂ H.CK 1 4 (C₀ H.CA 7 H.CK) 4 1041 3
    hG hj hjm hL (GlobalTheory.ArcCM.killQ_of_gamAt hK D _ h.toLawsCore j ka 7 Tn _ hG hj hjm)
    (GlobalTheory.T.cmFamilyFunctionals_detect_lowCoefficients hK D _ h.toLawsCore j ka 7 Tn _ hG hj hjm h3 hT hc) hZ (hC₀ _ _ _) (by norm_num) hR
    (le_trans hdim hpp)
  have e4 : max (4 : ℝ) (max 4 3) = 4 := by norm_num
  rw [e4] at key
  exact key hCR hO hn hlast hsz hT hc hTc

end GlobalTheory.RunJoin
