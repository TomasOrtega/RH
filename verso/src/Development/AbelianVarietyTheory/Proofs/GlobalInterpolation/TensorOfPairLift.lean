import Mathlib
import Formalism.SharpRestriction.GrowthBounds.PlaneCountTheoremWithConstants
import Formalism.SharpRestriction.GrowthBounds.InitialMinorTransposeMemHighestWeight
import Formalism.LocalToGlobal.GroupLattices.FockModels.DualInclusionLattices
import Formalism.LocalToGlobal.GroupLattices.FockModels.LoBlockActComp
import Formalism.PeriodIntegrals.AdmissibleModel.WeylDim
import Formalism.LocalToGlobal.GroupLattices.FockModels.Cartan
import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti
import Formalism.LocalToGlobal.GroupLattices.FockModels.TestSideFinal
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains
import Formalism.SharpRestriction.GrowthBounds.FockGramWindow
import Formalism.SharpRestriction.GrowthBounds.WittIdentPI
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PolyUpperBoundDelta
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestAssumptionsOfThreeInterfaces
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColTop
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColumnPolynomialCovectorZero
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FamilyFourthBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegmentStatementHolds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeAlternative
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KapCore
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TopDegreeLeTwoB
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ExtendedStatementOfParts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.TotalDegreeEplus
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FirstCoefficientFacts
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.LeAndHalfLeProdOneSubExpNegOfBounds
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinrankTensor
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SegLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.RankOnDigitsCast
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CardEqChainSum
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.StWeyl
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FactorsOfPerturb
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ChainDim
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.UpperCountOfTopRows
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CountLow
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.AiAddMulLeA0
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockFG
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.ThresholdStandardLarge
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreeRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairLift
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PairCount
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.NotKept
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WtBound
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.KeptBlocksOfSLine
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.Bracket
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseDegreesLargeOfStd
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.CoarseThresholdRatioConsecutive
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.WittPNe
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.FinalTheorems
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualFlatOf
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.DualLat
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.PosCoreLetter
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCharZeroAt
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SettingCZ
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.SegFormZeroRight
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TestFlat
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Beyond44OfRestRawTail
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PairedLiftAtOfIdentity
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.GTheta
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyOne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.KeyMinorDvd
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.PsiRes0Ne
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFFinal

noncomputable section

namespace GlobalTheory.EX.RangeOne

section Numbers

open Formalism.MainNotions.G Formalism.MainNotions.ColumnSystems Formalism.MainNotions.ColumnSystems.Pf

/- English proof (translation)
Establish `hk0 : 0 < k` using `by linarith`. Establish `hQ0 : 0 < Q` using `by linarith`. Establish `hbe12 : be ≤ 1 / 12` using `by linarith`. Establish `h1 : b' * (11 / 12) ≤ b' * (1 - be)` using `mul_le_mul_of_nonneg_left (by linarith) hb.le`. Establish `h2 : A * P ≤ A * Q` using `mul_le_mul_of_nonneg_left hPQ hA0`.

Establish `h3 : k * P ≤ k * Q` using `mul_le_mul_of_nonneg_left hPQ hk0.le`. Establish `hAQ : b' * (11 / 12) - k * Q ≤ A * Q` using `by linarith`. Establish `hQ2 : Q ^ 2 ≤ Q ^ 4` using `pow_le_pow_right₀ hQ1 (by norm_num)`. Establish `hk3 : 0 ≤ k ^ 3` using `by positivity`. Establish `hb2 : 2 * k ^ 3 * Q ^ 2 * c ≤ b'`.

Establish `a0 : 0 ≤ k ^ 3 * c` using `by positivity`. Establish `a1 : 2 * k ^ 3 * Q ^ 2 * c ≤ 2 * k ^ 3 * Q ^ 4 * c`. Use `mul_le_mul_of_nonneg_left hQ2 a0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a5 : 0 ≤ k ^ 3 * Q ^ 4 * c` using `by positivity`.

Establish `a2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ N * (k ^ 3 * Q ^ 4 * c)` using `mul_le_mul_of_nonneg_right hN2 a5`. Establish `a6 : 0 ≤ N * (k ^ 3 * Q ^ 4 * c)` using `by positivity`. Establish `a3 : N * (k ^ 3 * Q ^ 4 * c) * 1 ≤ N * (k ^ 3 * Q ^ 4 * c) * Y` using `mul_le_mul_of_nonneg_left hY1 a6`. Establish `a4 : 1 * k ^ 3 * N * Q ^ 4 * c * Y = N * (k ^ 3 * Q ^ 4 * c) * Y` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA1 : ((11 / 6) * k ^ 3 * Q * c - k) * Q ≤ A * Q`. Establish `e : ((11 / 6) * k ^ 3 * Q * c - k) * Q = (11 / 12) * (2 * k ^ 3 * Q ^ 2 * c) - k * Q` using `by ring`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA2 : (11 / 6) * k ^ 3 * Q * c - k ≤ A` using `le_of_mul_le_mul_right hA1 hQ0`.

Establish `hdek : 40 ≤ de * k`. Establish `a1 : 40 * (1 / k) ≤ de` using `by linarith`. Establish `a2 : 40 * (1 / k) * k = 40` using `by field_simp`. Establish `a3 : 40 * (1 / k) * k ≤ de * k` using `mul_le_mul_of_nonneg_right a1 hk0.le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hfin : ((55 / 3) * k ^ 2 * Q * c - 10) * k ≤ de / 4 * A * k`. Establish `a1 : 40 * A ≤ de * k * A` using `mul_le_mul_of_nonneg_right hdek hA0`. Establish `a2 : ((55 / 3) * k ^ 2 * Q * c - 10) * k = (10 / 1) * ((11 / 6) * k ^ 3 * Q * c - k)` using `by ring`. Establish `a3 : de / 4 * A * k = (de * k * A) / 4` using `by ring`. Rewrite using `[a2, a3]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin2 : (55 / 3) * k ^ 2 * Q * c - 10 ≤ de / 4 * A` using `le_of_mul_le_mul_right hfin hk0`. Establish `hN1 : N1 ≤ k` using `by linarith`. Establish `hkaB : ka ≤ 13 * k ^ 2 * Q`. Rewrite using `[hka]`.

Establish `a1 : k * N1 ≤ k * k` using `mul_le_mul_of_nonneg_left hN1 hk0.le`. Establish `a2 : k * N1 * Q ≤ k * k * Q` using `mul_le_mul_of_nonneg_right a1 hQ0.le`. Establish `e1 : 13 * k * N1 * Q = 13 * (k * N1 * Q)` using `by ring`. Establish `e2 : 13 * k ^ 2 * Q = 13 * (k * k * Q)` using `by ring`. Rewrite using `[e1, e2]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hkQ : k ≤ k * Q` using `le_mul_of_one_le_right hk0.le hQ1`. Establish `hk25 : 5 * 5 ≤ k * k` using `mul_le_mul hk5 hk5 (by norm_num) hk0.le`. Establish `hk5k : 5 * k ≤ k * k` using `mul_le_mul_of_nonneg_right hk5 hk0.le`. Establish `hc0 : 0 ≤ c` using `by linarith`.

Establish `hQc0 : 0 ≤ Q * c` using `mul_nonneg hQ0.le hc0`. Establish `hQc1 : 1 ≤ Q * c` using `one_le_mul_of_one_le_of_one_le hQ1 hc1`. Establish `hQc : 25 * (Q * c) ≤ k * k * (Q * c)`. Use `mul_le_mul_of_nonneg_right hk25 hQc0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hkQc : 5 * k * (Q * c) ≤ k * k * (Q * c)` using `mul_le_mul_of_nonneg_right hk5k hQc0`. Establish `hX : k ^ 2 * Q * c = k * k * (Q * c)` using `by ring`. Establish `hfirst : c * (ka + 2 * Q + 3 * k) ≤ c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q))`. Apply `mul_le_mul_of_nonneg_left _ hc0` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e1 : c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) = 13 * (k * k * (Q * c)) + 2 * (Q * c) + 3 * (k * (Q * c))` using `by ring`. Establish `e2 : 55 / 3 * k ^ 2 * Q * c = 55 / 3 * (k * k * (Q * c))` using `by ring`. Establish `e3 : 5 * k * (Q * c) = 5 * (k * (Q * c))` using `by ring`. Rewrite `hfirst` using `[e1]`. Rewrite `hfin2` using `[e2]`.

Rewrite `hkQc` using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core_roomR {b' g A P Q k c de be eps N Y N1 ka : ℝ} (hb : 0 < b') (hAP : g - k * P < A * P)
    (hbT : b' * (1 - be) ≤ g) (hbe : be ≤ de / 2 - 18 * eps) (heps : 0 ≤ eps) (hde6 : de < 1 / 6)
    (hde40 : 40 * eps ≤ de) (hepsk : 1 / k ≤ eps) (hk5 : 5 ≤ k) (hQ1 : 1 ≤ Q) (hP0 : 0 < P) (hPQ : P ≤ Q)
    (sq_level_le_degree : 2 * N1 + 3 ≤ k) (hN2 : 2 ≤ N) (hY1 : 1 ≤ Y) (hHc : 1 * k ^ 3 * N * Q ^ 4 * c * Y ≤ b')
    (hc1 : 1 ≤ c) (hA0 : 0 ≤ A) (hN10 : 0 ≤ N1) (hka : ka = 13 * k * N1 * Q) :
    c * (ka + 2 * Q + 3 * k) + 4 ≤ de / 4 * A := by
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 < Q := by linarith
  have hbe12 : be ≤ 1 / 12 := by linarith
  have h1 : b' * (11 / 12) ≤ b' * (1 - be) := mul_le_mul_of_nonneg_left (by linarith) hb.le
  have h2 : A * P ≤ A * Q := mul_le_mul_of_nonneg_left hPQ hA0
  have h3 : k * P ≤ k * Q := mul_le_mul_of_nonneg_left hPQ hk0.le
  have hAQ : b' * (11 / 12) - k * Q ≤ A * Q := by linarith
  have hQ2 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hk3 : 0 ≤ k ^ 3 := by positivity
  have hb2 : 2 * k ^ 3 * Q ^ 2 * c ≤ b' := by
    have a0 : 0 ≤ k ^ 3 * c := by positivity
    have a1 : 2 * k ^ 3 * Q ^ 2 * c ≤ 2 * k ^ 3 * Q ^ 4 * c := by
      have := mul_le_mul_of_nonneg_left hQ2 a0
      linarith
    have a5 : 0 ≤ k ^ 3 * Q ^ 4 * c := by positivity
    have a2 : 2 * (k ^ 3 * Q ^ 4 * c) ≤ N * (k ^ 3 * Q ^ 4 * c) := mul_le_mul_of_nonneg_right hN2 a5
    have a6 : 0 ≤ N * (k ^ 3 * Q ^ 4 * c) := by positivity
    have a3 : N * (k ^ 3 * Q ^ 4 * c) * 1 ≤ N * (k ^ 3 * Q ^ 4 * c) * Y := mul_le_mul_of_nonneg_left hY1 a6
    have a4 : 1 * k ^ 3 * N * Q ^ 4 * c * Y = N * (k ^ 3 * Q ^ 4 * c) * Y := by ring
    linarith
  have hA1 : ((11 / 6) * k ^ 3 * Q * c - k) * Q ≤ A * Q := by
    have e : ((11 / 6) * k ^ 3 * Q * c - k) * Q = (11 / 12) * (2 * k ^ 3 * Q ^ 2 * c) - k * Q := by ring
    rw [e]
    linarith
  have hA2 : (11 / 6) * k ^ 3 * Q * c - k ≤ A := le_of_mul_le_mul_right hA1 hQ0
  have hdek : 40 ≤ de * k := by
    have a1 : 40 * (1 / k) ≤ de := by linarith
    have a2 : 40 * (1 / k) * k = 40 := by field_simp
    have a3 : 40 * (1 / k) * k ≤ de * k := mul_le_mul_of_nonneg_right a1 hk0.le
    linarith
  have hfin : ((55 / 3) * k ^ 2 * Q * c - 10) * k ≤ de / 4 * A * k := by
    have a1 : 40 * A ≤ de * k * A := mul_le_mul_of_nonneg_right hdek hA0
    have a2 : ((55 / 3) * k ^ 2 * Q * c - 10) * k = (10 / 1) * ((11 / 6) * k ^ 3 * Q * c - k) := by ring
    have a3 : de / 4 * A * k = (de * k * A) / 4 := by ring
    rw [a2, a3]
    linarith
  have hfin2 : (55 / 3) * k ^ 2 * Q * c - 10 ≤ de / 4 * A := le_of_mul_le_mul_right hfin hk0
  have hN1 : N1 ≤ k := by linarith
  have hkaB : ka ≤ 13 * k ^ 2 * Q := by
    rw [hka]
    have a1 : k * N1 ≤ k * k := mul_le_mul_of_nonneg_left hN1 hk0.le
    have a2 : k * N1 * Q ≤ k * k * Q := mul_le_mul_of_nonneg_right a1 hQ0.le
    have e1 : 13 * k * N1 * Q = 13 * (k * N1 * Q) := by ring
    have e2 : 13 * k ^ 2 * Q = 13 * (k * k * Q) := by ring
    rw [e1, e2]
    linarith
  have hkQ : k ≤ k * Q := le_mul_of_one_le_right hk0.le hQ1
  have hk25 : 5 * 5 ≤ k * k := mul_le_mul hk5 hk5 (by norm_num) hk0.le
  have hk5k : 5 * k ≤ k * k := mul_le_mul_of_nonneg_right hk5 hk0.le
  have hc0 : 0 ≤ c := by linarith
  have hQc0 : 0 ≤ Q * c := mul_nonneg hQ0.le hc0
  have hQc1 : 1 ≤ Q * c := one_le_mul_of_one_le_of_one_le hQ1 hc1
  have hQc : 25 * (Q * c) ≤ k * k * (Q * c) := by
    have := mul_le_mul_of_nonneg_right hk25 hQc0
    linarith
  have hkQc : 5 * k * (Q * c) ≤ k * k * (Q * c) := mul_le_mul_of_nonneg_right hk5k hQc0
  have hX : k ^ 2 * Q * c = k * k * (Q * c) := by ring
  have hfirst : c * (ka + 2 * Q + 3 * k) ≤ c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) := by
    apply mul_le_mul_of_nonneg_left _ hc0
    linarith
  have e1 : c * (13 * k ^ 2 * Q + 2 * Q + 3 * (k * Q)) =
      13 * (k * k * (Q * c)) + 2 * (Q * c) + 3 * (k * (Q * c)) := by ring
  have e2 : 55 / 3 * k ^ 2 * Q * c = 55 / 3 * (k * k * (Q * c)) := by ring
  have e3 : 5 * k * (Q * c) = 5 * (k * (Q * c)) := by ring
  rw [e1] at hfirst
  rw [e2] at hfin2
  rw [e3] at hkQc
  linarith

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc}

/- English proof (translation)
Establish `H` using `segHyp_of St j`. Take `⟨hP0, -, -, hQ, hPQ⟩` from `St.levels j i`. Establish `hcb` using `coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i) (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2`. Establish `hAP : (X.bT (segPos X.TT j i) : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) < (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ)` using `hcb.2`. Establish `hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ)` using `(H.bT i).1`.

Establish `hc1 : (1 : ℝ) ≤ (X.c : ℝ)` using `by exact_mod_cast hc`. Conclude with `core_roomR St.bpos hAP hbT St.be18 St.eps0 St.de6 St.forty_epsilon_le_delta St.eps_ge St.k5 St.Q1 hP0 (hPQ.trans hQ) St.N1k St.N2 St.Y1 St.Hc hc1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) rfl`.
-/
theorem core_room (St : Std C0 Cde CE1 CE2 1 X) (hc : 1 ≤ X.c) (j : Fin (numSeg X.TT))
    (b : SegBlock (segS X.TT j) X.m) (hdig : DigitsOK X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b)
    (i : Fin (segS X.TT j)) :
    (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) + 4 ≤
      X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
  have H := segHyp_of St j
  obtain ⟨hP0, -, -, hQ, hPQ⟩ := St.levels j i
  have hcb := coarse_bounds (X.bT (segPos X.TT j i)) (X.p ^ (segG X.TT j - (segDists X.TT j).get i)) (b.rz i)
    (fun c => (hdig.1 i c).1) (hdig.2.1 i).1 (hdig.2.1 i).2
  have hAP : (X.bT (segPos X.TT j i) : ℝ) - X.k * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) <
      (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * ((X.p ^ (segG X.TT j - (segDists X.TT j).get i) : ℕ) : ℝ) := hcb.2
  have hbT : X.b' * (1 - _root_.Formalism.MainNotions.ColumnSystems.Pf.be X C0) ≤ (X.bT (segPos X.TT j i) : ℝ) := (H.bT i).1
  have hc1 : (1 : ℝ) ≤ (X.c : ℝ) := by exact_mod_cast hc
  exact core_roomR St.bpos hAP hbT St.be18 St.eps0 St.de6 St.forty_epsilon_le_delta St.eps_ge St.k5 St.Q1 hP0 (hPQ.trans hQ) St.N1k
    St.N2 St.Y1 St.Hc hc1 (Nat.cast_nonneg _) (Nat.cast_nonneg _) rfl

/- English proof (translation)
Apply `Int.le_floor.2` to reduce the goal to its premises. Use `push_cast`. Combine the linear relations using `[Int.floor_le x]`.
-/
theorem core_floor {x y : ℝ} {z : ℤ} (h : x + z ≤ y) : ⌊x⌋ + z ≤ ⌊y⌋ := by
  apply Int.le_floor.2
  push_cast
  linarith [Int.floor_le x]

/- English proof (translation)
Unfold `cap`. Establish `h2 : ∀ i ∈ (Finset.univ : Finset (Fin s)), (if (i : ℕ) < l then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0) - (if (i : ℕ) < l then ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) else 0) ≤ D`. Introduce `i _`. Use `split_ifs`. Conclude with `h i`.

Simplify using `using hD`. Establish `h3` using `Finset.sum_le_sum h2`. Rewrite `h3` using `[Finset.sum_sub_distrib]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core_capdiff (p : ℕ) {s r : ℕ} (S : SegData s) (b b' : SegBlock s r) (l : ℕ) (D : ℤ) (hD : 0 ≤ D)
    (h : ∀ i : Fin s, ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) - ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) ≤ D) :
    cap p S b l - cap p S b' l ≤ (s : ℤ) * D := by
  unfold cap
  have h2 : ∀ i ∈ (Finset.univ : Finset (Fin s)),
      (if (i : ℕ) < l then ((coarseA p S b i : ℤ) - (oEff S b i : ℤ)) else 0) -
        (if (i : ℕ) < l then ((coarseA p S b' i : ℤ) - (oEff S b' i : ℤ)) else 0) ≤ D := by
    intro i _
    split_ifs
    · exact h i
    · simpa using hD
  have h3 := Finset.sum_le_sum h2
  rw [Finset.sum_sub_distrib] at h3
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  linarith

/- English proof (translation)
Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem core_termU {A A' o o' K q : ℕ} (hA : A ≤ A' + K) (ho : o' ≤ o + 2 * (K + q)) :
    ((A : ℤ) - (o : ℤ)) - ((A' : ℤ) - (o' : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

/- English proof (translation)
Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem core_termS {A A' w w' g g' K q : ℕ} (hA : A ≤ A' + K) (hw : w' ≤ w + (K + q)) (hg : g' ≤ g + (K + q)) :
    ((A : ℤ) - ((w + g : ℕ) : ℤ)) - ((A' : ℤ) - ((w' + g' : ℕ) : ℤ)) ≤ ((3 * K + 2 * q : ℕ) : ℤ) := by
  push_cast
  omega

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `X hD hH hcB mm _ n hn1 hnc e he1 hen j b hb`. Establish `St` using `hstd X hD hH hcB`. Establish `hc : 1 ≤ X.c` using `le_trans hn1 hnc`. Take `⟨hdig, hU, hS, _, hP2⟩` from `hb`. Establish `hk5` using `St.k5`.

Establish `hQ1` using `St.Q1`. Establish `hN1pos : (1 : ℝ) ≤ X.N1` using `by exact_mod_cast St.N1pos`. Establish `hde0 : 0 ≤ X.de C0 Cde` using `le_trans (mul_nonneg (by norm_num) St.eps0) St.forty_epsilon_le_delta`. Establish `hde6` using `St.de6`. Establish `he1r : (1 : ℝ) ≤ e` using `by exact_mod_cast he1`.

Establish `hecr : (e : ℝ) ≤ X.c` using `by exact_mod_cast (le_of_lt (lt_of_lt_of_le hen hnc))`. Establish `hkdef : X.k = (X.m : ℝ) + 1` using `rfl`. Establish `hQdef : X.Q = (X.p : ℝ) ^ X.G'` using `rfl`. Establish `hk0 : 0 < X.k` using `by linarith`. Establish `hQ0 : 0 < X.Q` using `by linarith`.

Establish `hka : ka1 X = 13 * X.k * X.N1 * X.Q` using `rfl`. Establish `hkapos : 0 ≤ ka1 X`. Rewrite using `[hka]`. Establish `: (0 : ℝ) ≤ X.N1` using `by linarith`. Check the signs of the components of the expression.

Establish `hE : (((X.c - n : ℕ)) : ℝ) ≤ X.c` using `by exact_mod_cast Nat.sub_le _ _`. Establish `hE' : (((X.c - (n - e) : ℕ)) : ℝ) * ka1 X = ((X.c - n : ℕ) : ℝ) * ka1 X + e * ka1 X`. Establish `: X.c - (n - e) = (X.c - n) + e` using `by omega`. Rewrite using `[this]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : (((n - e : ℕ)) : ℝ) = (n : ℝ) - e` using `Nat.cast_sub (le_of_lt hen)`. Establish `hkQ1 : 1 ≤ X.k * X.Q` using `one_le_mul_of_one_le_of_one_le (by linarith) hQ1`. Establish `hQe1 : 1 ≤ X.Q * e` using `one_le_mul_of_one_le_of_one_le hQ1 he1r`. Establish `hx : e * ka1 X = 13 * (X.N1 * X.k * X.Q * e)` using `by rw [hka]; ring`.

Establish `hN0 : (0 : ℝ) ≤ X.N1` using `by linarith`. Establish `b1 : (X.N1 : ℝ) * e ≤ X.N1 * X.k * X.Q * e`. Use `mul_le_mul_of_nonneg_left hkQ1 (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ e))` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `b2 : (X.N1 : ℝ) * X.k ≤ X.N1 * X.k * X.Q * e`.

Use `mul_le_mul_of_nonneg_left hQe1 (mul_nonneg hN0 hk0.le)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `b3 : (X.N1 : ℝ) * (X.Q * e) ≤ X.N1 * X.k * X.Q * e`. Establish `h1k : (1 : ℝ) ≤ X.k` using `by linarith`. Use `mul_le_mul_of_nonneg_left h1k (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ X.Q * e))` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `b4 : X.k ≤ (X.N1 : ℝ) * X.k` using `le_mul_of_one_le_left hk0.le hN1pos`. Establish `b5 : X.Q * e ≤ (X.N1 : ℝ) * (X.Q * e)` using `le_mul_of_one_le_left (by linarith) hN1pos`. Establish `hnumA : 3 * X.k + 2 * (X.Q * e) ≤ e * ka1 X` using `by rw [hx]; linarith`. Establish `hnumB : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) ≤ e * ka1 X`.

Establish `e1 : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) = (X.N1 : ℝ) * e + 4 * ((X.N1 : ℝ) * X.k) + 3 * ((X.N1 : ℝ) * (X.Q * e)) + X.k + X.Q * e` using `by ring`. Rewrite using `[e1, hx]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i hi`.

Take `⟨-, hoR, -, -⟩` from `hU i hi`. Establish `room` using `core_room St hc j b hdig i`. Establish `hEk : (((X.c - n : ℕ)) : ℝ) * ka1 X ≤ X.c * ka1 X` using `mul_le_mul_of_nonneg_right hE hkapos`. Establish `hQec : X.Q * e ≤ X.Q * X.c` using `mul_le_mul_of_nonneg_left hecr hQ0.le`. Establish `hkc : 0 ≤ X.k * X.c` using `by positivity`.

Establish `goalR : ((1 + 2 * (X.p ^ X.G' * e) + b.o i : ℕ) : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ)`. Use `push_cast`. Rewrite using `[← hQdef]`. Establish `e1 : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) = (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) - X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ)`. Expand and normalize the polynomial expressions, which then agree.

Establish `e2 : (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) = X.c * ka1 X + 2 * (X.Q * X.c) + 3 * (X.k * X.c)` using `by ring`. Rewrite `hoR` using `[e1]`. Rewrite `room` using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `goalR` after adjusting the coercions.

Introduce `b' hdig' hA hU' hS' hP1' hP2'`. Use `⟨⟨hdig', ?_, ?_, hP1', ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i hi`. Take `⟨h1, h2, h3, h4⟩` from `hU' i hi`. Take `⟨-, hoR, -, -⟩` from `hU i hi`.

Use `⟨h1, ?_, h3, h4⟩` and prove the remaining obligations. Establish `h2R : (b'.o i : ℝ) ≤ (b.o i : ℝ) + 2 * (X.k + X.Q * e)`. Use `(Nat.cast_le (α := ℝ)).2 h2` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[hkdef, hQdef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hAR : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k`. Use `(Nat.cast_le (α := ℝ)).2 (hA i)` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[hkdef]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : 0 ≤ 1 - X.de C0 Cde / 4` using `by linarith`. Establish `h5` using `mul_le_mul_of_nonneg_right hAR hm`. Establish `h6 : X.k * (1 - X.de C0 Cde / 4) ≤ X.k` using `by nlinarith`. Rewrite using `[hE']`.

Establish `e1 : ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k) * (1 - X.de C0 Cde / 4) = (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) * (1 - X.de C0 Cde / 4) + X.k * (1 - X.de C0 Cde / 4)` using `by ring`. Rewrite `h5` using `[e1]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i hi`. Take `⟨h1, h2, h3, h4, -⟩` from `hS' i hi`.

Take `⟨-, -, -, hsR⟩` from `hS i hi`. Use `⟨h1, h2, h3, ?_⟩` and prove the remaining obligations. Establish `h4R : (b'.sg i : ℝ) ≤ (b.sg i : ℝ) + (X.k + X.Q * e)`. Use `(Nat.cast_le (α := ℝ)).2 h4` as an intermediate fact. Move the coercions through the operations in `at this`.

Rewrite using `[hkdef, hQdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hE']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPR : (b'.oPlus : ℝ) ≤ (b.oPlus : ℝ) + X.Q * e`.

Use `(Nat.cast_le (α := ℝ)).2 hP2'` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[hQdef]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hE']`.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `l V hV`. Establish `hterm : ∀ i : Fin (segS X.TT j), ((coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b i : ℤ)) - ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b' i : ℤ)) ≤ ((3 * (X.m + 1) + 2 * (X.p ^ X.G' * e) : ℕ) : ℤ)`. Introduce `i`. Distinguish the cases in `hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma`.

Establish `e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.w i + b.sg i` using `if_pos hi`. Establish `e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.w i + b'.sg i` using `if_pos hi`. Rewrite using `[e1, e2]`. Take `⟨-, -, -, hg, hw⟩` from `hS' i hi`. Conclude with `core_termS (hA i) hw hg`.

Establish `e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i` using `if_neg hi`. Establish `e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.o i` using `if_neg hi`. Rewrite using `[e1, e2]`. Take `⟨-, ho, -, -⟩` from `hU' i (not_lt.1 hi)`. Conclude with `core_termU (hA i) ho`.

Establish `hcd` using `core_capdiff X.p (X.seg C0 CE1 CE2 j) b b' l _ (by positivity) hterm`. Establish `hcdR` using `(Int.cast_le (R := ℝ)).2 hcd`. Move the coercions through the operations in `at hcdR`. Establish `hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1` using `by exact_mod_cast (St.segB j).2`. Establish `hD0 : (0 : ℝ) ≤ 3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)` using `by positivity`.

Establish `hsD` using `mul_le_mul_of_nonneg_right hsN hD0`. Establish `hVR` using `(Int.cast_le (R := ℝ)).2 hV`. Move the coercions through the operations in `at hVR`. Rewrite using `[add_assoc]`. Apply `core_floor` to reduce the goal to its premises.

Rewrite using `[hne]`. Use `push_cast`. Rewrite `hnumB` using `[hkdef, hQdef]`. Establish `e1 : (mm + (n : ℝ) * ka1 X) - (mm + ((n : ℝ) - e) * ka1 X) = e * ka1 X` using `by ring`. Establish `e2 : (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) = (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e))` using `rfl`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem numCore_std {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X hD hH hcB mm _ n hn1 hnc e he1 hen j b hb
  have St := hstd X hD hH hcB
  have hc : 1 ≤ X.c := le_trans hn1 hnc
  obtain ⟨hdig, hU, hS, _, hP2⟩ := hb
  have hk5 := St.k5
  have hQ1 := St.Q1
  have hN1pos : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (mul_nonneg (by norm_num) St.eps0) St.forty_epsilon_le_delta
  have hde6 := St.de6
  have he1r : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hecr : (e : ℝ) ≤ X.c := by exact_mod_cast (le_of_lt (lt_of_lt_of_le hen hnc))
  have hkdef : X.k = (X.m : ℝ) + 1 := rfl
  have hQdef : X.Q = (X.p : ℝ) ^ X.G' := rfl
  have hk0 : 0 < X.k := by linarith
  have hQ0 : 0 < X.Q := by linarith
  have hka : ka1 X = 13 * X.k * X.N1 * X.Q := rfl
  have hkapos : 0 ≤ ka1 X := by
    rw [hka]
    have : (0 : ℝ) ≤ X.N1 := by linarith
    positivity
  have hE : (((X.c - n : ℕ)) : ℝ) ≤ X.c := by exact_mod_cast Nat.sub_le _ _
  have hE' : (((X.c - (n - e) : ℕ)) : ℝ) * ka1 X = ((X.c - n : ℕ) : ℝ) * ka1 X + e * ka1 X := by
    have : X.c - (n - e) = (X.c - n) + e := by omega
    rw [this]
    push_cast
    ring
  have hne : (((n - e : ℕ)) : ℝ) = (n : ℝ) - e := Nat.cast_sub (le_of_lt hen)

  have hkQ1 : 1 ≤ X.k * X.Q := one_le_mul_of_one_le_of_one_le (by linarith) hQ1
  have hQe1 : 1 ≤ X.Q * e := one_le_mul_of_one_le_of_one_le hQ1 he1r
  have hx : e * ka1 X = 13 * (X.N1 * X.k * X.Q * e) := by rw [hka]; ring
  have hN0 : (0 : ℝ) ≤ X.N1 := by linarith
  have b1 : (X.N1 : ℝ) * e ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hkQ1 (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ e))
    nlinarith
  have b2 : (X.N1 : ℝ) * X.k ≤ X.N1 * X.k * X.Q * e := by
    have := mul_le_mul_of_nonneg_left hQe1 (mul_nonneg hN0 hk0.le)
    nlinarith
  have b3 : (X.N1 : ℝ) * (X.Q * e) ≤ X.N1 * X.k * X.Q * e := by
    have h1k : (1 : ℝ) ≤ X.k := by linarith
    have := mul_le_mul_of_nonneg_left h1k (mul_nonneg hN0 (by linarith : (0:ℝ) ≤ X.Q * e))
    nlinarith
  have b4 : X.k ≤ (X.N1 : ℝ) * X.k := le_mul_of_one_le_left hk0.le hN1pos
  have b5 : X.Q * e ≤ (X.N1 : ℝ) * (X.Q * e) := le_mul_of_one_le_left (by linarith) hN1pos
  have hnumA : 3 * X.k + 2 * (X.Q * e) ≤ e * ka1 X := by rw [hx]; linarith
  have hnumB : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) ≤
      e * ka1 X := by
    have e1 : (X.N1 : ℝ) * e + ((X.N1 : ℝ) + 1) * (X.k + X.Q * e) + (X.N1 : ℝ) * (3 * X.k + 2 * (X.Q * e)) =
        (X.N1 : ℝ) * e + 4 * ((X.N1 : ℝ) * X.k) + 3 * ((X.N1 : ℝ) * (X.Q * e)) + X.k + X.Q * e := by ring
    rw [e1, hx]
    linarith
  refine ⟨?_, ?_⟩
  ·
    intro i hi
    obtain ⟨-, hoR, -, -⟩ := hU i hi
    have room := core_room St hc j b hdig i
    have hEk : (((X.c - n : ℕ)) : ℝ) * ka1 X ≤ X.c * ka1 X := mul_le_mul_of_nonneg_right hE hkapos
    have hQec : X.Q * e ≤ X.Q * X.c := mul_le_mul_of_nonneg_left hecr hQ0.le
    have hkc : 0 ≤ X.k * X.c := by positivity
    have goalR : ((1 + 2 * (X.p ^ X.G' * e) + b.o i : ℕ) : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
      push_cast
      rw [← hQdef]
      have e1 : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) - X.de C0 Cde / 4 * (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) := by
        ring
      have e2 : (X.c : ℝ) * (ka1 X + 2 * X.Q + 3 * X.k) = X.c * ka1 X + 2 * (X.Q * X.c) + 3 * (X.k * X.c) := by ring
      rw [e1] at hoR
      rw [e2] at room
      linarith
    exact_mod_cast goalR
  · intro b' hdig' hA hU' hS' hP1' hP2'
    refine ⟨⟨hdig', ?_, ?_, hP1', ?_⟩, ?_⟩
    · intro i hi
      obtain ⟨h1, h2, h3, h4⟩ := hU' i hi
      obtain ⟨-, hoR, -, -⟩ := hU i hi
      refine ⟨h1, ?_, h3, h4⟩
      have h2R : (b'.o i : ℝ) ≤ (b.o i : ℝ) + 2 * (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h2
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      have hAR : (coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℝ) ≤ (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k := by
        have := (Nat.cast_le (α := ℝ)).2 (hA i)
        push_cast at this
        rw [hkdef]
        linarith
      have hm : 0 ≤ 1 - X.de C0 Cde / 4 := by linarith
      have h5 := mul_le_mul_of_nonneg_right hAR hm
      have h6 : X.k * (1 - X.de C0 Cde / 4) ≤ X.k := by nlinarith
      rw [hE']
      have e1 : ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) + X.k) * (1 - X.de C0 Cde / 4) =
          (coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℝ) * (1 - X.de C0 Cde / 4) + X.k * (1 - X.de C0 Cde / 4) := by ring
      rw [e1] at h5
      linarith
    · intro i hi
      obtain ⟨h1, h2, h3, h4, -⟩ := hS' i hi
      obtain ⟨-, -, -, hsR⟩ := hS i hi
      refine ⟨h1, h2, h3, ?_⟩
      have h4R : (b'.sg i : ℝ) ≤ (b.sg i : ℝ) + (X.k + X.Q * e) := by
        have := (Nat.cast_le (α := ℝ)).2 h4
        push_cast at this
        rw [hkdef, hQdef]
        linarith
      rw [hE']
      linarith
    · have hPR : (b'.oPlus : ℝ) ≤ (b.oPlus : ℝ) + X.Q * e := by
        have := (Nat.cast_le (α := ℝ)).2 hP2'
        push_cast at this
        rw [hQdef]
        linarith
      rw [hE']
      linarith
    · intro l V hV
      have hterm : ∀ i : Fin (segS X.TT j),
          ((coarseA X.p (X.seg C0 CE1 CE2 j) b i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b i : ℤ)) -
            ((coarseA X.p (X.seg C0 CE1 CE2 j) b' i : ℤ) - (oEff (X.seg C0 CE1 CE2 j) b' i : ℤ)) ≤
            ((3 * (X.m + 1) + 2 * (X.p ^ X.G' * e) : ℕ) : ℤ) := by
        intro i
        by_cases hi : (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.w i + b.sg i := if_pos hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.w i + b'.sg i := if_pos hi
          rw [e1, e2]
          obtain ⟨-, -, -, hg, hw⟩ := hS' i hi
          exact core_termS (hA i) hw hg
        · have e1 : oEff (X.seg C0 CE1 CE2 j) b i = b.o i := if_neg hi
          have e2 : oEff (X.seg C0 CE1 CE2 j) b' i = b'.o i := if_neg hi
          rw [e1, e2]
          obtain ⟨-, ho, -, -⟩ := hU' i (not_lt.1 hi)
          exact core_termU (hA i) ho
      have hcd := core_capdiff X.p (X.seg C0 CE1 CE2 j) b b' l _ (by positivity) hterm
      have hcdR := (Int.cast_le (R := ℝ)).2 hcd
      push_cast at hcdR
      have hsN : ((segS X.TT j : ℕ) : ℝ) ≤ X.N1 := by exact_mod_cast (St.segB j).2
      have hD0 : (0 : ℝ) ≤ 3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e) := by positivity
      have hsD := mul_le_mul_of_nonneg_right hsN hD0
      have hVR := (Int.cast_le (R := ℝ)).2 hV
      push_cast at hVR
      rw [add_assoc]
      apply core_floor
      rw [hne]
      push_cast
      rw [hkdef, hQdef] at hnumB
      have e1 : (mm + (n : ℝ) * ka1 X) - (mm + ((n : ℝ) - e) * ka1 X) = e * ka1 X := by ring
      have e2 : (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) =
          (X.N1 : ℝ) * (3 * ((X.m : ℝ) + 1) + 2 * ((X.p : ℝ) ^ X.G' * e)) := rfl
      linarith

/- English proof (translation)
The claim follows from `TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => numCore_std h.2) thr_std`.
-/
theorem numCore_thr : RestNumCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => numCore_std h.2) thr_std

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Introduce `X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP hK i hi`. Establish `hs` using `hstd X hD hI hc`. Establish `hk5` using `hs.k5`. Establish `hk : (0 : ℝ) < X.k` using `by linarith`. Establish `hkk : X.k = (X.m : ℝ) + 1` using `rfl`.

Establish `hLK` using `hs.LaK`. Establish `hN1 : (1 : ℝ) ≤ X.N1` using `by exact_mod_cast hs.N1pos`. Establish `hLa1` using `hs.La1`. Establish `hLa0 : (0 : ℝ) ≤ X.La C0` using `le_trans zero_le_one hLa1`. Establish `hde6` using `hs.de6`.

Establish `hp0 : (0 : ℝ) < X.p` using `by have := hs.p5; exact_mod_cast (show 0 < X.p by omega)`. Establish `hp2pos : (0 : ℝ) < (X.p : ℝ) ^ 2` using `by positivity`. Establish `hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2`. Establish `: (5 : ℝ) ≤ X.p` using `by exact_mod_cast hs.p5`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hde0 : 0 ≤ X.de C0 Cde` using `le_trans (by positivity) hLK`. Use `set A0 : ℝ := ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) with hA0`. Use `set Aa : Fin (segS X.TT j) → ℝ := fun l => (clA C0 CE1 CE2 X j rz ry l : ℝ) with hAa`. Establish `hAl : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → Aa l ≤ A0`. Introduce `l hl`.

Establish `h` using `(coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd l).1 (lt_of_le_of_lt hl hi)`. Establish `h0 : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ)` using `Nat.cast_nonneg _`. Use `show (clA C0 CE1 CE2 X j rz ry l : ℝ) ≤ _`. Use the polynomial consequences of the given equalities and inequalities. Establish `hAnn : ∀ l : Fin (segS X.TT j), (0 : ℝ) ≤ Aa l` using `fun l => by show (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ); exact Nat.cast_nonneg _`.

Establish `hA00 : (0 : ℝ) ≤ A0` using `le_trans (hAnn i) (hAl i le_rfl)`. Establish `h4p : 4 / (X.p : ℝ) ^ 2 ≤ 1` using `by rw [div_le_one hp2pos]; linarith`. Establish `hsum : ∀ l : Fin (segS X.TT j), (∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0) ≤ 4 * Aa l / (X.p : ℝ) ^ 2` using `fun l => coarse_degree_prefix_sum hs le_rfl j rz ry hd l`. Establish `hkap : ∀ l : Fin (segS X.TT j), ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ 4 * Aa l / (X.p : ℝ) ^ 2`. Introduce `l`.

Establish `h1` using `pf_prev_le hP.1 l.val (by omega)`. Establish `h2 : ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) ≤ ∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0`. Use `push_cast`. Use `Finset.sum_le_sum fun x _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Take `⟨-, -, -, hw, -, -, -, -⟩` from `pair_top hP.1 x show _ ≤ ((clA C0 CE1 CE2 X j rz ry x : ℕ) : ℝ)`. Conclude with `hw` after adjusting the coercions. Conclude with `le_rfl`. Establish `h1' : ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ)` using `by exact_mod_cast h1`. Combine the linear relations using `[hsum l]`.

Establish `hrho : ∀ l : Fin (segS X.TT j), ((pairRho mu l.val : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2`. Introduce `l`. Establish `h1` using `pf_rho_le hP.1 l`. Take `⟨-, -, -, hw, -, -, -, -⟩` from `pair_top hP.1 l`. Establish `h1' : ((pairRho mu l.val : ℤ) : ℝ) ≤ ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) + ((pairW mu l.val : ℤ) : ℝ)` using `by exact_mod_cast h1`.

Establish `hw' : ((pairW mu l.val : ℤ) : ℝ) ≤ Aa l` using `by show _ ≤ ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℝ)`. Conclude with `hw` after adjusting the coercions. Combine the linear relations using `[hkap l]`. Establish `hcup : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → ((pairC mu l.val : ℤ) : ℝ) ≤ 2 * A0`. Introduce `l hl`.

Establish `h1` using `pairC_le_sum hP.1 l`. Establish `hA : (A : ℝ) ≤ A0` using `hA2`. Establish `h3 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ Aa l`. Establish `e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2)` using `by ring`. Rewrite using `[e]`.

Use polynomial arithmetic with `[hAnn l]`. Use `hsum l` as an intermediate fact. Use `hAl l hl` as an intermediate fact. Simplify using `only [hAa] at *`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hkept : ∀ l : Fin (segS X.TT j), ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) - ((pairRho mu l.val : ℤ) : ℝ) + 4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 ≤ X.La C0 * max ((pairC mu l.val : ℤ) : ℝ) (Aa l) / X.k`. Introduce `l`. Establish `h` using `(hK l).1`. Rewrite using `[hkk]`. Move the coercions through the operations in `at h ⊢`.

Conclude with `h`. Use `set δ : ℝ := 3 * A0 * (4 / (X.p : ℝ) ^ 2 + X.La C0 / X.k) with hδ`. Establish `hlow : ∀ n : ℕ, ∀ hn : n ≤ i.val, (A : ℝ) - n * δ ≤ ((pairC mu n : ℤ) : ℝ)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro _`. Rewrite using `[pairC_zero hP.1]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `hn`.

Establish `ih'` using `ih (by omega)`. Use `set l : Fin (segS X.TT j) := ⟨n, by omega⟩ with hl`. Establish `eC : pairC mu (n + 1) = pairC mu n + ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℤ) - pairO mu (clA C0 CE1 CE2 X j rz ry) l` using `by unfold pairO; ring`. Establish `hk1` using `hkept l`. Establish `hr` using `hrho l`.

Establish `hcl` using `hcup l (by show n ≤ i.val; omega)`. Establish `hal` using `hAl l (by show n ≤ i.val; omega)`. Establish `hmax : max ((pairC mu n : ℤ) : ℝ) (Aa l) ≤ 2 * A0` using `max_le hcl (by linarith)`. Establish `hLk : 0 ≤ X.La C0 / X.k` using `div_nonneg hLa0 hk.le`. Establish `hm0 : (0 : ℝ) ≤ 4 * (Aa l + X.m) / (X.p : ℝ) ^ 2`.

Use `hAnn l` as an intermediate fact. Check the signs of the components of the expression. Establish `hOl : ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 + X.La C0 * (2 * A0) / X.k`. Establish `: X.La C0 * max ((pairC mu n : ℤ) : ℝ) (Aa l) / X.k ≤ X.La C0 * (2 * A0) / X.k`. Apply `div_le_div_of_nonneg_right _ hk.le` to reduce the goal to its premises.

Conclude with `mul_le_mul_of_nonneg_left hmax hLa0`. Simplify using `only [hl] at hk1 hr ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd1 : 4 * Aa l / (X.p : ℝ) ^ 2 + X.La C0 * (2 * A0) / X.k ≤ δ`. Establish `e1 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ 3 * A0 * (4 / (X.p : ℝ) ^ 2)`.

Establish `e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2)` using `by ring`. Rewrite using `[e]`. Establish `: (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : X.La C0 * (2 * A0) / X.k ≤ 3 * A0 * (X.La C0 / X.k)`.

Establish `e : X.La C0 * (2 * A0) / X.k = 2 * A0 * (X.La C0 / X.k)` using `by ring`. Rewrite using `[e]`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hδ]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[eC]`. Use `push_cast`. Simplify using `only [hl] at hOl hd1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hci_low` using `hlow i.val le_rfl`.

Establish `hsN : (i.val : ℝ) ≤ X.N1`. Use `(hs.segB j).2` as an intermediate fact. Establish `: i.val ≤ X.N1` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hδ0 : 0 ≤ δ` using `by rw [hδ]; positivity`.

Establish `hAlo : A0 * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ)` using `hA1`. Establish `hdich` using `(coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd i).1 hi`. Establish `sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k` using `hs.N1k`. Establish `hkp : X.k ^ 2 ≤ (X.p : ℝ)`. Establish `hY2 : (1 : ℝ) ≤ X.Y ^ 2` using `one_le_pow₀ hs.Y1`.

Use polynomial arithmetic with `[hs.pk, mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)]`. Establish `hde40 : 40 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde` using `hLK`. Establish `hq1 : 4 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde / 10`. Establish `e : 4 * X.N1 * X.La C0 / X.k = (40 * X.N1 * X.La C0 / X.k) / 10` using `by ring`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq2 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde / 80`. Establish `hk4 : X.k ^ 4 ≤ (X.p : ℝ) ^ 2`. Combine the equalities or inequalities in the displayed calculation. Establish `h40 : 40 / X.k ≤ X.de C0 Cde`.

Use `le_trans ?_ hde40` and prove the remaining obligations. Rewrite using `[div_le_div_iff_of_pos_right hk]`. Establish `h1 : 1 ≤ (X.N1 : ℝ) * X.La C0` using `one_le_mul_of_one_le_of_one_le hN1 hLa1`. Establish `e : 40 * (X.N1 : ℝ) * X.La C0 = 40 * ((X.N1 : ℝ) * X.La C0)` using `by ring`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hN1le : (X.N1 : ℝ) ≤ X.k` using `by linarith`. Establish `h1 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ 12 * X.k / X.k ^ 4`. Apply `div_le_div₀ (by positivity) (by linarith) (by positivity) hk4` to reduce the goal to its premises. Establish `h2 : 12 * X.k / X.k ^ 4 ≤ (40 / X.k) / 80`.

Rewrite using `[div_div, div_le_div_iff₀ (by positivity) (by positivity)]`. Establish `hk3 : (5 : ℝ) ^ 3 ≤ X.k ^ 3`. Use `pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hk5 3` as an intermediate fact. Conclude with `this`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hk3 (by positivity : (0:ℝ) ≤ X.k ^ 2)]`.

Establish `h3 : (40 / X.k) / 80 ≤ X.de C0 Cde / 80` using `by linarith`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hci_ge : Aa i ≤ ((pairC mu i.val : ℤ) : ℝ)`. Establish `h1 : (i.val : ℝ) * δ ≤ X.N1 * δ` using `mul_le_mul_of_nonneg_right hsN hδ0`. Establish `hexp : X.N1 * δ = A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k)`.

Rewrite using `[hδ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlow2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) ≤ ((pairC mu i.val : ℤ) : ℝ)`. Establish `e : A0 * (1 - X.N1 * X.La C0 / X.k) = A0 - A0 * (X.N1 * X.La C0 / X.k)` using `by ring`. Establish `e2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) = A0 - A0 * (X.N1 * X.La C0 / X.k) - A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k)` using `by ring`.

Rewrite using `[e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hε : (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2) * (1 + X.de C0 Cde) ≤ X.de C0 Cde`. Establish `hsum' : 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde * (9 / 80)` using `by linarith`. Establish `hε0 : 0 ≤ 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `key : Aa i * (1 + X.de C0 Cde) ≤ A0` using `le_of_lt hdich`. Use `set ε : ℝ := 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 with hεd`. Establish `hε1 : 0 ≤ 1 - ε` using `by linarith`. Establish `hprod : 1 ≤ (1 + X.de C0 Cde) * (1 - ε)` using `by nlinarith`.

Establish `g1 : Aa i ≤ Aa i * ((1 + X.de C0 Cde) * (1 - ε))` using `le_mul_of_one_le_right (hAnn i) hprod`. Establish `g2 : Aa i * ((1 + X.de C0 Cde) * (1 - ε)) ≤ A0 * (1 - ε)`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right key hε1`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hmaxc : max ((pairC mu i.val : ℤ) : ℝ) (Aa i) = ((pairC mu i.val : ℤ) : ℝ)` using `max_eq_left hci_ge`. Establish `hk1` using `hkept i`. Rewrite `hk1` using `[hmaxc]`. Establish `hm0 : (0 : ℝ) ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2` using `by have := hAnn i; positivity`. Establish `hr` using `hrho i`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : Aa i * (1 + 4 / (X.p : ℝ) ^ 2) = Aa i + 4 * Aa i / (X.p : ℝ) ^ 2` using `by ring show _ ≤ Aa i * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k`. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu` using `pf_u_ge hP.1 i`.

Establish `hu' : ((pairSg mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((pairRho mu i.val : ℤ) : ℝ)` using `by exact_mod_cast hu`. Establish `hkp'` using `hkap i`. Establish `h4 : 4 * Aa i / (X.p : ℝ) ^ 2 ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2`. Apply `div_le_div_of_nonneg_right _ hp2pos.le` to reduce the goal to its premises. Establish `: (0 : ℝ) ≤ X.m` using `Nat.cast_nonneg _`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc2` using `hcup i le_rfl`. Establish `hfin : X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k ≤ 2 * X.La C0 * A0 / X.k`. Apply `div_le_div_of_nonneg_right _ hk.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem keptPair_bounds {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    PairSAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ hD hI hc j rz ry hd A hA1 hA2 mu lam hP hK i hi
  have hs := hstd X hD hI hc
  have hk5 := hs.k5
  have hk : (0 : ℝ) < X.k := by linarith
  have hkk : X.k = (X.m : ℝ) + 1 := rfl
  have hLK := hs.LaK
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast hs.N1pos
  have hLa1 := hs.La1
  have hLa0 : (0 : ℝ) ≤ X.La C0 := le_trans zero_le_one hLa1
  have hde6 := hs.de6
  have hp0 : (0 : ℝ) < X.p := by have := hs.p5; exact_mod_cast (show 0 < X.p by omega)
  have hp2pos : (0 : ℝ) < (X.p : ℝ) ^ 2 := by positivity
  have hp25 : (25 : ℝ) ≤ (X.p : ℝ) ^ 2 := by
    have : (5 : ℝ) ≤ X.p := by exact_mod_cast hs.p5
    nlinarith
  have hde0 : 0 ≤ X.de C0 Cde := le_trans (by positivity) hLK
  set A0 : ℝ := ((X.seg C0 CE1 CE2 j).A0 X.p : ℝ) with hA0
  set Aa : Fin (segS X.TT j) → ℝ := fun l => (clA C0 CE1 CE2 X j rz ry l : ℝ) with hAa

  have hAl : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → Aa l ≤ A0 := by
    intro l hl
    have h := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd l).1 (lt_of_le_of_lt hl hi)
    have h0 : (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ) := Nat.cast_nonneg _
    show (clA C0 CE1 CE2 X j rz ry l : ℝ) ≤ _
    nlinarith
  have hAnn : ∀ l : Fin (segS X.TT j), (0 : ℝ) ≤ Aa l := fun l => by
    show (0 : ℝ) ≤ (clA C0 CE1 CE2 X j rz ry l : ℝ); exact Nat.cast_nonneg _
  have hA00 : (0 : ℝ) ≤ A0 := le_trans (hAnn i) (hAl i le_rfl)
  have h4p : 4 / (X.p : ℝ) ^ 2 ≤ 1 := by rw [div_le_one hp2pos]; linarith

  have hsum : ∀ l : Fin (segS X.TT j), (∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 :=
    fun l => coarse_degree_prefix_sum hs le_rfl j rz ry hd l

  have hkap : ∀ l : Fin (segS X.TT j), ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤ 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_prev_le hP.1 l.val (by omega)
    have h2 : ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) ≤
        ∑ x : Fin (segS X.TT j), if x.val < l.val then Aa x else 0 := by
      push_cast
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs
      · obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 x
        show _ ≤ ((clA C0 CE1 CE2 X j rz ry x : ℕ) : ℝ)
        exact_mod_cast hw
      · exact le_rfl
    have h1' : ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((∑ x : Fin (segS X.TT j), if x.val < l.val then pairW mu x.val else 0 : ℤ) : ℝ) := by exact_mod_cast h1
    linarith [hsum l]
  have hrho : ∀ l : Fin (segS X.TT j), ((pairRho mu l.val : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 := by
    intro l
    have h1 := pf_rho_le hP.1 l
    obtain ⟨-, -, -, hw, -, -, -, -⟩ := pair_top hP.1 l
    have h1' : ((pairRho mu l.val : ℤ) : ℝ) ≤ ((mu ⟨2 * l.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) +
        ((pairW mu l.val : ℤ) : ℝ) := by exact_mod_cast h1
    have hw' : ((pairW mu l.val : ℤ) : ℝ) ≤ Aa l := by
      show _ ≤ ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℝ)
      exact_mod_cast hw
    linarith [hkap l]

  have hcup : ∀ l : Fin (segS X.TT j), l.val ≤ i.val → ((pairC mu l.val : ℤ) : ℝ) ≤ 2 * A0 := by
    intro l hl
    have h1 := pairC_le_sum hP.1 l
    have hA : (A : ℝ) ≤ A0 := hA2
    have h3 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ Aa l := by
      have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
      rw [e]; nlinarith [hAnn l]
    have := hsum l
    have := hAl l hl
    simp only [hAa] at *
    linarith

  have hkept : ∀ l : Fin (segS X.TT j), ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) - ((pairRho mu l.val : ℤ) : ℝ) +
      4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 ≤ X.La C0 * max ((pairC mu l.val : ℤ) : ℝ) (Aa l) / X.k := by
    intro l
    have h := (hK l).1
    rw [hkk]
    push_cast at h ⊢
    exact h

  set δ : ℝ := 3 * A0 * (4 / (X.p : ℝ) ^ 2 + X.La C0 / X.k) with hδ
  have hlow : ∀ n : ℕ, ∀ hn : n ≤ i.val, (A : ℝ) - n * δ ≤ ((pairC mu n : ℤ) : ℝ) := by
    intro n
    induction n with
    | zero => intro _; rw [pairC_zero hP.1]; simp
    | succ n ih =>
      intro hn
      have ih' := ih (by omega)
      set l : Fin (segS X.TT j) := ⟨n, by omega⟩ with hl
      have eC : pairC mu (n + 1) = pairC mu n + ((clA C0 CE1 CE2 X j rz ry l : ℕ) : ℤ) -
          pairO mu (clA C0 CE1 CE2 X j rz ry) l := by unfold pairO; ring
      have hk1 := hkept l
      have hr := hrho l
      have hcl := hcup l (by show n ≤ i.val; omega)
      have hal := hAl l (by show n ≤ i.val; omega)
      have hmax : max ((pairC mu n : ℤ) : ℝ) (Aa l) ≤ 2 * A0 := max_le hcl (by linarith)
      have hLk : 0 ≤ X.La C0 / X.k := div_nonneg hLa0 hk.le
      have hm0 : (0 : ℝ) ≤ 4 * (Aa l + X.m) / (X.p : ℝ) ^ 2 := by
        have := hAnn l; positivity
      have hOl : ((pairO mu (clA C0 CE1 CE2 X j rz ry) l : ℤ) : ℝ) ≤ Aa l + 4 * Aa l / (X.p : ℝ) ^ 2 +
          X.La C0 * (2 * A0) / X.k := by
        have : X.La C0 * max ((pairC mu n : ℤ) : ℝ) (Aa l) / X.k ≤ X.La C0 * (2 * A0) / X.k := by
          apply div_le_div_of_nonneg_right _ hk.le
          exact mul_le_mul_of_nonneg_left hmax hLa0
        simp only [hl] at hk1 hr ⊢
        linarith
      have hd1 : 4 * Aa l / (X.p : ℝ) ^ 2 + X.La C0 * (2 * A0) / X.k ≤ δ := by
        have e1 : 4 * Aa l / (X.p : ℝ) ^ 2 ≤ 3 * A0 * (4 / (X.p : ℝ) ^ 2) := by
          have e : 4 * Aa l / (X.p : ℝ) ^ 2 = Aa l * (4 / (X.p : ℝ) ^ 2) := by ring
          rw [e]
          have : (0 : ℝ) ≤ 4 / (X.p : ℝ) ^ 2 := by positivity
          nlinarith
        have e2 : X.La C0 * (2 * A0) / X.k ≤ 3 * A0 * (X.La C0 / X.k) := by
          have e : X.La C0 * (2 * A0) / X.k = 2 * A0 * (X.La C0 / X.k) := by ring
          rw [e]; nlinarith
        rw [hδ]; linarith
      rw [eC]
      push_cast
      simp only [hl] at hOl hd1
      linarith

  have hci_low := hlow i.val le_rfl
  have hsN : (i.val : ℝ) ≤ X.N1 := by
    have := (hs.segB j).2
    have : i.val ≤ X.N1 := by omega
    exact_mod_cast this
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  have hAlo : A0 * (1 - X.N1 * X.La C0 / X.k) ≤ (A : ℝ) := hA1
  have hdich := (coarse_degree_alternative le_rfl hs j (digitBlock rz ry) hd i).1 hi

  have sq_level_le_degree : 2 * (X.N1 : ℝ) + 3 ≤ X.k := hs.N1k
  have hkp : X.k ^ 2 ≤ (X.p : ℝ) := by
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hs.Y1
    nlinarith [hs.pk, mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)]
  have hde40 : 40 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde := hLK
  have hq1 : 4 * X.N1 * X.La C0 / X.k ≤ X.de C0 Cde / 10 := by
    have e : 4 * X.N1 * X.La C0 / X.k = (40 * X.N1 * X.La C0 / X.k) / 10 := by ring
    rw [e]; linarith
  have hq2 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde / 80 := by
    have hk4 : X.k ^ 4 ≤ (X.p : ℝ) ^ 2 := by
      calc X.k ^ 4 = (X.k ^ 2) ^ 2 := by ring
        _ ≤ (X.p : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hkp 2
    have h40 : 40 / X.k ≤ X.de C0 Cde := by
      refine le_trans ?_ hde40
      rw [div_le_div_iff_of_pos_right hk]
      have h1 : 1 ≤ (X.N1 : ℝ) * X.La C0 := one_le_mul_of_one_le_of_one_le hN1 hLa1
      have e : 40 * (X.N1 : ℝ) * X.La C0 = 40 * ((X.N1 : ℝ) * X.La C0) := by ring
      rw [e]; linarith
    have hN1le : (X.N1 : ℝ) ≤ X.k := by linarith
    have h1 : 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ 12 * X.k / X.k ^ 4 := by
      apply div_le_div₀ (by positivity) (by linarith) (by positivity) hk4
    have h2 : 12 * X.k / X.k ^ 4 ≤ (40 / X.k) / 80 := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hk3 : (5 : ℝ) ^ 3 ≤ X.k ^ 3 := by
        have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hk5 3
        exact this
      nlinarith [mul_le_mul_of_nonneg_left hk3 (by positivity : (0:ℝ) ≤ X.k ^ 2)]
    have h3 : (40 / X.k) / 80 ≤ X.de C0 Cde / 80 := by linarith
    linarith
  have hci_ge : Aa i ≤ ((pairC mu i.val : ℤ) : ℝ) := by

    have h1 : (i.val : ℝ) * δ ≤ X.N1 * δ := mul_le_mul_of_nonneg_right hsN hδ0
    have hexp : X.N1 * δ = A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by
      rw [hδ]; ring
    have hlow2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) ≤ ((pairC mu i.val : ℤ) : ℝ) := by
      have e : A0 * (1 - X.N1 * X.La C0 / X.k) = A0 - A0 * (X.N1 * X.La C0 / X.k) := by ring
      have e2 : A0 * (1 - (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2)) =
          A0 - A0 * (X.N1 * X.La C0 / X.k) - A0 * (12 * X.N1 / (X.p : ℝ) ^ 2 + 3 * X.N1 * X.La C0 / X.k) := by ring
      rw [e2]
      linarith
    have hε : (4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2) * (1 + X.de C0 Cde) ≤ X.de C0 Cde := by
      have hsum' : 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 ≤ X.de C0 Cde * (9 / 80) := by linarith
      have hε0 : 0 ≤ 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 := by positivity
      nlinarith

    have key : Aa i * (1 + X.de C0 Cde) ≤ A0 := le_of_lt hdich
    set ε : ℝ := 4 * X.N1 * X.La C0 / X.k + 12 * X.N1 / (X.p : ℝ) ^ 2 with hεd
    have hε1 : 0 ≤ 1 - ε := by linarith
    have hprod : 1 ≤ (1 + X.de C0 Cde) * (1 - ε) := by nlinarith
    have g1 : Aa i ≤ Aa i * ((1 + X.de C0 Cde) * (1 - ε)) := le_mul_of_one_le_right (hAnn i) hprod
    have g2 : Aa i * ((1 + X.de C0 Cde) * (1 - ε)) ≤ A0 * (1 - ε) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right key hε1
    linarith
  have hmaxc : max ((pairC mu i.val : ℤ) : ℝ) (Aa i) = ((pairC mu i.val : ℤ) : ℝ) := max_eq_left hci_ge
  have hk1 := hkept i
  rw [hmaxc] at hk1
  have hm0 : (0 : ℝ) ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by have := hAnn i; positivity
  have hr := hrho i
  refine ⟨?_, ?_⟩
  · have e : Aa i * (1 + 4 / (X.p : ℝ) ^ 2) = Aa i + 4 * Aa i / (X.p : ℝ) ^ 2 := by ring
    show _ ≤ Aa i * (1 + 4 / (X.p : ℝ) ^ 2) + X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k
    rw [e]
    linarith
  ·
    have hu := pf_u_ge hP.1 i
    have hu' : ((pairSg mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) -
        ((mu ⟨2 * i.val + 1, by omega⟩ (0 : Fin X.m).succ : ℤ) : ℝ) ≤
        ((pairO mu (clA C0 CE1 CE2 X j rz ry) i : ℤ) : ℝ) - ((pairRho mu i.val : ℤ) : ℝ) := by exact_mod_cast hu
    have hkp' := hkap i
    have h4 : 4 * Aa i / (X.p : ℝ) ^ 2 ≤ 4 * (Aa i + X.m) / (X.p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ hp2pos.le
      have : (0 : ℝ) ≤ X.m := Nat.cast_nonneg _
      linarith
    have hc2 := hcup i le_rfl
    have hfin : X.La C0 * ((pairC mu i.val : ℤ) : ℝ) / X.k ≤ 2 * X.La C0 * A0 / X.k := by
      apply div_le_div_of_nonneg_right _ hk.le
      nlinarith
    linarith

/- English proof (translation)
The claim follows from `TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1) fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 => keptPair_bounds fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc`.
-/
theorem keptPair_thr : RestPairS :=
  TransportedAlt.of_explicit (fun _ => 1) (fun _ _ => 1) (fun Cc _ CE1 CE2 _ => T2 CE1 CE2 Cc 1)
    fun _ _ _ _ _ _ _ _ _ _ hCc hC0 _ h1 h2 _ _ _ _ _ _ _ _ _ t1 t2 t3 t4 t5 =>
      keptPair_bounds fun _ hD hI hc => std_of hCc hC0 h1 h2 le_rfl t1 t2 t3 t4 t5 hD hI hc

/- English proof (translation)
The claim follows from `kept_blocks_of_S_line keptPair_thr`.
-/
theorem keptBlocks : KeptBlocksBeyondThreshold := kept_blocks_of_S_line keptPair_thr

/- English proof (translation)
The claim follows from `have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D) (one_segment_of_upper_lower hU hL) hA2 (restExt_of …`.
-/
theorem closed_of_bounds {D : Formalism.BasicNotions.D7} (h3 : adm3 D) (hU : RestUp) (hL : RestLow) (hL1 : PartnersToFactors)
    (hLift : RestLift) : Closed (ExtendedAllConclusions D) :=
  have hA2 : RemainderSegmentBoundSecond D := restAlt2_of (restSegLow_of hL) (dimHH_of h3) charZeroAt
  closed_of_rests (fun _ _ _ => segment_statement_holds D _ _ _) (restFree D) (remainderSegmentBoundFirst D) (rest2 D) (restAlt3 D)
    (one_segment_of_upper_lower hU hL) hA2 (restExt_of restRk hL1 hLift hA2)

/- English proof (translation)
Introduce `hA` and use `have hPL := h hA have hY : DimYAt := dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D) have hCD : ChainDimAt := chainDim_of hY have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1 have hT : RestTail := restTail_of hCD hNB restPairCount (restNotKeptWt …`.
-/
theorem tensor_of_pairLift {D : Formalism.BasicNotions.D7} (h : admitted D → RestPairLift) : ExtendedClosedForm D := fun hA =>
  have hPL := h hA
  have hY : DimYAt := dimY_of (D := D) hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.1 (stWeylAt D)
  have hCD : ChainDimAt := chainDim_of hY
  have hNB : NumBranchAt := numBranch_of hA.2.1 hA.2.2.1
  have hT : RestTail := restTail_of hCD hNB restPairCount
    (restNotKeptWt_of (wtBound_of hCD) (restBracket_of (restPairFacts_of restNUp) coarse_degrees_large_holds))
  have hB : BlockRankAt := blockRankAt
  have hCU : RestCountUp := upper_count_of_top_rows hCD hNB top_rows_bound_holds
  have hMU : RestMatchUp := restMatchUp_of (restFirstRows_of (restSTopRows_of top_rows_bound_holds))
  have hCL : RestCountLow := restCountLow_of'' hCD hT hMU keptBlocks
  closed_of_bounds hA.2.2.1 (restUp_of hB hY charZeroAt hCU) (restLow_of hB hY charZeroAt hCL) partners_to_factors_holds
    (restLift_of (restLiftVec_of hPL))

/- English proof (translation)
The claim follows from `tensor_of_pairLift fun hA => paired_lifts_of_identity hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res))) (rest_assumptions_of_three_interfaces hA restCols restPre (restTCore_of_seg (restSegCor …`.
-/
theorem tensor_closed (D : Formalism.BasicNotions.D7) : ExtendedClosedForm D :=
  tensor_of_pairLift fun hA =>
    paired_lifts_of_identity hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      (restRawTail1_of (third_key_of_order key3Ord) (local_fourth_of_order (loc4Ord_of (loc4Div_of loc4Res)))
        (rest_assumptions_of_three_interfaces hA restCols restPre (restTCore_of_seg (restSegCore_of_num numCore_thr))))
      (restForm_of_oplus (Formalism.MainNotions.G.GLWeightTheory.lemma_five_two_first_holds D) restOPlus)

end Numbers

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G

/- English proof (translation)
The claim follows from `ExtremalProjector.extremal_projector_statement`.
-/
theorem tools : ExtremalProjectorTools where
  extremalProjectorAlt := ExtremalProjector.extremal_projector_statement

/- English proof (translation)
The claim follows from `flipOneThree.Pf.theorem_I_closed_form_holds p13A := GramWindowAlt.theorem_A_closed_form_holds p15 := tensor_closed windowClauseTwo := Model.gl_branching_dimension windowClauseThree := Model.weyl_dual_weight_admissible lWeylV := Model.weylV_proved lWitt := WittPI.wittIdentity_hold …`.
-/
theorem inputs : Loc8All where
  p13B := flipOneThree.Pf.theorem_I_closed_form_holds
  p13A := GramWindowAlt.theorem_A_closed_form_holds
  p15 := tensor_closed
  windowClauseTwo := Model.gl_branching_dimension
  windowClauseThree := Model.weyl_dual_weight_admissible
  lWeylV := Model.weylV_proved
  lWitt := WittPI.wittIdentity_holds
  tFlatTop := Model.flatTop
  tFlatHH := Model.flatHH
  hyperLatticeBasis := Model.dualHeightBasis
  hyperDualInclusion := Model.dualInclusionLattices
  tBePerfect := Model.bePerfect
  tHLSpans := Model.hlSpans
  tTestSide := Model.testSide
  tLPOneEvery := Model.lPOneEvery
  tCartanDomain := Model.cartanDomain_proved
  tCartanOnto := Model.cartanOnto_proved
  tKP1 := CountingStatementReduction.key_positivity_condition
  tKP2 := Joints.saturated_restriction_holds
  tKP3 := Joints.restriction_dimension_holds
  tRES := CountingStatementReduction.residue_division_transfer
  thresholdClauseOne := CountingStatementReduction.positivity_condition_eventually
  thresholdClauseThree := CountingStatementReduction.exponent_bound_eventually
  instanceClauseEight := fun D X => PolBridge.combined_weight_of_nested_sets D X (GLWeightTheory.weight_condition_from_integral_form D) (ColumnFamilies.Top.b15 D)

/- English proof (translation)
The claim follows from `first_theorem_threshold_functions tools inputs`.
-/
theorem rangeOne_abs :
    ∃ (T0 : ℝ) (T2 C : ℝ → ℝ), 0 < T0 ∧ ∀ C₀ : ℝ, T0 ≤ C₀ → 0 < T2 C₀ ∧ 0 < C C₀ ∧ ∀ CH : ℝ, T2 C₀ ≤ CH →
      ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.flipOneThree.Conclusion2 D C₀ CH (C C₀) :=
  first_theorem_threshold_functions tools inputs

end GlobalTheory.EX.RangeOne
