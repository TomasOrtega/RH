import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageTwoLeLAndSigns
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PageRowsOfLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAuxiliaryWeightsAtRunWeights
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardComponentsLeAtGoodEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIntegralThetaCombinationNonzeroOnComponentStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ThetaIntegralWeights

/- English proof (translation)
Take `⟨-, hS, -, -, -⟩` from `hP`. Take `⟨-, -, -, h4, -, h6, -, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, hc, -⟩` from `hS`. Take `⟨-, hLP, -⟩` from `hL`. Take `⟨-, hFP, -⟩` from `hF`. Establish `key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → ((Tn : ℤ) + WeightFamilies.dimY D j + 2 ≤ wL.aP τ i) ∧ (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i`.

Introduce `τ i hi`. Establish `hg` using `hLP τ i`. Establish `hlt : ¬ (i.1 + 1 < (D.R.sigW j).1)` using `by omega`. Simplify using `only [gapZ, hlt, dif_neg, if_neg, not_false_eq_true] at hg`. Establish `ha : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ)`.

Use `h6 τ i hi` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha' : 2 * (Tn : ℤ) ^ 2 ≤ (ka.aP τ i : ℤ)` using `by exact_mod_cast ha`. Establish `k` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities (ka.aP τ i : ℤ) (wL.aP τ i : ℤ) (WeightFamilies.dimY D j : ℤ) (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * (D.R.r : ℤ)) Tn (Tp D j Tn : ℤ) (by simp only [Tp]; push_cast; ring) (by positivity) (b …`. Simplify using `only [Tp] at k`.

Move the coercions through the operations in `at k`. Conclude with `k`. Prove the components needed by the constructor for the conclusion. Introduce `w2 hw2 τ i hi`. Take `⟨-, h2P, -⟩` from `hw2`.

Establish `e` using `h2P τ i`. Establish `f` using `hFP τ i`. Take `⟨k1, k2⟩` from `key τ i hi`. Establish `e' : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i` using `by exact_mod_cast e`. Establish `: (1 : ℤ) ≤ w2.aP τ i` using `by nlinarith`.

Conclude with `this` after adjusting the coercions. Introduce `w1 hw1 τ i hi`. Take `⟨-, h1P, -⟩` from `hw1`. Take `⟨k1, -⟩` from `key τ i hi`. Establish `: (1 : ℤ) ≤ w1.aP τ i` using `by rw [h1P τ i]; push_cast; omega`.

Conclude with `this` after adjusting the coercions.
-/
theorem auxiliaryWeights_last_entry_pos {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp}
    {C2 A2 CR CT : ℝ} {ka wL wF : WeightFamilies.Wt D j} {Tn nP nW : ℕ} {h0 : ℝ}
    (hP : FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0) :
    (∀ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 → w2.LastPos) ∧ ∀ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW → w1.LastPos := by
  obtain ⟨-, hS, -, -, -⟩ := hP
  obtain ⟨-, -, -, h4, -, h6, -, -, -, -, -, -, -, -, hL, hF, -, -, -, h40, hc, -⟩ := hS
  obtain ⟨-, hLP, -⟩ := hL
  obtain ⟨-, hFP, -⟩ := hF

  have key : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      ((Tn : ℤ) + WeightFamilies.dimY D j + 2 ≤ wL.aP τ i) ∧
        (ka.aP τ i : ℤ) + 1 ≤ ((Tn : ℤ) + WeightFamilies.dimY D j + 4) * wL.aP τ i := by
    intro τ i hi
    have hg := hLP τ i
    have hlt : ¬ (i.1 + 1 < (D.R.sigW j).1) := by omega
    simp only [gapZ, hlt, dif_neg, if_neg, not_false_eq_true] at hg
    have ha : 2 * (Tn : ℝ) ^ 2 ≤ (ka.aP τ i : ℝ) := by
      have := h6 τ i hi
      linarith
    have ha' : 2 * (Tn : ℤ) ^ 2 ≤ (ka.aP τ i : ℤ) := by exact_mod_cast ha
    have k := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.weight_floor_inequalities (ka.aP τ i : ℤ) (wL.aP τ i : ℤ) (WeightFamilies.dimY D j : ℤ)
      (((WeightFamilies.dimY D j : ℤ) + 2) * nW) (2 * (D.R.r : ℤ)) Tn (Tp D j Tn : ℤ)
      (by simp only [Tp]; push_cast; ring) (by positivity) (by exact_mod_cast h40)
      (by exact_mod_cast hc) ha' (by rw [hg])
    simp only [Tp] at k
    push_cast at k
    exact k
  constructor
  · intro w2 hw2 τ i hi
    obtain ⟨-, h2P, -⟩ := hw2
    have e := h2P τ i
    have f := hFP τ i
    obtain ⟨k1, k2⟩ := key τ i hi
    have e' : (w2.aP τ i : ℤ) + wF.aP τ i = ((WeightFamilies.dimY D j : ℤ) + 4) * wL.aP τ i := by exact_mod_cast e
    have : (1 : ℤ) ≤ w2.aP τ i := by nlinarith
    exact_mod_cast this
  · intro w1 hw1 τ i hi
    obtain ⟨-, h1P, -⟩ := hw1
    obtain ⟨k1, -⟩ := key τ i hi
    have : (1 : ℤ) ≤ w1.aP τ i := by rw [h1P τ i]; push_cast; omega
    exact_mod_cast this

/- English proof (translation)
Introduce `hCI D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR hf hT2 hT1`. Establish `hj1 : 1 ≤ j` using `hj.1`. Take `⟨hL2, -, -, hlam, hdim, -⟩` from `GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR`. Establish `hdimR : (1 : ℝ) ≤ WeightFamilies.dimY D j` using `by exact_mod_cast hdim hj1`. Take `⟨-, -, hw2, hw1⟩` from `GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hP`.

Take `⟨hW2, hW1⟩` from `ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.theta_weight_bounds D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP`. Establish `hLast` using `auxiliaryWeights_last_entry_pos hP`. Take `⟨⟨w2, hg2⟩, -⟩` from `GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP`. Take `⟨hr2, -, hq2⟩` from `hW2 w2 hg2`. Take `⟨hdf2, hn2, hsz2⟩` from `hw2 w2 hg2`.

Establish `hpr2` using `GlobalTheory.pageRows_of_le D large₂ j ka w2 (by linarith) hdf2 hn2 hR`. Use `set lN := Real.log (Fintype.card (T.U j T.σ₀).Comp) with hlN`. Establish `hN0 : 0 ≤ lN` using `Real.log_natCast_nonneg _`. Establish `hN : lN ≤ 41 * Zb D large₂ ^ 2` using `GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w2 hpr2 hL2 hr2 hf T.σ₀ (Formalism.L2.Pj.Core.good_σ₀ _)`. Establish `hZ : 0 ≤ Zb D large₂`.

Unfold `Zb`. Conclude with `mul_nonneg (by positivity) (by linarith)`. Establish `hA : 0 ≤ 400 * Zb D large₂ + lamStar D` using `by linarith`. Establish `hs : 1 ≤ wL.size` using `WeightFamilies.Wt.one_le_size wL`. Establish `hPI : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) = 5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN`.

Establish `: (WeightFamilies.dimY D j : ℝ) ≠ 0` using `by linarith`. Unfold `WeightAlgebra.PI4`. Clear the denominators using the available nonvanishing facts. Establish `hAs : 0 ≤ (400 * Zb D large₂ + lamStar D) * wL.size` using `mul_nonneg hA (by linarith)`. Use `⟨400 * Zb D large₂, lN, by nlinarith, by nlinarith, ?_, ?_⟩` and prove the remaining obligations.

Introduce `hjm`. Take `⟨⟨w1, hg1⟩⟩` from `(⟨(GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP).2⟩ : Nonempty _)`. Take `⟨hr1, -, hq1⟩` from `hW1 hjm w1 hg1`. Take `⟨hdf1, hn1, hsz1⟩` from `hw1 w1 hg1`. Establish `hpr1` using `GlobalTheory.pageRows_of_le D large₂ j ka w1 (by linarith) hdf1 hn1 hR`.

Take `⟨th, hth, hnz, hb⟩` from `GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w1 hpr1 hL2 hr1 (hLast.2 w1 hg1) hq1 hinj EX (hT1 hjm w1 hg1)`. Use `⟨w1, hg1, th, hth, hnz, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : 2 * WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size = 2 * (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size`. Rewrite using `[← hPI]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use polynomial arithmetic with `[hb σ, mul_le_mul_of_nonneg_left hsz1 hA, mul_nonneg hAs (sub_nonneg.2 hdimR), mul_nonneg hN0 (sub_nonneg.2 hs)]`. Take `⟨th, hth, hnz, hb⟩` from `GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w2 hpr2 hL2 hr2 (hLast.1 w2 hg2) hq2 hinj EX (hT2 w2 hg2)`. Use `⟨w2, hg2, th, hth, hnz, fun σ => ?_⟩` and prove the remaining obligations. Establish `e : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size = (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size`.

Rewrite using `[← hPI]`. Rewrite using `[e]`. Use polynomial arithmetic with `[hb σ, mul_le_mul_of_nonneg_left hsz2 hA, mul_nonneg hAs (sub_nonneg.2 hdimR), mul_nonneg hN0 (sub_nonneg.2 hs)]`.
-/
theorem familyHypothesesI4_recPJ_of_supBound_thInt : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ ka → 16 ≤ D.R.f → (∀ w2, IsG2 wL wF w2 → ThInt (recPJ h j hj) hinj EX w2) → (j < D.R.m → ∀ w1, IsDoubledWeightWithShift wL w1 nW → ThInt (recPJ h j hj) hinj EX w1) → FamilyHypotheses.I4 large₂ (recPJ h j hj) wL wF nW := by
  intro hCI D T h hG hinj EX p j hj large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR hf hT2 hT1
  have hj1 : 1 ≤ j := hj.1
  obtain ⟨hL2, -, -, hlam, hdim, -⟩ :=
    GlobalTheory.page_two_le_L_and_signs D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP hR
  have hdimR : (1 : ℝ) ≤ WeightFamilies.dimY D j := by exact_mod_cast hdim hj1
  obtain ⟨-, -, hw2, hw1⟩ :=
    GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj1 hP
  obtain ⟨hW2, hW1⟩ :=
    ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.theta_weight_bounds D T h large₂ H C2 A2 CR CT j hj ka wL wF Tn nP nW h0 hP
  have hLast := auxiliaryWeights_last_entry_pos hP
  obtain ⟨⟨w2, hg2⟩, -⟩ :=
    GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hP
  obtain ⟨hr2, -, hq2⟩ := hW2 w2 hg2
  obtain ⟨hdf2, hn2, hsz2⟩ := hw2 w2 hg2
  have hpr2 := GlobalTheory.pageRows_of_le D large₂ j ka w2 (by linarith) hdf2 hn2 hR

  set lN := Real.log (Fintype.card (T.U j T.σ₀).Comp) with hlN
  have hN0 : 0 ≤ lN := Real.log_natCast_nonneg _
  have hN : lN ≤ 41 * Zb D large₂ ^ 2 :=
    GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w2 hpr2 hL2 hr2 hf T.σ₀ (Formalism.L2.Pj.Core.good_σ₀ _)
  have hZ : 0 ≤ Zb D large₂ := by
    unfold Zb
    exact mul_nonneg (by positivity) (by linarith)
  have hA : 0 ≤ 400 * Zb D large₂ + lamStar D := by linarith
  have hs : 1 ≤ wL.size := WeightFamilies.Wt.one_le_size wL
  have hPI : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) =
      5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN := by
    have : (WeightFamilies.dimY D j : ℝ) ≠ 0 := by linarith
    unfold WeightAlgebra.PI4
    field_simp
  have hAs : 0 ≤ (400 * Zb D large₂ + lamStar D) * wL.size := mul_nonneg hA (by linarith)
  refine ⟨400 * Zb D large₂, lN, by nlinarith, by nlinarith, ?_, ?_⟩
  · intro hjm
    obtain ⟨⟨w1, hg1⟩⟩ := (⟨(GlobalTheory.AuxiliaryWeightsExistence.exists_auxiliaryWeights_at_runWeights D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF
      Tn nP nW h0 hP).2⟩ : Nonempty _)
    obtain ⟨hr1, -, hq1⟩ := hW1 hjm w1 hg1
    obtain ⟨hdf1, hn1, hsz1⟩ := hw1 w1 hg1
    have hpr1 := GlobalTheory.pageRows_of_le D large₂ j ka w1 (by linarith) hdf1 hn1 hR
    obtain ⟨th, hth, hnz, hb⟩ :=
      GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w1 hpr1 hL2 hr1 (hLast.2 w1 hg1) hq1 hinj EX (hT1 hjm w1 hg1)
    refine ⟨w1, hg1, th, hth, hnz, fun σ => ?_⟩
    have e : 2 * WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        2 * (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]; ring
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz1 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]
  · obtain ⟨th, hth, hnz, hb⟩ :=
      GlobalTheory.T.exists_integral_theta_combination_nonzero_on_components hCI D T h hG large₂ j hj w2 hpr2 hL2 hr2 (hLast.1 w2 hg2) hq2 hinj EX (hT2 w2 hg2)
    refine ⟨w2, hg2, th, hth, hnz, fun σ => ?_⟩
    have e : WeightAlgebra.PI4 D j (400 * Zb D large₂) lN * (WeightFamilies.dimY D j : ℝ) * wL.size =
        (5 * (400 * Zb D large₂ + lamStar D) * WeightFamilies.dimY D j + 2 * lN) * wL.size := by
      rw [← hPI]
    rw [e]
    nlinarith [hb σ, mul_le_mul_of_nonneg_left hsz2 hA, mul_nonneg hAs (sub_nonneg.2 hdimR),
      mul_nonneg hN0 (sub_nonneg.2 hs)]

end GlobalTheory.ThetaIntegralWeights
