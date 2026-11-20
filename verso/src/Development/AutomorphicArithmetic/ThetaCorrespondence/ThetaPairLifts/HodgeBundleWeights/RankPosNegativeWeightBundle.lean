import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueNeZeroLowLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundleStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowPos
open GlobalTheory.FlatTw GlobalTheory.FlatLine
/- English proof (translation)
Establish `hL` using `GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY`. Establish `hN` using `GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ hL.pos`. Take `⟨hK, ht⟩` from `GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread _ _ _ _ _ _ _ Y.U hL.unf (xiR D) hL.xi hL.geo hL.pos hL.good hN`. Take `⟨t, ht1, ht2⟩` from `ht Z`. Take `⟨s, -, -, -, hs1, hs2⟩` from `(GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hL.unf hL.pos hN).1 Z (-w₀) _ (FlatSec.shift (hasPts Y.U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀)) ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := T.Q.Dw j) (c := Y.d.c₂) τ).sub …`.

Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn`. Conclude with `hw (by simp [Finset.sum_apply, hn]))`. Take `⟨z, -, -⟩` from `GlobalTheory.CombTw.exists_twSec_comb _ _ _ _ _ _ _ Y.U hL.unf (xiR D) _ Z u w₀ m _ s t hs1 hs2 ht1 ht2`. Establish `hB : Even (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m).2` using `AllWt.even_wtOf _ _`.

Establish `hf' : f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m + (wtOf (T.Q.Dw j) u 0 - wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m))`. Rewrite using `[add_sub_cancel]` and apply the resulting hypothesis. Use `⟨f * z.inv, z.cusp_inv _ hB f hf', fun h0 => hf0 ?_⟩` and prove the remaining obligations. Establish `h1 : idem Z * f = f` using `idem_mul_eq (e := exZ _ (wtOf (T.Q.Dw j) u 0)) ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_twist_ne_zero_of_lowered (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {D : D7} (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ)
    (hT : LawsJ T) (hj : InR D j) (hY : Y.Good e o) (hF : FlatExists Y.U (xiR D))
    (u : AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    {f : Rul Y.d.Xo₂ Y.d.c₂} (hf : f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (hf0 : f ≠ 0) :
    ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m), g ≠ 0 := by
  have hL := GlobalTheory.T.complexUniformizationLaws_of_goodDeepCover D T j Y e o hT hj hY
  have hN := GlobalTheory.T.hasUnramifiedIntegralFramedPoints_of_goodPlaces hP.q18 hP.q1 hP.p5 _ _ _ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ hL.pos
  obtain ⟨hK, ht⟩ := GlobalTheory.T.exists_keySection_inverseRoot_twistingSection_spread _ _ _ _ _ _ _ Y.U hL.unf (xiR D) hL.xi hL.geo hL.pos hL.good hN
  obtain ⟨t, ht1, ht2⟩ := ht Z
  obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts Y.U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := T.Q.Dw j) (c := Y.d.c₂) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
  obtain ⟨z, -, -⟩ := GlobalTheory.CombTw.exists_twSec_comb _ _ _ _ _ _ _ Y.U hL.unf (xiR D) _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  have hB : Even (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m).2 := AllWt.even_wtOf _ _
  have hf' : f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m +
      (wtOf (T.Q.Dw j) u 0 - wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) := by
    rwa [add_sub_cancel]
  refine ⟨f * z.inv, z.cusp_inv _ hB f hf', fun h0 => hf0 ?_⟩
  have h1 : idem Z * f = f := idem_mul_eq (e := exZ _ (wtOf (T.Q.Dw j) u 0)) ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩
  calc f = f * idem Z := by rw [mul_comm, h1]
    _ = f * z.inv * z.sig := by rw [← z.mul_inv, mul_comm z.sig, mul_assoc]
    _ = 0 := by rw [h0, zero_mul]
/- English proof (translation)
Introduce `hP hG hQ hS hKS hLie`. Establish `R` using `GlobalTheory.T.weight_conditions_at_index`. Establish `F` using `GlobalTheory.T.flat_line_c1_log_bound (_root_.GlobalTheory.T.flatDeg_of_scholze_weinstein hP)`. Establish `S` using `_root_.GlobalTheory.T.exists_nonzero_cusp_form_of_fan_charts hP hG hQ hS hKS.toroidalChartsForFan hLie`. Unfold `Covers Lifts at *`.

Use `(R.and (F.and S)).imp fun Fm CH _ h => ?_` and prove the remaining obligations. Take `⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩` from `h`. Use `⟨C1, h1, ?_⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `e1.and (e2.and e3)`. Use `⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩` and prove the remaining obligations.

Take `⟨hA, hB, hC⟩` from `hx0 x hx hle ι p hp`. Take `⟨hL, hp1, hq1, hf, hj, hn, -, -, hs⟩` from `hA i hi`. Establish `hFl` using `(hB i hi Y hY).2.2.1`. Take `⟨Z, g, hg, hg0⟩` from `hC i hi Y hY`. Establish `hgood` using `_root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn (hs _ (Or.inl rfl)).1 (hs _ (Or.inl rfl)).2`.

Take `⟨g', hg', hg'0⟩` from `_root_.GlobalTheory.CovTop.LowPos.exists_twist_ne_zero_of_lowered hP p.T _ Y _ _ hL hj hY.1 hFl (uM p i) (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)) ((p.κ i).n / 2) Z hg hg0`. Conclude with `rk_pos hgood (mem_cuspW_of_exZ hY.1.unf (exZ_lowered _ _ _ _ _ hn) hg'.1) hg'0`.
-/
theorem covers_rk_Gs_neg_cZero_pos : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation →
    GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative →
    Covers fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  intro hP hG hQ hS hKS hLie
  have R := GlobalTheory.T.weight_conditions_at_index
  have F := GlobalTheory.T.flat_line_c1_log_bound (_root_.GlobalTheory.T.flatDeg_of_scholze_weinstein hP)
  have S := _root_.GlobalTheory.T.exists_nonzero_cusp_form_of_fan_charts hP hG hQ hS hKS.toroidalChartsForFan hLie
  unfold Covers Lifts at *
  refine (R.and (F.and S)).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩, ⟨C3, h3, e3⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and (e2.and e3)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY => ?_⟩
  obtain ⟨hA, hB, hC⟩ := hx0 x hx hle ι p hp
  obtain ⟨hL, hp1, hq1, hf, hj, hn, -, -, hs⟩ := hA i hi
  have hFl := (hB i hi Y hY).2.2.1
  obtain ⟨Z, g, hg, hg0⟩ := hC i hi Y hY
  have hgood := _root_.GlobalTheory.T.covering_shift_preserves_goodAt hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hY.1 (wtA (p.κ i)) (p.κ i).n _ hn
    (hs _ (Or.inl rfl)).1 (hs _ (Or.inl rfl)).2
  obtain ⟨g', hg', hg'0⟩ := _root_.GlobalTheory.CovTop.LowPos.exists_twist_ne_zero_of_lowered hP p.T _ Y _ _ hL hj hY.1 hFl (uM p i)
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)) ((p.κ i).n / 2) Z hg hg0
  exact rk_pos hgood (mem_cuspW_of_exZ hY.1.unf (exZ_lowered _ _ _ _ _ hn) hg'.1) hg'0
end GlobalTheory.CovTop.LowPos
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos | exact _root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos | (intros; apply _root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.covers_rk_pos_of_semiAbelianLieSeminegative : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → Covers fun Fm x _ ι p i Y _ _ => 0 < Y.rk (Gs p i (-(cZero (Fm.D x ι) ((i : ℕ) + 1)))) := by
  first | exact @_root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos | exact _root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos | (intros; apply _root_.GlobalTheory.CovTop.LowPos.covers_rk_Gs_neg_cZero_pos <;> assumption)
end
