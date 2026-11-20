import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.H1algDefStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RPfVal
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.QBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepRun
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie
namespace GlobalTheory.PtTie

/- English proof (translation)
Introduce `τ i hi1`. Establish `hh` using `h`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩` from `hh`. Establish `h2` using `two_T_sq_le_last h τ i hi1`. Establish `h3` using `hL.2.1 τ i`.

Establish `hn : ¬ i.1 + 1 < (D.R.sigW j).1` using `by omega`. Rewrite `h3` using `[if_neg hn]`. Unfold `WeightAlgebra.gapZ at h3`. Rewrite `h3` using `[dif_neg hn]`. Establish `hTp : (0 : ℤ) < (WeightAlgebra.Tp D j T : ℤ)` using `by unfold WeightAlgebra.Tp; positivity`.

Rewrite `h3` using `[Int.fdiv_eq_ediv_of_nonneg _ hTp.le]`. Establish `h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (WeightAlgebra.Tp D j T : ℤ)`. Rewrite using `[Int.le_ediv_iff_mul_le hTp, _root_.one_mul]`. Unfold `WeightAlgebra.Tp`. Establish `e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ)` using `by exact_mod_cast h2`.

Establish `e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T` using `by exact_mod_cast hnW`. Establish `e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T` using `by exact_mod_cast h40`. Establish `e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ)` using `Int.natCast_nonneg _`. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite `h4` using `[← h3]`. Conclude with `h4` after adjusting the coercions.
-/
theorem lastPos_L_of_setC {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {large₂ : SizeData₂ D} {X : WeightAlgebra.PJ D B P j}
    {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : WeightAlgebra.SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : wL.LastPos := by
  intro τ i hi1
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold WeightAlgebra.gapZ at h3
  rw [dif_neg hn] at h3
  have hTp : (0 : ℤ) < (WeightAlgebra.Tp D j T : ℤ) := by unfold WeightAlgebra.Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (1 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (WeightAlgebra.Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp, _root_.one_mul]
    unfold WeightAlgebra.Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    push_cast
    nlinarith
  rw [← h3] at h4
  exact_mod_cast h4

/- English proof (translation)
Establish `hn : (1 : ℝ) ≤ Module.finrank ℚ D.host.E`. Conclude with `Module.finrank_pos (R := ℚ) (M := D.host.E)` after adjusting the coercions. Establish `e : D.host.rdE ^ (2 : ℝ) = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E)`. Unfold `Formalism.BasicNotions.Host.rdE`. Rewrite using `[← Real.rpow_mul (abs_nonneg _)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Unfold `rr0`. Conclude with `div_le_self (by positivity) (by linarith)`.
-/
theorem rootDiscriminantDegreeRatio_le_rootDiscriminant_sq (D : D7) : rr0 D ≤ D.host.rdE ^ (2 : ℝ) := by
  have hn : (1 : ℝ) ≤ Module.finrank ℚ D.host.E := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := D.host.E)
  have e : D.host.rdE ^ (2 : ℝ) = |(NumberField.discr D.host.E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ D.host.E) := by
    unfold Formalism.BasicNotions.Host.rdE
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    ring
  rw [e]
  unfold rr0
  exact div_le_self (by positivity) (by linarith)

/- English proof (translation)
Introduce `D large₂ B P j hj X H C2 A2 CR S ka wL wF Tn nP nW h0 hA hS h3 hP hCR`. Establish `h1` using `lastPos_L_of_setC hS`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, hn, -, hL, -⟩` from `hS`. Establish `hw : wL.n = nW` using `hL.1`. Take `⟨hP13, -, -, hr, hD⟩` from `hP`.

Establish `hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE` using `hA.2.2.2.2.2.2.2.2.2`. Establish `hf : 1 ≤ D.R.f`. Establish `: 0 < D.R.f` using `by unfold Ranks.f Ranks.n; positivity`. Use linear arithmetic over natural numbers and integers. Establish `hm : 1 ≤ D.R.m` using `hj.1.trans hj.2`.

Establish `hfR : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf`. Establish `hmR : (1 : ℝ) ≤ D.R.m` using `by exact_mod_cast hm`. Establish `hDR : (3 : ℝ) ≤ WeightAlgebra.DF wL` using `by exact_mod_cast hD`. Establish `h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * wL.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2`. Rewrite using `[hw]`.

Conclude with `((le_max_left _ _).trans (le_max_right _ _)).trans hP13`. Establish `hq` using `modulus_pos_of_third_hypothesis h3`. Establish `h31` using `h3.1`. Rewrite `h31` using `[Real.rpow_zero, _root_.one_mul]`. Establish `hs : (2 : ℝ) ≤ 2 * D.R.f * D.R.m` using `by nlinarith`.

Establish `hRR : D.host.rdE ^ (2 : ℝ) ≤ WeightFamilies.RRv D CR` using `Real.rpow_le_rpow_of_exponent_le (by linarith) hCR`. Establish `h4 : rr0 D ≤ WeightFamilies.RRv D CR` using `(rootDiscriminantDegreeRatio_le_rootDiscriminant_sq D).trans hRR`. Establish `hqg : ∀ i, (WeightAlgebra.qq D : ℝ) ≤ D.host.g i` using `fun i => by`. Establish `: WeightAlgebra.qq D ≤ D.host.g i` using `by fin_cases i exacts [min_le_left _ _, min_le_right _ _]`. Conclude with `this` after adjusting the coercions.

Establish `r0 : 0 ≤ rr0 D` using `by unfold rr0; positivity`. Generalize the expression as in `hsd : (2 * D.R.f * D.R.m : ℝ) = s at *`. Establish `p0 : (1 : ℝ) ≤ s ^ 4 * wL.n + 2 * s ^ 3`. Establish `a : (0 : ℝ) ≤ s ^ 4 * wL.n` using `by positivity`. Establish `b : (1 : ℝ) ≤ s ^ 3` using `one_le_pow₀ (by linarith)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR2 : s ^ 2 ≤ WeightFamilies.RRv D CR`. Use `le_trans ?_ hRR` and prove the remaining obligations. Rewrite using `[Real.rpow_two]`. Conclude with `pow_le_pow_left₀ (by linarith) hrd 2`.

Establish `hR1 : 1 ≤ WeightFamilies.RRv D CR` using `by nlinarith`. Establish `hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2` using `p0.trans h5`. Establish `hkey : s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ WeightAlgebra.qq D`. Use `le_trans ?_ h31` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right ?_ (by positivity)` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Use `⟨h1, ?_, fun i => ?_, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hw]`. Use `le_trans ?_ hn` and prove the remaining obligations. Use polynomial arithmetic with `[Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]`.

Establish `a : 4 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2` using `mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)`. Establish `b : 4 * (WeightAlgebra.DF wL : ℝ) + 4 ≤ D.host.g i` using `by nlinarith [hqg i]`. Conclude with `b` after adjusting the coercions. Rewrite using `[hsd]`. Establish `a : Real.sqrt s ≤ s` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`.

Establish `b : (WeightAlgebra.DF wL : ℝ) * (2 * Real.sqrt s) ≤ (WeightAlgebra.DF wL : ℝ) * s * 2` using `by nlinarith`. Establish `c : (6 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) * s` using `by nlinarith`. Establish `d` using `hqg i`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hsd]`.

Establish `d` using `hqg i`. Unfold `WeightAlgebra.cc`. Use `gcongr`.
-/
theorem runNum_of_sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ), InR D j → ∀ (X : WeightAlgebra.PJ D B P j) (H : WeightAlgebra.KHyp) (C2 A2 CR : ℝ) (S : WeightAlgebra.Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), WeightAlgebra.ParA large₂ H.CA → WeightAlgebra.SetC large₂ X H.CK H.C1 H.A1 ka wL wF Tn nP nW h0 → WeightAlgebra.H3 large₂ H C2 A2 CR 0 wL Tn → PageSupp D large₂ B C2 A2 nW S wL → 2 ≤ CR → RunNum D wL (WeightAlgebra.cc D large₂ C2 A2 CR wL) := by
  intro D large₂ B P j hj X H C2 A2 CR S ka wL wF Tn nP nW h0 hA hS h3 hP hCR
  have h1 := lastPos_L_of_setC hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hn, -, hL, -⟩ := hS
  have hw : wL.n = nW := hL.1
  obtain ⟨hP13, -, -, hr, hD⟩ := hP
  have hrd : 2 * (D.R.f : ℝ) * D.R.m ≤ D.host.rdE := hA.2.2.2.2.2.2.2.2.2
  have hf : 1 ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    omega
  have hm : 1 ≤ D.R.m := hj.1.trans hj.2
  have hfR : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf
  have hmR : (1 : ℝ) ≤ D.R.m := by exact_mod_cast hm
  have hDR : (3 : ℝ) ≤ WeightAlgebra.DF wL := by exact_mod_cast hD
  have h5 : (2 * D.R.f * D.R.m : ℝ) ^ 4 * wL.n + 2 * (2 * D.R.f * D.R.m : ℝ) ^ 3 ≤ WeightFamilies.PPv D large₂ C2 A2 := by
    rw [hw]
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans hP13
  have hq := modulus_pos_of_third_hypothesis h3
  have h31 := h3.1
  rw [Real.rpow_zero, _root_.one_mul] at h31
  have hs : (2 : ℝ) ≤ 2 * D.R.f * D.R.m := by nlinarith
  have hRR : D.host.rdE ^ (2 : ℝ) ≤ WeightFamilies.RRv D CR :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hCR
  have h4 : rr0 D ≤ WeightFamilies.RRv D CR := (rootDiscriminantDegreeRatio_le_rootDiscriminant_sq D).trans hRR
  have hqg : ∀ i, (WeightAlgebra.qq D : ℝ) ≤ D.host.g i := fun i => by
    have : WeightAlgebra.qq D ≤ D.host.g i := by
      fin_cases i
      exacts [min_le_left _ _, min_le_right _ _]
    exact_mod_cast this
  have r0 : 0 ≤ rr0 D := by unfold rr0; positivity
  generalize hsd : (2 * D.R.f * D.R.m : ℝ) = s at *
  have p0 : (1 : ℝ) ≤ s ^ 4 * wL.n + 2 * s ^ 3 := by
    have a : (0 : ℝ) ≤ s ^ 4 * wL.n := by positivity
    have b : (1 : ℝ) ≤ s ^ 3 := one_le_pow₀ (by linarith)
    linarith
  have hR2 : s ^ 2 ≤ WeightFamilies.RRv D CR := by
    refine le_trans ?_ hRR
    rw [Real.rpow_two]
    exact pow_le_pow_left₀ (by linarith) hrd 2
  have hR1 : 1 ≤ WeightFamilies.RRv D CR := by nlinarith
  have hP1 : 1 ≤ WeightFamilies.PPv D large₂ C2 A2 := p0.trans h5
  have hkey : s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ WeightAlgebra.qq D := by
    refine le_trans ?_ h31
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc s ^ 2 ≤ WeightFamilies.RRv D CR := hR2
      _ ≤ WeightFamilies.RRv D CR ^ 4 := le_self_pow₀ hR1 (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hP1)
  refine ⟨h1, ?_, fun i => ?_, by unfold WeightAlgebra.cc; positivity, fun _ i => ⟨?_, ?_⟩⟩
  · rw [hw]
    refine le_trans ?_ hn
    nlinarith [Nat.mul_le_mul_left (D.R.f * D.R.r) (show 2 ≤ D.R.r + 1 by omega)]
  · have a : 4 * (WeightAlgebra.DF wL : ℝ) ^ 2 ≤ s ^ 2 * (WeightAlgebra.DF wL : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    have b : 4 * (WeightAlgebra.DF wL : ℝ) + 4 ≤ D.host.g i := by nlinarith [hqg i]
    exact_mod_cast b
  · rw [hsd]
    have a : Real.sqrt s ≤ s := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have b : (WeightAlgebra.DF wL : ℝ) * (2 * Real.sqrt s) ≤ (WeightAlgebra.DF wL : ℝ) * s * 2 := by nlinarith
    have c : (6 : ℝ) ≤ (WeightAlgebra.DF wL : ℝ) * s := by nlinarith
    have d := hqg i
    nlinarith
  · rw [hsd]
    have d := hqg i
    unfold WeightAlgebra.cc
    gcongr

end GlobalTheory.PtTie
