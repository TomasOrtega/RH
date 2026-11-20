import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilyStatementOfItemsFourSeven
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma

noncomputable section

namespace GlobalTheory

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.BridgeLemma Formalism.MainNotions.S.Cnt Formalism.FourierDecayAlt
open scoped ENNReal

/- English proof (translation)
Unfold `VanishingOnXAndXPlusBranching.IntegralityFromMetric`. Introduce `hS hW`. Unfold `VanishingOnXAndXPlusBranching.adm11 UnitaryVolumeMass.stSchur at hS`. Unfold `VanishingOnXAndXPlusBranching.adm12 UnitaryVolumeMass.stWeyl at hW`. Unfold `VanishingOnXAndXPlusBranching.Conclusion1 UnitaryVolumeMass.stCONST`.

Introduce `hH0 τ w w' hTT θ hθ W hGW A hGS hdeg μsec hμ`. Establish `hSch` using `hS hH0 τ w w' hTT θ hθ W hGW A hGS μsec hμ`. Establish `hdimq : (Module.finrank ℂ W.Wq : ℝ) = vand (uS D w' τ) / superfactorial D.R.k` using `hW τ w' W.Wq W.z' W.π' hGW.2.1`. Establish `hF` using `superfactorial_pos D.R.k`. Establish `hVu0 : 0 ≤ vand (uS D w' τ)`.

Establish `e : vand (uS D w' τ) = (Module.finrank ℂ W.Wq : ℝ) * superfactorial D.R.k`. Rewrite using `[hdimq]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) hF.le`.

Break down `hVu0.lt_or_eq with hVu | hVu` into its components or cases. Use `swap`. Establish `h0 : (Module.finrank ℂ W.Wq : ℝ) = 0` using `by rw [hdimq, ← hVu, zero_div]`. Establish `hM0 : MMv D w w' A μsec = 0`. Apply `le_antisymm _ (by positivity)` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hM0, mul_zero]`. Check the signs of the components of the expression. Take `⟨hS0, -, -⟩` from `hH0`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hg1, hg1b, hg2, hg2b, -, -, -, hv1, -⟩` from `hS0`.

Establish `hk6` using `rank_lower_bound D`. Establish `hm` using `rank_eq_two_mul_add_two D`. Establish `hn : D.R.r = D.R.k + 2 * D.R.rS + 1` using `by unfold Formalism.BasicNotions.Ranks.r; omega`. Establish `hk1 : 1 ≤ D.R.k` using `by omega`. Establish `hb1 : 1 ≤ large₂.sc.b` using `one_le_scale_base_local large₂`.

Establish `hv : 0 < D.host.v` using `by linarith`. Establish `hT : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w` using `by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.1`. Establish `hT' : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w'` using `by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.2.1`. Establish `hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8` using `one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk1) hb1)`. Establish `hgg1 : 1 ≤ gg D`.

Unfold `gg`. Conclude with `one_le_mul_of_one_le_of_one_le (hkb.trans hg1) (hkb.trans hg2)`. Establish `hgpos : 0 < gg D` using `by linarith`. Establish `hggb : gg D ≤ large₂.sc.b ^ (2 * Cg)`. Unfold `gg`.

Rewrite using `[show 2 * Cg = Cg + Cg by ring, Real.rpow_add (by linarith)]`. Conclude with `mul_le_mul hg1b hg2b (by linarith) (by positivity)`. Establish `hL1 : 1 ≤ large₂.sc.L`. Unfold `Formalism.BasicNotions.Scale.L`. Conclude with `Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)`.

Establish `h2v : 2 * D.host.v = D.host.rdE` using `by simp only [Formalism.BasicNotions.Host.v]; ring`. Establish `hV : Real.log (2 * D.host.v) ≤ large₂.sc.L / 1`. Rewrite using `[div_one, h2v]`. Combine the equalities or inequalities in the displayed calculation. Establish `hnum` using `numerical_constant_clause_bound D.R.rS D.R.m hm large₂.sc.b large₂.sc.L (2 * D.host.v) (gg D) (Formalism.MainNotions.S.Tr D w) (Formalism.MainNotions.S.Tr D w') 1 Cg CS C rfl hL1 (by linarith) hV hgg1 hggb (by linarith) (by linarith) (by norm_num; linarith)`.

Establish `hmain` using `volume_constant_main_estimate D.R.k D.R.rS D.R.m D.R.r hm hn hk1 D.host.v (gg D) (Formalism.MainNotions.S.Tr D w) (Formalism.MainNotions.S.Tr D w') (Module.finrank ℂ W.Wp) (vand (uS D w' τ)) (D.dsig τ) (large₂.sc.b ^ (CS * (D.R.m : ℝ) ^ 2)) (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) h …`. Establish `hmm1 : D.R.m - 1 = 2 * D.R.rS + 1` using `by omega`. Establish `hmm2 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1)`. Rewrite using `[hmm1, hm, show (2 * D.R.rS + 2) * (2 * D.R.rS + 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1)) by ring]`. Conclude with `Nat.mul_div_cancel_left _ (by norm_num)`.

Establish `ex1 : ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 = (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ)`. Rewrite using `[hmm2, hmm1, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ex2 : (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 = ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ)`.

Rewrite using `[hmm2, hm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `eX : Formalism.MainNotions.S.Tcrit D w' τ = (Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v) (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ))) ^ ((1 : ℝ) / D.R.k)`. Unfold `Formalism.MainNotions.S.Tcrit Formalism.FourierDecayAlt.Sz.TcritPow`.

Rewrite using `[show D.host.ka = Real.pi / D.host.v from rfl, ex1, ex2, Real.rpow_neg (div_nonneg Real.pi_pos.le hv.le), Real.rpow_natCast, Real.rpow_natCast, h2v]`. Both sides reduce to the same expression. Establish `hTP : 0 ≤ Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v) (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ))`. Unfold `Formalism.FourierDecayAlt.Sz.TcritPow`. Conclude with `div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.2 (pow_nonneg (div_nonneg Real.pi_pos.le hv.le) _)) (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hgpos.le _)) (mul_nonneg (D.dsig_pos τ).le (superfactorial_pos _).le)) hVu.le`.

Establish `hk0 : (D.R.k : ℝ) ≠ 0` using `by exact_mod_cast (show D.R.k ≠ 0 by omega)`. Establish `eT : Formalism.MainNotions.S.Tcrit D w' τ ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v) (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ))`. Rewrite using `[eX, ← Real.rpow_natCast, ← Real.rpow_mul hTP, one_div, inv_mul_cancel₀ hk0, Real.rpow_one]`. Establish `e1 : normalizedLocalScale D w = (Real.exp 1 * Real.pi * (gg D ^ D.R.m)⁻¹ / (Formalism.MainNotions.S.Tr D w * D.R.k * D.host.v)) ^ D.R.k`. Unfold `normalizedLocalScale`.

Rewrite using `[Real.rpow_neg (le_of_lt hgpos), Real.rpow_natCast]`. Establish `eP : tvPr D τ w' ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v) (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) / Formalism.MainNotions.S.Tr D w' ^ D.R.k`. Unfold `tvPr`. Rewrite using `[div_pow, eT]`. Establish `hnv : 0 ≤ normalizedLocalScale D w` using `by rw [e1]; positivity`.

Establish `key` using `hmain`. Rewrite `key` using `[← e1, ← eP, ← hdimq, ← hdeg]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ampConst_of_rd_le_b (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 C1 CS C : ℝ)
    (hrd : D.host.rdE ≤ large₂.sc.b) (hC : CS + 1 + (1 + 2 * Cg) / 2 ≤ C) :
    VanishingOnXAndXPlusBranching.IntegralityFromMetric D large₂ C' Cl Cg cb Cu cT CT C0 C1 CS C := by
  unfold VanishingOnXAndXPlusBranching.IntegralityFromMetric
  intro hS hW
  unfold VanishingOnXAndXPlusBranching.adm11 UnitaryVolumeMass.stSchur at hS
  unfold VanishingOnXAndXPlusBranching.adm12 UnitaryVolumeMass.stWeyl at hW
  unfold VanishingOnXAndXPlusBranching.Conclusion1 UnitaryVolumeMass.stCONST
  intro hH0 τ w w' hTT θ hθ W hGW A hGS hdeg μsec hμ
  have hSch := hS hH0 τ w w' hTT θ hθ W hGW A hGS μsec hμ
  have hdimq : (Module.finrank ℂ W.Wq : ℝ) = vand (uS D w' τ) / superfactorial D.R.k :=
    hW τ w' W.Wq W.z' W.π' hGW.2.1
  have hF := superfactorial_pos D.R.k
  have hVu0 : 0 ≤ vand (uS D w' τ) := by
    have e : vand (uS D w' τ) = (Module.finrank ℂ W.Wq : ℝ) * superfactorial D.R.k := by
      rw [hdimq]; field_simp
    rw [e]; exact mul_nonneg (Nat.cast_nonneg _) hF.le
  rcases hVu0.lt_or_eq with hVu | hVu
  swap
  · have h0 : (Module.finrank ℂ W.Wq : ℝ) = 0 := by rw [hdimq, ← hVu, zero_div]
    have hM0 : MMv D w w' A μsec = 0 := by
      apply le_antisymm _ (by positivity)
      calc MMv D w w' A μsec ≤ _ := hSch
        _ = 0 := by rw [h0]; simp
    rw [hM0, mul_zero]
    positivity
  obtain ⟨hS0, -, -⟩ := hH0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hg1, hg1b, hg2, hg2b, -, -, -, hv1, -⟩ := hS0
  have hk6 := rank_lower_bound D
  have hm := rank_eq_two_mul_add_two D
  have hn : D.R.r = D.R.k + 2 * D.R.rS + 1 := by unfold Formalism.BasicNotions.Ranks.r; omega
  have hk1 : 1 ≤ D.R.k := by omega
  have hb1 : 1 ≤ large₂.sc.b := one_le_scale_base_local large₂
  have hv : 0 < D.host.v := by linarith
  have hT : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w := by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.1
  have hT' : (3 : ℝ) ≤ Formalism.MainNotions.S.Tr D w' := by unfold Formalism.MainNotions.S.Tr; exact_mod_cast hTT.2.2.2.1
  have hkb : (1 : ℝ) ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast hk1) hb1)
  have hgg1 : 1 ≤ gg D := by
    unfold gg; exact one_le_mul_of_one_le_of_one_le (hkb.trans hg1) (hkb.trans hg2)
  have hgpos : 0 < gg D := by linarith
  have hggb : gg D ≤ large₂.sc.b ^ (2 * Cg) := by
    unfold gg
    rw [show 2 * Cg = Cg + Cg by ring, Real.rpow_add (by linarith)]
    exact mul_le_mul hg1b hg2b (by linarith) (by positivity)
  have hL1 : 1 ≤ large₂.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact Real.one_le_rpow (le_of_lt large₂.sc.one_lt_alt) (le_of_lt large₂.sc.eps_pos)
  have h2v : 2 * D.host.v = D.host.rdE := by simp only [Formalism.BasicNotions.Host.v]; ring
  have hV : Real.log (2 * D.host.v) ≤ large₂.sc.L / 1 := by
    rw [div_one, h2v]
    calc Real.log D.host.rdE ≤ Real.log large₂.sc.b := Real.log_le_log (by linarith) hrd
      _ = large₂.sc.L := Real.log_exp _
  have hnum := numerical_constant_clause_bound D.R.rS D.R.m hm large₂.sc.b large₂.sc.L (2 * D.host.v) (gg D) (Formalism.MainNotions.S.Tr D w)
    (Formalism.MainNotions.S.Tr D w') 1 Cg CS C rfl hL1 (by linarith) hV hgg1 hggb (by linarith) (by linarith)
    (by norm_num; linarith)
  have hmain := volume_constant_main_estimate D.R.k D.R.rS D.R.m D.R.r hm hn hk1 D.host.v (gg D) (Formalism.MainNotions.S.Tr D w)
    (Formalism.MainNotions.S.Tr D w') (Module.finrank ℂ W.Wp) (vand (uS D w' τ)) (D.dsig τ)
    (large₂.sc.b ^ (CS * (D.R.m : ℝ) ^ 2)) (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2)) hv hgpos (by linarith)
    (by linarith) (Nat.cast_nonneg _) hVu (D.dsig_pos τ) hnum (by positivity)
  have hmm1 : D.R.m - 1 = 2 * D.R.rS + 1 := by omega
  have hmm2 : D.R.m * (D.R.m - 1) / 2 = (D.R.rS + 1) * (2 * D.R.rS + 1) := by
    rw [hmm1, hm, show (2 * D.R.rS + 2) * (2 * D.R.rS + 1) = 2 * ((D.R.rS + 1) * (2 * D.R.rS + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have ex1 : ((D.R.m : ℝ) - 1) * D.R.k + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 =
      (((D.R.m - 1) * D.R.k + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) := by
    rw [hmm2, hmm1, hm]; push_cast; ring
  have ex2 : (D.R.k : ℝ) * D.R.m + (D.R.m : ℝ) * ((D.R.m : ℝ) - 1) / 2 =
      ((D.R.k * D.R.m + D.R.m * (D.R.m - 1) / 2 : ℕ) : ℝ) := by
    rw [hmm2, hm]; push_cast; ring
  have eX : Formalism.MainNotions.S.Tcrit D w' τ = (Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ))) ^ ((1 : ℝ) / D.R.k) := by
    unfold Formalism.MainNotions.S.Tcrit Formalism.FourierDecayAlt.Sz.TcritPow
    rw [show D.host.ka = Real.pi / D.host.v from rfl, ex1, ex2, Real.rpow_neg (div_nonneg Real.pi_pos.le hv.le), Real.rpow_natCast, Real.rpow_natCast,
      h2v]
    rfl
  have hTP : 0 ≤ Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) := by
    unfold Formalism.FourierDecayAlt.Sz.TcritPow
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (inv_nonneg.2 (pow_nonneg (div_nonneg Real.pi_pos.le hv.le) _))
      (Real.rpow_nonneg (by linarith) _)) (pow_nonneg hgpos.le _))
      (mul_nonneg (D.dsig_pos τ).le (superfactorial_pos _).le)) hVu.le
  have hk0 : (D.R.k : ℝ) ≠ 0 := by exact_mod_cast (show D.R.k ≠ 0 by omega)
  have eT : Formalism.MainNotions.S.Tcrit D w' τ ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) := by
    rw [eX, ← Real.rpow_natCast, ← Real.rpow_mul hTP, one_div, inv_mul_cancel₀ hk0, Real.rpow_one]
  have e1 : normalizedLocalScale D w = (Real.exp 1 * Real.pi * (gg D ^ D.R.m)⁻¹ /
      (Formalism.MainNotions.S.Tr D w * D.R.k * D.host.v)) ^ D.R.k := by
    unfold normalizedLocalScale
    rw [Real.rpow_neg (le_of_lt hgpos), Real.rpow_natCast]
  have eP : tvPr D τ w' ^ D.R.k = Formalism.FourierDecayAlt.Sz.TcritPow D.R.k D.R.m (Real.pi / D.host.v)
      (2 * D.host.v) (gg D) (D.dsig τ * superfactorial D.R.r) (vand (uS D w' τ)) / Formalism.MainNotions.S.Tr D w' ^ D.R.k := by
    unfold tvPr
    rw [div_pow, eT]
  have hnv : 0 ≤ normalizedLocalScale D w := by rw [e1]; positivity
  have key := hmain
  rw [← e1, ← eP, ← hdimq, ← hdeg] at key
  calc ENNReal.ofReal (normalizedLocalScale D w) * MMv D w w' A μsec
      ≤ ENNReal.ofReal (normalizedLocalScale D w) * _ := by gcongr
    _ = ENNReal.ofReal (normalizedLocalScale D w * _) := (ENNReal.ofReal_mul hnv).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal key

/- English proof (translation)
Unfold `OwnEv at hS ⊢`. Take `⟨x0, hx0⟩` from `hS`. Take `⟨x1, hx1⟩` from `family_sizes_eventually_large eps Fm 0`. Use `⟨max x0 x1, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `h1` using `hx0 x (le_trans (le_max_left _ _) hx) i`.

Establish `h2` using `(hx1 x (le_trans (le_max_right _ _) hx) i).2.2.2.2.1`. Conclude with `ampConst_of_rd_le_b (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 _ _ (CS + Cg + 2) h2 (by linarith) h1 (hW x i)`.
-/
theorem ampConst_fam {eps : ℝ} (Fm : FamP eps) (Cg cb Cu cT CT C0 C1 CS : ℝ)
    (hS : OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 CS)
    (hW : VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm) :
    OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.Conclusion1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 (CS + Cg + 2) := by
  unfold OwnEv at hS ⊢
  obtain ⟨x0, hx0⟩ := hS
  obtain ⟨x1, hx1⟩ := family_sizes_eventually_large eps Fm 0
  refine ⟨max x0 x1, fun x hx i => ?_⟩
  have h1 := hx0 x (le_trans (le_max_left _ _) hx) i
  have h2 := (hx1 x (le_trans (le_max_right _ _) hx) i).2.2.2.2.1
  exact ampConst_of_rd_le_b (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 _ _ (CS + Cg + 2) h2
    (by linarith) h1 (hW x i)

/- English proof (translation)
Introduce `Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa`. Establish `hA6 : 0 ≤ 6 * Real.exp 1 * Real.pi * |A|` using `by positivity`. Establish `hAA : 6 * Real.exp 1 * Real.pi * A ≤ 6 * Real.exp 1 * Real.pi * |A|` using `mul_le_mul_of_nonneg_left (le_abs_self A) (by positivity)`. Take `⟨C, hCd⟩ : ∃ C : ℝ, C = max CPT 0 + max (CS + Cg + 2) 0 + 6 + Ca + 6 * Real.exp 1 * Real.pi * |A|` from `⟨_, rfl⟩`. Take `⟨Ch, hChd⟩ : ∃ Ch : ℝ, Ch = max CDl 0 + 1` from `⟨_, rfl⟩`.

Establish `hm1` using `le_max_right CPT 0`. Establish `hm2` using `le_max_right (CS + Cg + 2) 0`. Establish `hm3` using `le_max_left CDl 0`. Establish `hm4` using `le_max_right CDl 0`. Establish `hC0 : 0 ≤ C` using `by linarith`.

Establish `hCL : max CPT 0 + max (CS + Cg + 2) 0 + 6 ≤ C` using `by linarith`. Establish `hCaC : Ca ≤ C` using `by linarith`. Establish `hC2 : 2 ≤ C` using `by linarith`. Establish `hCA : 6 * Real.exp 1 * Real.pi * A ≤ C` using `by linarith`. Establish `hCh0 : 0 ≤ Ch` using `by linarith`.

Establish `hChD : CDl ≤ Ch` using `by linarith`. Establish `hChD1 : CDl + 1 ≤ Ch` using `by linarith`. Use `⟨C, 6 * C + C ^ 2 + C * Ch, Ch, hC0, hCh0, ?_⟩` and prove the remaining obligations. Introduce `eps Fm h1 h2 h5 h9 hDeg hAbs h4c h11 h12 Cpr δ hδ`. Establish `hCn0 : 0 ≤ max Cpr 0` using `le_max_right _ _`.

Establish `hCpr : Cpr ≤ max Cpr 0` using `le_max_left _ _`. Establish `hCCh` using `mul_nonneg hC0 hCh0`. Establish `hsq` using `sq_nonneg C`. Establish `hP1` using `ampConst_fam Fm Cg cb Cu cT CT C0 C1 CS h11 h12`. Establish `h35` using `family_third_fifth_items Fm Cg cb Cu cT CT C0 A C (6 * C + C ^ 2 + C * Ch) Ch hC0 hCh0 (by linarith) (by linarith)`.

Unfold `OwnEv at hP1 h35 h4c ⊢`. Unfold `VanishingOnXAndXPlusBranching.admF5 OwnEv at h5`. Unfold `VanishingOnXAndXPlusBranching.admF9 OwnEv at h9`. Take `⟨a1, ha1⟩` from `h1 (max Cpr 0)`. Take `⟨a2, ha2⟩` from `h2 (max Cpr 0)`.

Take `⟨a5, ha5⟩` from `h5`. Take `⟨a9, ha9⟩` from `h9 (max Cpr 0)`. Take `⟨aD, haD⟩` from `hDeg (max Cpr 0)`. Take `⟨aA, haA⟩` from `hAbs (max Cpr 0)`. Take `⟨ac, hac⟩` from `h4c`.

Take `⟨aP, haP⟩` from `hP1`. Take `⟨a35, ha35⟩` from `h35`. Take `⟨a6, ha6⟩` from `family_side_conditions_large Fm C δ hδ`. Take `⟨a9s, ha9s⟩` from `rank_power_le_scale_power Fm hilbertNinetyConstant hilbertNinetyConstant_pos`. Use `⟨|Fm.x1| + 1 + |a1| + |a2| + |a5| + |a9| + |aD| + |aA| + |ac| + |aP| + |a35| + |a6| + |a9s|, fun x hx i => ?_⟩` and prove the remaining obligations.

Establish `b1` using `le_abs_self a1`. Establish `b2` using `le_abs_self a2`. Establish `b5` using `le_abs_self a5`. Establish `b9` using `le_abs_self a9`. Establish `bD` using `le_abs_self aD`.

Establish `bA` using `le_abs_self aA`. Establish `bc` using `le_abs_self ac`. Establish `bP` using `le_abs_self aP`. Establish `b35` using `le_abs_self a35`. Establish `b6` using `le_abs_self a6`.

Establish `b9s` using `le_abs_self a9s`. Establish `bx` using `le_abs_self Fm.x1`. Establish `n1` using `abs_nonneg a1`. Establish `n2` using `abs_nonneg a2`. Establish `n5` using `abs_nonneg a5`.

Establish `n9` using `abs_nonneg a9`. Establish `nD` using `abs_nonneg aD`. Establish `nA` using `abs_nonneg aA`. Establish `nc` using `abs_nonneg ac`. Establish `nP` using `abs_nonneg aP`.

Establish `n35` using `abs_nonneg a35`. Establish `n6` using `abs_nonneg a6`. Establish `n9s` using `abs_nonneg a9s`. Establish `nx` using `abs_nonneg Fm.x1`. Establish `hx1 : Fm.x1 < x` using `by linarith`.

Establish `A1` using `ha1 x (by linarith) i`. Establish `A2` using `ha2 x (by linarith) i`. Establish `A5` using `ha5 x (by linarith) i`. Establish `A9` using `ha9 x (by linarith) i`. Establish `AD` using `haD x (by linarith) i`.

Establish `AA` using `haA x (by linarith) i`. Establish `Ac` using `hac x (by linarith) i`. Establish `AP` using `haP x (by linarith) i`. Establish `A35` using `ha35 x (by linarith) i`. Establish `S6` using `ha6 x (by linarith) hx1 i`.

Establish `S9` using `ha9s x (by linarith) hx1 i`. Apply `VanishingOnXAndXPlus.eight_amplitude_bounds_of_source` to reduce the goal to its premises. Establish `Q1` using `constant_bound_mono (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 C1 (CS + Cg + 2) C (by linarith [le_max_left (CS + Cg + 2) 0]) AP`. Establish `Q2` using `weightStatement_holds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT (CS + Cg + 2) C hCn0 hCL A1 AP`. Establish `Dec0` using `abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant 0 Ca Ch hCn0 hCn0 hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA`.

Establish `DecP` using `abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant Cpr Ca Ch hCn0 hCpr hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA`. Establish `Q4` using `abs_bound_of_zero_decay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C Ch (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl Dec0)`. Establish `L2D` using `L2_decay_of_admissible (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT CDl (CS + Cg + 2) Cpr C Ch hCn0 hCpr hCL hCh0 hChD A1 A2 AP`. Establish `Q6` using `lossStatement_of_bounds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C C δ hC2 le_rfl S6.1 S6.2 hCA A5 Q2 Q4`. Establish `Q7` using `decayProp_of_l2AbsDecay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 Cpr C C Ch δ hC2 le_rfl S6.1 S6.2 hCA A5 L2D (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl DecP)`.

Conclude with `⟨Q1, Q2, A35.1, Q4, Ac, A35.2, Q6, Q7⟩`.
-/
theorem ampBounds_uniform_of_inputs :
    ∀ Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS : ℝ, 0 ≤ hilbertNinetyConstant → 0 ≤ Ca → ∃ C C2 Ch : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧
      ∀ (eps : ℝ) (Fm : FamP eps),
      (∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm1 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 CPT)) →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 CDl)) →
      VanishingOnXAndXPlusBranching.admF5 Fm Cg cb Cu cT CT C0 → VanishingOnXAndXPlusBranching.admF9 Fm Cg cb Cu cT CT C0 C1 →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => DegreeRatioUnitShiftBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 hilbertNinetyConstant)) →
      (∀ Cn, (OwnEv Fm fun C' Cl x i => AbsAllParameters (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cn Ca)) →
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.PrimeSumLogBound (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1) →
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm11 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 C1 CS) →
      VanishingOnXAndXPlusBranching.FamilyTwelfthHypothesis Fm → ∀ Cpr : ℝ, ∀ δ > 0,
      (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  intro Cg cb Cu cT CT C0 A C1 CPT CDl hilbertNinetyConstant Ca CS hilbertNinetyConstant_pos hCa
  have hA6 : 0 ≤ 6 * Real.exp 1 * Real.pi * |A| := by positivity
  have hAA : 6 * Real.exp 1 * Real.pi * A ≤ 6 * Real.exp 1 * Real.pi * |A| :=
    mul_le_mul_of_nonneg_left (le_abs_self A) (by positivity)
  obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = max CPT 0 + max (CS + Cg + 2) 0 + 6 + Ca +
      6 * Real.exp 1 * Real.pi * |A| := ⟨_, rfl⟩
  obtain ⟨Ch, hChd⟩ : ∃ Ch : ℝ, Ch = max CDl 0 + 1 := ⟨_, rfl⟩
  have hm1 := le_max_right CPT 0
  have hm2 := le_max_right (CS + Cg + 2) 0
  have hm3 := le_max_left CDl 0
  have hm4 := le_max_right CDl 0
  have hC0 : 0 ≤ C := by linarith
  have hCL : max CPT 0 + max (CS + Cg + 2) 0 + 6 ≤ C := by linarith
  have hCaC : Ca ≤ C := by linarith
  have hC2 : 2 ≤ C := by linarith
  have hCA : 6 * Real.exp 1 * Real.pi * A ≤ C := by linarith
  have hCh0 : 0 ≤ Ch := by linarith
  have hChD : CDl ≤ Ch := by linarith
  have hChD1 : CDl + 1 ≤ Ch := by linarith
  refine ⟨C, 6 * C + C ^ 2 + C * Ch, Ch, hC0, hCh0, ?_⟩
  intro eps Fm h1 h2 h5 h9 hDeg hAbs h4c h11 h12 Cpr δ hδ
  have hCn0 : 0 ≤ max Cpr 0 := le_max_right _ _
  have hCpr : Cpr ≤ max Cpr 0 := le_max_left _ _
  have hCCh := mul_nonneg hC0 hCh0
  have hsq := sq_nonneg C
  have hP1 := ampConst_fam Fm Cg cb Cu cT CT C0 C1 CS h11 h12
  have h35 := family_third_fifth_items Fm Cg cb Cu cT CT C0 A C (6 * C + C ^ 2 + C * Ch) Ch hC0 hCh0
    (by linarith) (by linarith)
  unfold OwnEv at hP1 h35 h4c ⊢
  unfold VanishingOnXAndXPlusBranching.admF5 OwnEv at h5
  unfold VanishingOnXAndXPlusBranching.admF9 OwnEv at h9
  obtain ⟨a1, ha1⟩ := h1 (max Cpr 0)
  obtain ⟨a2, ha2⟩ := h2 (max Cpr 0)
  obtain ⟨a5, ha5⟩ := h5
  obtain ⟨a9, ha9⟩ := h9 (max Cpr 0)
  obtain ⟨aD, haD⟩ := hDeg (max Cpr 0)
  obtain ⟨aA, haA⟩ := hAbs (max Cpr 0)
  obtain ⟨ac, hac⟩ := h4c
  obtain ⟨aP, haP⟩ := hP1
  obtain ⟨a35, ha35⟩ := h35
  obtain ⟨a6, ha6⟩ := family_side_conditions_large Fm C δ hδ
  obtain ⟨a9s, ha9s⟩ := rank_power_le_scale_power Fm hilbertNinetyConstant hilbertNinetyConstant_pos
  refine ⟨|Fm.x1| + 1 + |a1| + |a2| + |a5| + |a9| + |aD| + |aA| + |ac| + |aP| + |a35| + |a6| + |a9s|,
    fun x hx i => ?_⟩
  have b1 := le_abs_self a1
  have b2 := le_abs_self a2
  have b5 := le_abs_self a5
  have b9 := le_abs_self a9
  have bD := le_abs_self aD
  have bA := le_abs_self aA
  have bc := le_abs_self ac
  have bP := le_abs_self aP
  have b35 := le_abs_self a35
  have b6 := le_abs_self a6
  have b9s := le_abs_self a9s
  have bx := le_abs_self Fm.x1
  have n1 := abs_nonneg a1
  have n2 := abs_nonneg a2
  have n5 := abs_nonneg a5
  have n9 := abs_nonneg a9
  have nD := abs_nonneg aD
  have nA := abs_nonneg aA
  have nc := abs_nonneg ac
  have nP := abs_nonneg aP
  have n35 := abs_nonneg a35
  have n6 := abs_nonneg a6
  have n9s := abs_nonneg a9s
  have nx := abs_nonneg Fm.x1
  have hx1 : Fm.x1 < x := by linarith
  have A1 := ha1 x (by linarith) i
  have A2 := ha2 x (by linarith) i
  have A5 := ha5 x (by linarith) i
  have A9 := ha9 x (by linarith) i
  have AD := haD x (by linarith) i
  have AA := haA x (by linarith) i
  have Ac := hac x (by linarith) i
  have AP := haP x (by linarith) i
  have A35 := ha35 x (by linarith) i
  have S6 := ha6 x (by linarith) hx1 i
  have S9 := ha9s x (by linarith) hx1 i
  apply VanishingOnXAndXPlus.eight_amplitude_bounds_of_source
  have Q1 := constant_bound_mono (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 C1 (CS + Cg + 2) C
    (by linarith [le_max_left (CS + Cg + 2) 0]) AP
  have Q2 := weightStatement_holds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT
    (CS + Cg + 2) C hCn0 hCL A1 AP
  have Dec0 := abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant 0 Ca Ch
    hCn0 hCn0 hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA
  have DecP := abs_decay_of_all_parameters (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CDl hilbertNinetyConstant Cpr Ca
    Ch hCn0 hCpr hCa hilbertNinetyConstant_pos hCh0 hChD1 S9 A2 A9 AD AA
  have Q4 := abs_bound_of_zero_decay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C Ch
    (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl Dec0)
  have L2D := L2_decay_of_admissible (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A (max Cpr 0) C1 CPT CDl
    (CS + Cg + 2) Cpr C Ch hCn0 hCpr hCL hCh0 hChD A1 A2 AP
  have Q6 := lossStatement_of_bounds (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 C C δ hC2 le_rfl S6.1 S6.2 hCA
    A5 Q2 Q4
  have Q7 := decayProp_of_l2AbsDecay (Fm.D x i) (Fm.L x i) _ _ Cg cb Cu cT CT C0 A C1 Cpr C C Ch δ hC2 le_rfl S6.1
    S6.2 hCA A5 L2D (abs_decay_mono_constants (Fm.D x i) (Fm.L x i) hCa hCaC le_rfl DecP)
  exact ⟨Q1, Q2, A35.1, Q4, Ac, A35.2, Q6, Q7⟩

end GlobalTheory

end
