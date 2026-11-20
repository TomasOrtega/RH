import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.DataTies
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupCayleyBoundStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupBesselGrowthStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModel
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LastMajorantLengthSqGeAndPosStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOneStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassLowTypesSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedMassHighestToLowestKTypeLargeGapStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamiliesHaveLargeGapOfNumericalHypothesesStatement
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.InvLenMomentGap

/- English proof (translation)
Introduce `hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a`. Establish `hSG` using `(GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS`. Establish `hS'` using `hS`. Take `⟨hN, hF, hG, hSF⟩` from `hS'`. Establish `hb : 1 ≤ b`.

Take `⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩` from `hN`. Establish `e1` using `h7 (Fin.last _) (by simp only [Fin.val_last]; omega)`. Establish `e2` using `h8 (Fin.last _)`. Establish `e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)`. Establish `e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7` using `one_le_pow₀ e3`.

Establish `e5` using `neg_abs_le (lam (Fin.last _))`. Combine the linear relations using `[e1.2]`. Establish `hdg : 0 < dg ν` using `(hSF ν hν).2.1`. Take `⟨m1, -, m3, m4⟩` from `GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq (hF ν hν) hG`. Use `GlobalTheory.T.weightedMass_highestToLowestKType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw` and prove the remaining obligations.

Introduce `Q E hQ hE v hv hv1`. Apply the tactic sequence `have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2`. Establish `hv1' : ‖(v : (R ν).H)‖ = 1` using `hv1`. Simplify using `only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass`. Establish `hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c` using `by filter_upwards [m1] with x hx`.

Take `⟨e1, e2⟩` from `GlobalTheory.T.last_majorant_length_sq_ge_and_pos k r z hG.1 hG.2.1 _ hx`. Use `⟨?_, fun c => (e2 c).1⟩` and prove the remaining obligations. Use `(e2 (Fin.last r)).1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq` using `(((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _`.

Establish `key` using `GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one (Mt k r) νq r q (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc) (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2) (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val)) (fun …`. Conclude with `div_nonneg (hx.2 _).le (hx.2 _).le)`. Use `hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)`. Use the proof step `(fun c => by`. Use `Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν 0 (r * q) (by omega) c v hv` as an intermediate fact.

Rewrite using `[hv1, one_pow, mul_one] at this)` and apply the resulting hypothesis. Establish `hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q)`. Rewrite using `[← pow_mul, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hpw]`. Use `le_trans (lintegral_mono_ae ?_) key` and prove the remaining obligations. Use `filter_upwards [hpos] with x hx`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))` and prove the remaining obligations. Rewrite using `[GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]`.

Use `pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _` and prove the remaining obligations. Rewrite using `[inv_eq_one_div]`. Conclude with `div_le_div_of_nonneg_right hx.1 (hx.2 a).le`.
-/
theorem inv_len_moment_gap : GlobalTheory.GapIn.Hyp → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (lb : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), Setup lam u b bv ga h q0 z π μW μN μG νq R lb dg → 1 ≤ Tz k r z → ∀ ν (q : ℕ), n1 ν ≤ q0 → r * q ≤ 2 * (2 * r + k + 1) ^ 2 → ∀ w : (R ν).H, PI.UpqRep.IsLowUnitH k r (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ)) (R ν).σ w → ∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lenA k r z (Matrix.of x) a)⁻¹ ^ (2 * q) * (dg ν * ‖lb ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((b ^ (2 * r)) ^ (2 * q)) := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R lb dg hS hT ν q hν hq w hw a
  have hSG := (GlobalTheory.T.families_have_largeGap_of_numericalHypotheses.2 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg).1 hS
  have hS' := hS
  obtain ⟨hN, hF, hG, hSF⟩ := hS'
  have hb : 1 ≤ b := by
    obtain ⟨hk, -, -, -, -, -, h7, h8, -, -, -, -, -, -, h15⟩ := hN
    have e1 := h7 (Fin.last _) (by simp only [Fin.val_last]; omega)
    have e2 := h8 (Fin.last _)
    have e3 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
    have e4 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 := one_le_pow₀ e3
    have e5 := neg_abs_le (lam (Fin.last _))
    linarith [e1.2]
  have hdg : 0 < dg ν := (hSF ν hν).2.1
  obtain ⟨m1, -, m3, m4⟩ := GlobalTheory.quotMeas_ae_mem_and_measurable hH.1.1.2.2.1 k r _ _ (R ν) Wp z π u μW μN μG νq
    (hF ν hν) hG
  refine GlobalTheory.T.weightedMass_highestToLowestKType_largeGap hH k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hS ν hν
    (fun y => (y a)⁻¹ ^ (2 * q)) _ (by fun_prop) (fun y => Even.pow_nonneg (even_two_mul q) _) ?_ w hw
  intro Q E hQ hE v hv hv1
  have hmass := (Gp91.GlobalTheory.T.bessel_functional_l2_bound_and_isometry hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg hSG ν hν).1 v v.2
  have hv1' : ‖(v : (R ν).H)‖ = 1 := hv1
  simp only [one_mul, hv1', one_pow, ENNReal.ofReal_one] at hmass
  have hpos : ∀ᵐ x ∂νq, 1 ≤ lenA k r z (Matrix.of x) (Fin.last r) ∧ ∀ c, 0 < lenA k r z (Matrix.of x) c := by
    filter_upwards [m1] with x hx
    obtain ⟨e1, e2⟩ := GlobalTheory.T.last_majorant_length_sq_ge_and_pos k r z hG.1 hG.2.1 _ hx
    refine ⟨?_, fun c => (e2 c).1⟩
    have := (e2 (Fin.last r)).1
    nlinarith
  have hmeas : AEMeasurable (fun x : Mt k r => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) νq :=
    (((m4 (lb ν) (hSF ν hν).1.1 v v.2).norm.aemeasurable).pow_const 2).const_mul _
  have key := GlobalTheory.T.lintegral_prod_pow_le_of_moments_mass_le_one (Mt k r) νq r q
    (fun c x => lenA k r z (Matrix.of x) c.succ / lenA k r z (Matrix.of x) c.castSucc)
    (fun x => dg ν * ‖lb ν ((R ν).σ (Matrix.of x) v)‖ ^ 2) (b ^ 2)
    (Finset.univ.filter (fun c : Fin r => a.val ≤ c.val))
    (fun c => (m3 _).div (m3 _))
    (fun c => by
      filter_upwards [hpos] with x hx
      exact div_nonneg (hx.2 _).le (hx.2 _).le)
    hmeas (fun x => by positivity) hmass (one_le_pow₀ hb)
    (fun c => by
      have := Gp91.GlobalTheory.T.family_setup_cayley_bound hH.1 k r Wp lam u b bv ga h q0 z π μW μN μG νq R lb dg Q E hSG hQ hE ν hν
        0 (r * q) (by omega) c v hv
      rwa [hv1, one_pow, mul_one] at this)
  have hpw : (b ^ 2) ^ (2 * (r * q)) = (b ^ (2 * r)) ^ (2 * q) := by
    rw [← pow_mul, ← pow_mul]; congr 1; ring
  rw [← hpw]
  refine le_trans (lintegral_mono_ae ?_) key
  filter_upwards [hpos] with x hx
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (by positivity))
  rw [GlobalTheory.InvLenMoment.prod_ratio (fun c => lenA k r z (Matrix.of x) c) hx.2 a]
  refine pow_le_pow_left₀ (inv_nonneg.2 (hx.2 a).le) ?_ _
  rw [inv_eq_one_div]
  exact div_le_div_of_nonneg_right hx.1 (hx.2 a).le

end GlobalTheory.InvLenMomentGap
