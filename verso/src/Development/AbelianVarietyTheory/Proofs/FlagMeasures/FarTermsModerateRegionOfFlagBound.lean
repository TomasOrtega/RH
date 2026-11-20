import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermSum
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FarTermsLatticeBound
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GapThresholdPaysFarTerms

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.Deep

/- English proof (translation)
Take `⟨-, -, -, hpos, -⟩` from `B.e_adm`. Establish `h` using `hpos 1 (fun _ => 1) (fun _ => 1)`. Simplify using `at h`. Simplify using `using (Complex.le_def.1 h).1`.
-/
theorem farModerate_e_one_nonneg (B : RowsAut) : 0 ≤ (B.e 1).re := by
  obtain ⟨-, -, -, hpos, -⟩ := B.e_adm
  have h := hpos 1 (fun _ => 1) (fun _ => 1)
  simp at h
  simpa using (Complex.le_def.1 h).1

/- English proof (translation)
Establish `hn' : (8 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hq' : (1 : ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hqn' : (q : ℝ) ≤ n`. Establish `: q ≤ n` using `le_trans (Nat.le_self_pow (by norm_num) q) hqn`.

Conclude with `this` after adjusting the coercions. Establish `hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2` using `by positivity`. Establish `hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8` using `pow_le_pow_right₀ (by linarith) (by norm_num)`. Establish `hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2` using `one_le_pow₀ hf'`. Establish `hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2` using `by nlinarith`.

Establish `hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2` using `by nlinarith`. Use `⟨by positivity, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q`. Combine the equalities or inequalities in the displayed calculation. Establish `hspos : 0 < Real.sqrt (2 * (q : ℝ))` using `Real.sqrt_pos.2 (by linarith)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_le_div_iff₀ hD (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs`. Establish `hlog : (0.6931471803 : ℝ) < Real.log 2` using `Real.log_two_gt_d9`.

Establish `h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1` using `(div_le_one hD).2 hnD`. Establish `h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) = 2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2))` using `by ring`. Rewrite using `[h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem epN_pos_and_le_inv_sqrt_and_mul_le_log_two (n f q : ℕ) (hn : 8 ≤ n) (hf : 1 ≤ f) (hq : 1 ≤ q)
    (hqn : q ^ 2 ≤ n) :
    0 < 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ∧
      1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / Real.sqrt (2 * (q : ℝ)) ∧
      2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) ≤ Real.log 2 := by
  have hn' : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ≤ n := by
    have : q ≤ n := le_trans (Nat.le_self_pow (by norm_num) q) hqn
    exact_mod_cast this
  have hD : 0 < (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by positivity
  have hn8 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hf2 : (1 : ℝ) ≤ (f : ℝ) ^ 2 := one_le_pow₀ hf'
  have hnD : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 8 * (f : ℝ) ^ 2 := by nlinarith
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_⟩
  · have hs : Real.sqrt (2 * (q : ℝ)) ≤ 2 * q :=
      calc Real.sqrt (2 * (q : ℝ)) ≤ Real.sqrt ((2 * (q : ℝ)) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * q := Real.sqrt_sq (by linarith)
    have hspos : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    calc 1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 / (2 * q) := by
          rw [div_le_div_iff₀ hD (by linarith)]
          nlinarith
      _ ≤ 1 / Real.sqrt (2 * (q : ℝ)) := one_div_le_one_div_of_le hspos hs
  · have hlog : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h1 : (n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2) ≤ 1 := (div_le_one hD).2 hnD
    have h2 : 2 * (n : ℝ) ^ 2 * (1 / 10 ^ 6 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) =
        2 / 10 ^ 6 * ((n : ℝ) ^ 2 / ((n : ℝ) ^ 8 * (f : ℝ) ^ 2)) := by ring
    rw [h2]
    linarith

/- English proof (translation)
Introduce `hFM hFB Cg hCg`. Use `⟨8, fun B d p q b hq hCH => ?_⟩` and prove the remaining obligations. Take `⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩` from `GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH`. Take `⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩` from `hCH`. Establish `htq' : tauStar B q b < 1 / 2` using `(htq hq).1`.

Establish `he1 : 0 ≤ (B.e 1).re` using `farModerate_e_one_nonneg B`. Establish `hK : 0 ≤ (∏ v, d v) * (B.e 1).re` using `mul_nonneg hdpos.le he1`. Take `⟨hep0, hepq, heplog⟩` from `epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn`. Take `⟨hA, hB, hC⟩` from `GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le`. Take `⟨-, -, hfin, -⟩` from `hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)`.

Establish `hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))`. Introduce `x hx`. Take `⟨hs, hsum⟩` from `hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x`. Establish `hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖)`. Rewrite using `[ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]`.

Simplify using `only [ofReal_norm]`. Both sides reduce to the same expression. Establish `hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤ (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f))`. Establish `ht1 : tauStar B q b ≤ tau1 B.I x` using `le_min htq'.le hx.2`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor`.

Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Conclude with `div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2) (pow_le_pow_left₀ htpos.le ht1 2)`. Establish `hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))` using `by positivity`. Rewrite using `[hx1]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]`. Use `congr 1`. Use `show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem farModerate_of_farBound :
    GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.Deep.FarBound → GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.FarModerate := by
  intro hFM hFB Cg hCg
  refine ⟨8, fun B d p q b hq hCH => ?_⟩
  obtain ⟨-, hrd, hf1, -, -, h2q, -, hmin, hdpos, -, htpos, htq, h, hh, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg 8 d p q b le_rfl hCH
  obtain ⟨hDS, hSig, hn0, hqn, -, hlf, hb2, -, -, hg1, hgb, -, -, -, -⟩ := hCH
  have htq' : tauStar B q b < 1 / 2 := (htq hq).1
  have he1 : 0 ≤ (B.e 1).re := farModerate_e_one_nonneg B
  have hK : 0 ≤ (∏ v, d v) * (B.e 1).re := mul_nonneg hdpos.le he1
  obtain ⟨hep0, hepq, heplog⟩ := epN_pos_and_le_inv_sqrt_and_mul_le_log_two B.I.n B.I.f q hn0 hf1 hq hqn
  obtain ⟨hA, hB, hC⟩ := GlobalTheory.gap_threshold_pays_far_terms Cg B.I.n B.I.f q B.I.rd (B.g : ℝ) b h
    (tauStar B q b) hCg (by omega) hf1 hq hqn hrd hlf hb2 (Nat.one_le_cast.2 hg1) hgb hh.ge le_rfl htq'.le
  obtain ⟨-, -, hfin, -⟩ := hFM B.I B.μf B.fund B.fund_spec p q hSig h2q 1 (fun _ => 1) le_rfl
    (fun _ => le_rfl) (by simpa using hq) ∅ MeasurableSet.empty (Set.empty_subset _)
  have hpt : ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ≤
      ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) := by
    intro x hx
    obtain ⟨hs, hsum⟩ := hFB B d p q h (epN B) hDS hSig hmin.symm hq hgap hep0 hepq heplog hA hB h120 x
    have hx1 : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x = ENNReal.ofReal
        (∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) hs]
      simp only [ofReal_norm]
      rfl
    have hlat : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x ≤
        (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) := by
      have ht1 : tauStar B q b ≤ tau1 B.I x := le_min htq'.le hx.2
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos htpos 2)
        (pow_le_pow_left₀ htpos.le ht1 2)
    have hC0 : 0 ≤ 2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)) := by positivity
    rw [hx1]
    apply ENNReal.ofReal_le_ofReal
    calc ∑' γ : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d (epN B) x, ‖phe B d (x⁻¹ * γ.1 * x)‖
        ≤ (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) := hsum
      _ ≤ (∏ v, d v) * (B.e 1).re *
            (3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlat hK) hC0
      _ = (∏ v, d v) * (B.e 1).re *
            ((3 * Real.sqrt (B.I.n : ℝ) / tauStar B q b ^ 2) ^ (2 * (B.I.n ^ 2 * B.I.f)) *
            (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * epN B ^ 2 / 16)))) := by ring
      _ ≤ (∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) :=
          mul_le_mul_of_nonneg_left hC hK
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.farSum B d x ∂(B.I.muA B.μf)
      ≤ ∫⁻ _ in GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b,
          ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))))
          ∂(B.I.muA B.μf) := setLIntegral_mono measurable_const hpt
    _ = ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsModerate.moderate B q b) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal ((∏ v, d v) * (B.e 1).re * Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ)))) *
          B.I.muA B.μf B.fund := mul_le_mul_of_nonneg_left (measure_mono fun x hx => hx.1) (by simp)
    _ = ENNReal.ofReal (Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) * mainTerm B d) := by
      rw [← ENNReal.ofReal_toReal hfin.ne,
        ← ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      congr 1
      show _ = Real.exp (-((B.I.n : ℝ) ^ 2 * (B.I.f : ℝ))) *
        ((∏ v, d v) * ((B.I.muA B.μf) B.fund).toReal * (B.e 1).re)
      ring

end GlobalTheory.Deep
