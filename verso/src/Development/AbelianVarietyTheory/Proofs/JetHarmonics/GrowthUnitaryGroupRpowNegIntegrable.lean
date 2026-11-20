import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HaarUniquenessConjugation
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

open Matrix MeasureTheory Finset in
open scoped InnerProductSpace ENNReal in

/- English proof (translation)
Unfold `_root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG`. Introduce `k r μG A hμ hA`. Establish `hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG` using `(_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ`. Establish `hvol` using `_root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp`. Unfold `_root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol`.

Take `⟨C, hC⟩` from `hvol k r μG hW`. Establish `hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)`. Unfold `_root_.PI.BesselPeriodGGP.IsHaarOn at hμ`. Conclude with `ae_iff.2 hμ.2.2.1`. Use `set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef`.

Establish `hNcont : Continuous N`. Simplify using `only [hNdef]`. Unfold `_root_.Formalism.FourierDecayAlt.B.gN`. Use `fun_prop`. Establish `hNm : Measurable N` using `hNcont.measurable`.

Establish `h1 : ∀ᵐ x ∂μG, 1 ≤ N x` using `hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx`. Establish `hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1)` using `by positivity`. Establish `hAd : 2 * ((k:ℝ) + r) * (r + 1) < A`. Establish `: _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1)` using `by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring`. Rewrite `hA` using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd`. Use `set C' : ℝ := max C 0 with hC'`. Use `set q : ℝ := (2:ℝ) ^ (d - A) with hq`. Establish `hq0 : 0 ≤ q` using `by positivity`.

Establish `hq1 : q < 1` using `Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)`. Establish `hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)}` using `fun n ↦ measurableSet_le hNm measurable_const`. Establish `hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)} ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d)`. Introduce `n`. Use `(hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations.

Use `gcongr`. Conclude with `le_max_left _ _`. Establish `hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d) = C' * 2 ^ d * q ^ n`. Introduce `n`. Rewrite using `[← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq, ← Real.rpow_mul_natCast (by norm_num)]`.

Establish `e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d) = 2 ^ d * 2 ^ ((d - A) * n)`. Rewrite using `[← Real.rpow_add two_pos, ← Real.rpow_add two_pos]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Establish `hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n` using `(summable_geometric_of_lt_one hq0 hq1).mul_left _`. Establish `hC'0 : 0 ≤ C'` using `le_max_right _ _`. Establish `hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x` using `by filter_upwards [h1] with x hx`. Take `⟨n, hn1, hn2⟩` from `exists_nat_pow_near hx one_lt_two`.

Use `le_trans ?_ (ENNReal.le_tsum n)` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]`. Conclude with `ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))`. Use `⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Unfold `HasFiniteIntegral`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x ↦ ?_` and prove the remaining obligations. Rewrite using `[Real.enorm_eq_ofReal (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]`. Use `_ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt`. Use `_ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by`.

Rewrite using `[lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]`. Conclude with `tsum_congr fun n ↦ lintegral_indicator_const (hS n) _`. Use `_ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by`. Use `ENNReal.tsum_le_tsum fun n ↦ ?_` and prove the remaining obligations. Rewrite using `[← hkey n, ENNReal.ofReal_mul (by positivity)]`.

Use `gcongr`. Conclude with `hvolS n`. Use `_ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) := (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm`. Use `_ < ⊤ := ENNReal.ofReal_lt_top`.
-/
theorem _root_.GlobalTheory.gN_rpow_neg_integrable_haar : _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG := by
  unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.GrowthG
  intro k r μG A hμ hA
  have hW : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.B.GV k r) μG :=
    (_root_.GlobalTheory.HaarNotions.isHaarOn_iff_groups k r μG).1.1 hμ
  have hvol := _root_.Formalism.FourierDecayAlt.P.norm_ball_volume_sharp
  unfold _root_.Formalism.FourierDecayAlt.B2.VolSharp at hvol
  obtain ⟨C, hC⟩ := hvol k r μG hW
  have hU : ∀ᵐ x ∂μG, Matrix.of x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := by
    unfold _root_.PI.BesselPeriodGGP.IsHaarOn at hμ
    exact ae_iff.2 hμ.2.2.1
  set N : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun x ↦ _root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) with hNdef
  have hNcont : Continuous N := by
    simp only [hNdef]
    unfold _root_.Formalism.FourierDecayAlt.B.gN
    fun_prop
  have hNm : Measurable N := hNcont.measurable
  have h1 : ∀ᵐ x ∂μG, 1 ≤ N x := hU.mono fun x hx ↦ _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hx
  have hd0 : (0:ℝ) ≤ 2 * ((k:ℝ) + r) * (r + 1) := by positivity
  have hAd : 2 * ((k:ℝ) + r) * (r + 1) < A := by
    have : _root_.Formalism.FourierDecayAlt.ThreeDimData.AG k r = 4 * ((k:ℝ) + r) * (r + 1) := by unfold _root_.Formalism.FourierDecayAlt.ThreeDimData.AG; ring
    rw [this] at hA
    linarith
  set d : ℝ := 2 * ((k:ℝ) + r) * (r + 1) with hd
  set C' : ℝ := max C 0 with hC'
  set q : ℝ := (2:ℝ) ^ (d - A) with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hS : ∀ n : ℕ, MeasurableSet {x | N x ≤ (2:ℝ) ^ (n + 1)} := fun n ↦
    measurableSet_le hNm measurable_const
  have hvolS : ∀ n : ℕ, μG {x | N x ≤ (2:ℝ) ^ (n + 1)}
      ≤ ENNReal.ofReal (C' * ((2:ℝ) ^ (n + 1)) ^ d) := by
    intro n
    refine (hC _ (one_le_pow₀ one_le_two)).trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left _ _
  have hkey : ∀ n : ℕ, ((2:ℝ) ^ n) ^ (-A) * (C' * ((2:ℝ) ^ (n + 1)) ^ d)
      = C' * 2 ^ d * q ^ n := by
    intro n
    rw [← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_natCast_mul (by norm_num), hq,
      ← Real.rpow_mul_natCast (by norm_num)]
    have e : (2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)
        = 2 ^ d * 2 ^ ((d - A) * n) := by
      rw [← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring
    calc ((2:ℝ) ^ ((n:ℝ) * -A)) * (C' * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d))
        = C' * ((2:ℝ) ^ ((n:ℝ) * -A) * (2:ℝ) ^ (((n + 1 : ℕ) : ℝ) * d)) := by ring
      _ = C' * 2 ^ d * 2 ^ ((d - A) * n) := by rw [e]; ring
  have hsum : Summable fun n : ℕ ↦ C' * 2 ^ d * q ^ n :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hpt : ∀ᵐ x ∂μG, ENNReal.ofReal (N x ^ (-A)) ≤ ∑' n : ℕ,
      {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x := by
    filter_upwards [h1] with x hx
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx one_lt_two
    refine le_trans ?_ (ENNReal.le_tsum n)
    rw [Set.indicator_of_mem (show x ∈ {y | N y ≤ (2:ℝ) ^ (n + 1)} from hn2.le)]
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos (by positivity) hn1 (by linarith))
  refine ⟨(hNm.pow_const _).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖_root_.Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (-A)‖ₑ ∂μG
      = ∫⁻ x, ENNReal.ofReal (N x ^ (-A)) ∂μG := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.enorm_eq_ofReal
          (Real.rpow_nonneg (by unfold _root_.Formalism.FourierDecayAlt.B.gN; exact Real.sqrt_nonneg _) _)]
    _ ≤ ∫⁻ x, ∑' n : ℕ, {y | N y ≤ (2:ℝ) ^ (n + 1)}.indicator
          (fun _ ↦ ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A))) x ∂μG := lintegral_mono_ae hpt
    _ = ∑' n : ℕ, ENNReal.ofReal (((2:ℝ) ^ n) ^ (-A)) * μG {y | N y ≤ (2:ℝ) ^ (n + 1)} := by
        rw [lintegral_tsum fun n ↦ (measurable_const.indicator (hS n)).aemeasurable]
        exact tsum_congr fun n ↦ lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (C' * 2 ^ d * q ^ n) := by
        refine ENNReal.tsum_le_tsum fun n ↦ ?_
        rw [← hkey n, ENNReal.ofReal_mul (by positivity)]
        gcongr
        exact hvolS n
    _ = ENNReal.ofReal (∑' n : ℕ, C' * 2 ^ d * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n ↦ by positivity) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end GlobalTheory
