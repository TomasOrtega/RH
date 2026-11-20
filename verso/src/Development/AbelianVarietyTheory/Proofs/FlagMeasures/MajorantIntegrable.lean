import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableExpNegMulOfSublevelGrowthStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.Count.Majorant

/- English proof (translation)
Establish `hs : (1 : ℝ) ≤ Real.sqrt q`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]`. Conclude with `Real.sqrt_le_sqrt (by exact_mod_cast hq)`. Establish `hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q)`. Establish `h1 : d / Real.sqrt q ≤ d` using `div_le_self hd hs`.

Conclude with `le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)`. Establish `key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q)`. Rewrite using `[div_mul_eq_mul_div, div_mul_div_comm]`. Establish `hmul` using `mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)`. Unfold `GlobalTheory.Count.decE`.

Rewrite using `[← Real.exp_add, Real.exp_le_exp, key]`. Use polynomial arithmetic with `[hmul]`.
-/
theorem decE_le_exp (q : ℕ) (hq : 1 ≤ q) (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * d)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  have hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q) := by
    have h1 : d / Real.sqrt q ≤ d := div_le_self hd hs
    exact le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)
  have key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm]
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add, Real.exp_le_exp, key]
  nlinarith [hmul]

/- English proof (translation)
Establish `hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true)`. Unfold `GlobalTheory.Count.rkR at h0`. Break down `Nat.min_eq_zero_iff.mp h0 with h1 | h1` into its components or cases. Use `left`. Introduce `a`.

Establish `ha : a ∉ univ.filter (fun a => ε a = true)`. Rewrite using `[Finset.card_eq_zero.mp h1]`. Simplify using the standard rewrite rules. Simplify using `using ha`. Use `right`.

Introduce `a`. Establish `ha : a ∉ univ.filter (fun a => ε a = false)`. Rewrite using `[Finset.card_eq_zero.mp h1]`. Simplify using the standard rewrite rules. Simplify using `using ha`.

Establish `hJ : Jm ε = 1 ∨ Jm ε = -1`. Break down `hall with hf | ht` into its components or cases. Use `right`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]`.

Use `left`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]`. Establish `hg : inUJ ε (uMat g)` using `g.2`. Establish `hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ`.

Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Unfold `inUJ at hg`. Apply the tactic sequence `rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg`. Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality.

Unfold `GlobalTheory.Count.dOp`. Establish `hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0` using `ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]`. Rewrite using `[le_antisymm hle (norm_nonneg _), Real.log_zero]`. Establish `hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ)` using `by simp [inP, inG]`. Take `⟨hb0, hb1, -⟩` from `GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0`.

Rewrite `hb0`, `hb1` using `[NormedSpace.exp_zero, mul_one]`. Establish `hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0` using `by simp [hs]`. Rewrite `hb1` using `[hs0, Real.sqrt_zero]`. Use polynomial arithmetic with `[Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]`.
-/
theorem dOp_eq_zero {n : ℕ} (ε : Fin n → Bool) (h0 : rkR ε = 0) (g : UJ ε) : dOp (uMat g) = 0 := by
  have hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true) := by
    unfold GlobalTheory.Count.rkR at h0
    rcases Nat.min_eq_zero_iff.mp h0 with h1 | h1
    · left
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = true) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
    · right
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = false) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
  have hJ : Jm ε = 1 ∨ Jm ε = -1 := by
    rcases hall with hf | ht
    · right
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]
    · left
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]
  have hg : inUJ ε (uMat g) := g.2
  have hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold inUJ at hg
    rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold GlobalTheory.Count.dOp
    have hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0 :=
      ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]
    rw [le_antisymm hle (norm_nonneg _), Real.log_zero]
  · have hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
    obtain ⟨hb0, hb1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0
    rw [NormedSpace.exp_zero, mul_one] at hb0 hb1
    have hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hs]
    rw [hs0, Real.sqrt_zero] at hb1
    nlinarith [Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]

/- English proof (translation)
Introduce `n ε h s hh hcase`. Take `⟨C, -, hC⟩` from `GlobalTheory.T.haar_ball_growth_unitaryJ n ε`. Establish `hcont : Continuous (fun g : UJ ε => dOp (uMat g))` using `(GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2`. Establish `hmeas : Measurable (fun g : UJ ε => dOp (uMat g))` using `hcont.measurable`. Establish `hdec : Continuous (decE (rkR ε) h)`.

Unfold `GlobalTheory.Count.decE`. Use `fun_prop`. Establish `hint_meas : AEStronglyMeasurable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε)` using `((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable`. Distinguish the cases in `hq : rkR ε = 0`. Establish `hz : ∀ g : UJ ε, dOp (uMat g) = 0` using `fun g => dOp_eq_zero ε hq g`.

Establish `hI` using `GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε) (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)`. Use `hI.congr (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Simplify using `[hz g, GlobalTheory.Count.decE]`. Establish `hq1 : 1 ≤ rkR ε` using `Nat.one_le_iff_ne_zero.mpr hq`. Establish `hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h` using `hcase.resolve_left hq`.

Establish `hrk : rkR ε ≤ n`. Unfold `GlobalTheory.Count.rkR`. Conclude with `(min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)`. Establish `hn : 1 ≤ n` using `hq1.trans hrk`. Establish `hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g)` using `fun g => ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1`.

Establish `hsq : 0 < Real.sqrt (rkR ε)` using `Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)`. Establish `hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s`. Establish `: s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε))` using `(lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hI` using `(GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε) (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))`.

Use `hI.mono' hint_meas (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Establish `hd` using `hpos g`. Establish `hE` using `decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd`. Establish `hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))`. Unfold `GlobalTheory.Count.decE`.

Check the signs of the components of the expression. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg hnn]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, ← Real.exp_add]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem majorant_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 0 ≤ h → (rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) → Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  intro n ε h s hh hcase
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.haar_ball_growth_unitaryJ n ε
  have hcont : Continuous (fun g : UJ ε => dOp (uMat g)) :=
    (GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2
  have hmeas : Measurable (fun g : UJ ε => dOp (uMat g)) := hcont.measurable
  have hdec : Continuous (decE (rkR ε) h) := by
    unfold GlobalTheory.Count.decE
    fun_prop
  have hint_meas : AEStronglyMeasurable
      (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) :=
    ((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable
  by_cases hq : rkR ε = 0
  · have hz : ∀ g : UJ ε, dOp (uMat g) = 0 := fun g => dOp_eq_zero ε hq g
    have hI := GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)
    refine hI.congr (ae_of_all _ fun g => ?_)
    simp [hz g, GlobalTheory.Count.decE]
  · have hq1 : 1 ≤ rkR ε := Nat.one_le_iff_ne_zero.mpr hq
    have hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h := hcase.resolve_left hq
    have hrk : rkR ε ≤ n := by
      unfold GlobalTheory.Count.rkR
      exact (min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
    have hn : 1 ≤ n := hq1.trans hrk
    have hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g) := fun g =>
      ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    have hsq : 0 < Real.sqrt (rkR ε) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)
    have hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s := by
      have : s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε)) :=
        (lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)
      linarith
    have hI := (GlobalTheory.T.integrable_exp_neg_mul_of_sublevel_le_exp (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))
    refine hI.mono' hint_meas (ae_of_all _ fun g => ?_)
    have hd := hpos g
    have hE := decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd
    have hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      unfold GlobalTheory.Count.decE
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))
        ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt (rkR ε)) * dOp (uMat g))) *
            Real.exp (s * dOp (uMat g)) := mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
      _ = Real.exp (h / 8) * Real.exp (-((h / (8 * Real.sqrt (rkR ε)) - s) * dOp (uMat g))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end GlobalTheory.Count.Majorant
