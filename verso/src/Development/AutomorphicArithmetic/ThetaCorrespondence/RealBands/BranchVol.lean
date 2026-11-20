import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

/- English proof (translation)
Establish `hS : Real.sqrt (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) ≤ 1 / 4` using `hg`. Establish `hS0 : 0 ≤ ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2` using `by positivity`. Establish `hS2 : ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2 ≤ 1 / 16`. Establish `h` using `Real.sq_sqrt hS0`. Establish `h0` using `Real.sqrt_nonneg (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hent : ∀ a b, ‖g a b‖ ^ 2 ≤ 2 * ‖(g - 1) a b‖ ^ 2 + 2 * (if a = b then (1 : ℝ) else 0)`. Introduce `a b`. Establish `hsplit : g a b = (g - 1) a b + (1 : Matrix (Fin n) (Fin n) ℂ) a b` using `by simp`. Establish `hone : ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖ ^ 2 = if a = b then (1 : ℝ) else 0`.

Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.one_apply, h]`. Establish `htri` using `norm_add_le ((g - 1) a b) ((1 : Matrix (Fin n) (Fin n) ℂ) a b)`. Rewrite `htri` using `[← hsplit]`. Establish `hp` using `norm_nonneg (g a b)`. Establish `hq` using `norm_nonneg ((g - 1) a b)`.

Establish `hr` using `norm_nonneg ((1 : Matrix (Fin n) (Fin n) ℂ) a b)`. Rewrite using `[← hone]`. Use polynomial arithmetic with `[sq_nonneg (‖(g - 1) a b‖ - ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖)]`. Establish `hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 ≤ 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hent a b`. Use `_ = 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n := by`. Simplify using `[Finset.sum_add_distrib, Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree. Use `show Real.sqrt (∑ a, ∑ b, ‖g a b‖ ^ 2) ≤ (n : ℝ) + 1`.

Rewrite using `[Real.sqrt_le_iff]`. Prove the components needed by the constructor for the conclusion. Check the signs of the components of the expression. Establish `h0 : (0 : ℝ) ≤ n` using `n.cast_nonneg`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem hsn_le_of_near {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : GlobalTheory.SepReal.hsn (g - 1) ≤ 1 / 4) :
    GlobalTheory.SepReal.hsn g ≤ (n : ℝ) + 1 := by
  have hS : Real.sqrt (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) ≤ 1 / 4 := hg
  have hS0 : 0 ≤ ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2 := by positivity
  have hS2 : ∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2 ≤ 1 / 16 := by
    have h := Real.sq_sqrt hS0
    have h0 := Real.sqrt_nonneg (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2)
    nlinarith
  have hent : ∀ a b, ‖g a b‖ ^ 2 ≤ 2 * ‖(g - 1) a b‖ ^ 2 + 2 * (if a = b then (1 : ℝ) else 0) := by
    intro a b
    have hsplit : g a b = (g - 1) a b + (1 : Matrix (Fin n) (Fin n) ℂ) a b := by simp
    have hone : ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖ ^ 2 = if a = b then (1 : ℝ) else 0 := by
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    have htri := norm_add_le ((g - 1) a b) ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
    rw [← hsplit] at htri
    have hp := norm_nonneg (g a b)
    have hq := norm_nonneg ((g - 1) a b)
    have hr := norm_nonneg ((1 : Matrix (Fin n) (Fin n) ℂ) a b)
    rw [← hone]
    nlinarith [sq_nonneg (‖(g - 1) a b‖ - ‖(1 : Matrix (Fin n) (Fin n) ℂ) a b‖)]
  have hsum : ∑ a, ∑ b, ‖g a b‖ ^ 2 ≤ 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n := by
    calc ∑ a, ∑ b, ‖g a b‖ ^ 2
        ≤ ∑ a, ∑ b, (2 * ‖(g - 1) a b‖ ^ 2 + 2 * (if a = b then (1 : ℝ) else 0)) := by
          gcongr with a _ b _
          exact hent a b
      _ = 2 * (∑ a, ∑ b, ‖(g - 1) a b‖ ^ 2) + 2 * n := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]
          ring
  show Real.sqrt (∑ a, ∑ b, ‖g a b‖ ^ 2) ≤ (n : ℝ) + 1
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have h0 : (0 : ℝ) ≤ n := n.cast_nonneg
    nlinarith

/- English proof (translation)
Establish `hn' : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hm1 : 1 ≤ ((n : ℝ) + 1) ^ 2` using `by nlinarith`. Establish `hB1 : 1 ≤ B ^ 2` using `by nlinarith`. Establish `hp1 : 1 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2` using `one_le_mul_of_one_le_of_one_le hm1 hB1`. Establish `hmP : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2` using `le_mul_of_one_le_right (by positivity) hB1`.

Establish `hqp : (n : ℝ) ^ 2 * B ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2`. Establish `hB2 : 0 ≤ B ^ 2` using `by positivity`. Establish `: (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_right this hB2`. Establish `hq0 : 0 ≤ (n : ℝ) ^ 2 * B ^ 2` using `by positivity`.

Establish `e1 : 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) = 512 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) ^ 2 * B ^ 2)`. Rewrite using `[one_div, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (8 * ((n : ℝ) + 1) * B) ^ 4 = 4096 * (((n : ℝ) + 1) ^ 2 * B ^ 2) ^ 2` using `by ring`. Establish `hX0 : 0 ≤ 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))`.

Rewrite using `[e1]`. Check the signs of the components of the expression. Establish `hX : 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ≤ (8 * ((n : ℝ) + 1) * B) ^ 4`. Rewrite using `[e1, e2]`. Use `mul_le_mul hmP hqp hq0 (by linarith)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hL4 : (4 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B` using `by nlinarith`. Establish `hL0 : 0 < 8 * ((n : ℝ) + 1) * B` using `by linarith`. Establish `hstep : (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4 ≤ (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_mul, pow_succ]`. Put the polynomial expressions in normal form. Establish `hexp : (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1) = Real.exp (((8 * n ^ 2 + 1 : ℕ) : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B))`. Rewrite using `[Real.exp_nat_mul, Real.exp_log hL0]`. Establish `hN : ((8 * n ^ 2 + 1 : ℕ) : ℝ) ≤ 11 * ((n : ℝ) + 1) ^ 4`.

Use `push_cast`. Use polynomial arithmetic with `[sq_nonneg ((n : ℝ) + 1), sq_nonneg (n : ℝ)]`. Establish `hlog : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B)` using `Real.log_nonneg (by linarith)`. Unfold `big`. Combine the equalities or inequalities in the displayed calculation.

Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `mul_le_mul_of_nonneg_right hN hlog` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem vol_arith (n : ℕ) (B : ℝ) (hn : 3 ≤ n) (hB : 1 ≤ B) :
    (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4 ≤ big 11 n B := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1 : 1 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
  have hB1 : 1 ≤ B ^ 2 := by nlinarith
  have hp1 : 1 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := one_le_mul_of_one_le_of_one_le hm1 hB1
  have hmP : ((n : ℝ) + 1) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := le_mul_of_one_le_right (by positivity) hB1
  have hqp : (n : ℝ) ^ 2 * B ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * B ^ 2 := by
    have hB2 : 0 ≤ B ^ 2 := by positivity
    have : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hB2
  have hq0 : 0 ≤ (n : ℝ) ^ 2 * B ^ 2 := by positivity
  have e1 : 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))
      = 512 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) ^ 2 * B ^ 2) := by
    rw [one_div, div_inv_eq_mul]
    ring
  have e2 : (8 * ((n : ℝ) + 1) * B) ^ 4 = 4096 * (((n : ℝ) + 1) ^ 2 * B ^ 2) ^ 2 := by ring
  have hX0 : 0 ≤ 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) := by
    rw [e1]
    positivity
  have hX : 1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ≤ (8 * ((n : ℝ) + 1) * B) ^ 4 := by
    rw [e1, e2]
    have := mul_le_mul hmP hqp hq0 (by linarith)
    nlinarith
  have hL4 : (4 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  have hL0 : 0 < 8 * ((n : ℝ) + 1) * B := by linarith
  have hstep : (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4
      ≤ (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1) := by
    calc (1 + 2 * ((n : ℝ) + 1) ^ 2 / (1 / (4 * (8 * (n : ℝ) * B) ^ 2))) ^ (2 * n ^ 2) * 4
        ≤ ((8 * ((n : ℝ) + 1) * B) ^ 4) ^ (2 * n ^ 2) * (8 * ((n : ℝ) + 1) * B) := by
          gcongr
      _ = (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1) := by
          rw [← pow_mul, pow_succ]
          ring_nf
  have hexp : (8 * ((n : ℝ) + 1) * B) ^ (8 * n ^ 2 + 1)
      = Real.exp (((8 * n ^ 2 + 1 : ℕ) : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B)) := by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  have hN : ((8 * n ^ 2 + 1 : ℕ) : ℝ) ≤ 11 * ((n : ℝ) + 1) ^ 4 := by
    push_cast
    nlinarith [sq_nonneg ((n : ℝ) + 1), sq_nonneg (n : ℝ)]
  have hlog : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by linarith)
  unfold big
  calc _ ≤ _ := hstep
    _ = _ := hexp
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hN hlog
      push_cast at this ⊢
      linarith

/- English proof (translation)
Establish `hVol : VolBall` using `GlobalTheory.T.volume_of_ball_bound`. Establish `hDegU : DegUpper` using `GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume GlobalTheory.T.unitary_near_identity_eq_exp_log_bound GlobalTheory.T.lowestKType_lieWord_normBound hVol`. Use `⟨11, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd`. Establish `hn` using `hP.three_le`.

Establish `hn' : (3 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hB1 : 1 ≤ B` using `RealAsm.one_le_B hP`. Establish `hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3)` using `RealAsm.gap_mono (by`. Establish `: (0 : ℝ) ≤ n` using `n.cast_nonneg`. Use polynomial arithmetic with `[pow_le_pow_left₀ this (by linarith : (n : ℝ) ≤ n + 1) 3]) hP.gap'`.

Establish `hdu` using `hDegU n ε' mu B hn hP.hmu hgap' hP.bound.2 H' σ hσ d hd`. Take `⟨-, htop, hvb⟩` from `hVol n ε' (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ((n : ℝ) + 1) (by positivity) (by positivity)`. Establish `hsub : nbh ε' (1 / 4) ⊆ {g | GlobalTheory.SepReal.hsn (umat g) ≤ (n : ℝ) + 1}` using `fun g hg => hsn_le_of_near _ hg`. Establish `h1` using `(measure_mono hsub).trans hvb`. Establish `h2` using `ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) h1`.

Rewrite `h2` using `[ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Establish `hd0 : 0 < d` using `hd.1`. Use `h2.trans ((mul_le_mul_of_nonneg_left hdu (by positivity)).trans ?_)` and prove the remaining obligations. Rewrite using `[← mul_div_assoc]`. Conclude with `div_le_div_of_nonneg_right (vol_arith n B hn hB1) hd0.le`.
-/
theorem UpperTheory.Lit.Branch.volDeg :
    VolDeg := by
  have hVol : VolBall := GlobalTheory.T.volume_of_ball_bound
  have hDegU : DegUpper := GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume GlobalTheory.T.unitary_near_identity_eq_exp_log_bound GlobalTheory.T.lowestKType_lieWord_normBound hVol
  refine ⟨11, by norm_num, ?_⟩
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd
  have hn := hP.three_le
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hB1 : 1 ≤ B := RealAsm.one_le_B hP
  have hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3) :=
    RealAsm.gap_mono (by
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      nlinarith [pow_le_pow_left₀ this (by linarith : (n : ℝ) ≤ n + 1) 3]) hP.gap'
  have hdu := hDegU n ε' mu B hn hP.hmu hgap' hP.bound.2 H' σ hσ d hd
  obtain ⟨-, htop, hvb⟩ := hVol n ε' (1 / (4 * (8 * (n : ℝ) * B) ^ 2)) ((n : ℝ) + 1) (by positivity) (by positivity)
  have hsub : nbh ε' (1 / 4) ⊆ {g | GlobalTheory.SepReal.hsn (umat g) ≤ (n : ℝ) + 1} := fun g hg => hsn_le_of_near _ hg
  have h1 := (measure_mono hsub).trans hvb
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop.ne) h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h2
  have hd0 : 0 < d := hd.1
  refine h2.trans ((mul_le_mul_of_nonneg_left hdu (by positivity)).trans ?_)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (vol_arith n B hn hB1) hd0.le
