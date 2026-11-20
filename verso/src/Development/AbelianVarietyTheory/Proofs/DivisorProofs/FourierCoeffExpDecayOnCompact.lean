import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff

namespace GlobalTheory.TauPeriod

/- English proof (translation)
Introduce `E _ _ _ g U a hU ha hper K hKU hK R hR`. Establish `hcovopen : IsOpen (cov U g)` using `hU.prod isOpen_univ`. Establish `hcont : ContinuousOn a (cov U g)` using `ha.continuousOn`. Establish `hKS : IsCompact (K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R))` using `hK.prod (isCompact_closedBall _ _)`. Establish `hsub : K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R) ⊆ cov U g` using `fun P hP => ⟨hKU hP.1, Set.mem_univ _⟩`.

Take `⟨C, hC⟩` from `hKS.exists_bound_of_continuousOn (hcont.mono hsub)`. Use `⟨max C 0, fun n b hb => ?_⟩` and prove the remaining obligations. Use `set f : (Fin g → ℂ) → ℂ := fun z => a (b, z) with hf_def`. Establish `hfd : Differentiable ℂ f` using `fun z => by`. Establish `hP : (b, z) ∈ cov U g` using `⟨hKU hb, Set.mem_univ _⟩`.

Establish `h1 : DifferentiableAt ℂ a (b, z)` using `ha.differentiableAt (hcovopen.mem_nhds hP)`. Conclude with `h1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)`. Establish `hfp : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z` using `fun i z => hper i (b, z) ⟨hKU hb, Set.mem_univ _⟩`. Establish `hs : ∀ i, (n i : ℝ) * ((Int.sign (n i) : ℤ) : ℝ) = |(n i : ℝ)| ∧ |((Int.sign (n i) : ℤ) : ℝ)| ≤ 1`. Introduce `i`.

Break down `lt_trichotomy (n i) 0 with h | h | h` into its components or cases. Establish `h' : (n i : ℝ) < 0` using `by exact_mod_cast h`. Simplify using `[Int.sign_eq_neg_one_of_neg h, abs_of_neg h']`. Simplify using `[h]`. Establish `h' : (0 : ℝ) < n i` using `by exact_mod_cast h`.

Simplify using `[Int.sign_eq_one_of_pos h, abs_of_pos h']`. Use `set w : Fin g → ℂ := fun i => Complex.I * (((-(R * ((Int.sign (n i) : ℤ) : ℝ))) : ℝ) : ℂ) with hw`. Establish `htr` using `cf_translate f hfd hfp n w`. Establish `hsum : ∑ i, (n i : ℝ) * (w i).im = -R * l1 n`. Rewrite using `[l1, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `him : (w i).im = -(R * ((Int.sign (n i) : ℤ) : ℝ))` using `by simp [hw]`. Rewrite using `[him, ← (hs i).1]`. Expand and normalize the polynomial expressions, which then agree. Establish `hex : ‖ex n w‖ = Real.exp (2 * π * R * l1 n)`.

Rewrite using `[norm_ex, hsum]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hvol : volume (Set.Icc (0 : Fin g → ℝ) 1) = 1` using `by simp [Real.volume_Icc_pi]`. Establish `hbound : ‖cf (fun z => f (z + w)) n‖ ≤ C`.

Unfold `cf`. Establish `hvr : (volume : Measure (Fin g → ℝ)).real (Set.Icc (0 : Fin g → ℝ) 1) = 1`. Simplify using `[Measure.real, hvol]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`.

Establish `h1 : ‖cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ))‖ = 1`. Rewrite using `[Complex.norm_exp]`. Establish `: (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ)).re = 0`. Establish `e : ∑ i, (n i : ℂ) * (x i : ℂ) = ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[e]`.

Simplify using the standard rewrite rules. Rewrite using `[this, Real.exp_zero]`. Rewrite using `[h1, mul_one]`. Apply `hC` to reduce the goal to its premises. Use `⟨hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `(pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_` and prove the remaining obligations. Establish `hx1 : ‖((x i : ℝ) : ℂ)‖ ≤ 1`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_le]`. Prove the components needed by the constructor for the conclusion.

Establish `h0 : (0 : ℝ) ≤ x i` using `hx.1 i`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hx.2 i`. Establish `hw1 : ‖w i‖ ≤ R`. Simplify using `only [hw, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hR]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hmain : ‖cf f n‖ * Real.exp (2 * π * R * l1 n) ≤ C`. Rewrite using `[mul_comm, ← hex, ← norm_mul, ← htr]`. Conclude with `hbound`.

Establish `e : Real.exp (2 * π * R * l1 n) * Real.exp (-(2 * π * R) * l1 n) = 1`. Rewrite using `[← Real.exp_add, show 2 * π * R * l1 n + -(2 * π * R) * l1 n = 0 by ring, Real.exp_zero]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, e, mul_one]`. Use `_ ≤ max C 0 * Real.exp (-(2 * π * R) * l1 n) := mul_le_mul_of_nonneg_right (hmain.trans (le_max_left _ _)) (Real.exp_pos _).le`.
-/
theorem fibreCoeff_decay : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} (a : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ a (cov U g) → (∀ j : Fin g, ∀ P ∈ cov U g, a (P.1, P.2 + Pi.single j 1) = a P) → ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n : Fin g → ℤ, ∀ b ∈ K, ‖cf (fun z => a (b, z)) n‖ ≤ M * Real.exp (-(2 * π * R) * l1 n) := by
  intro E _ _ _ g U a hU ha hper K hKU hK R hR
  have hcovopen : IsOpen (cov U g) := hU.prod isOpen_univ
  have hcont : ContinuousOn a (cov U g) := ha.continuousOn
  have hKS : IsCompact (K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R)) :=
    hK.prod (isCompact_closedBall _ _)
  have hsub : K ×ˢ Metric.closedBall (0 : Fin g → ℂ) (1 + R) ⊆ cov U g :=
    fun P hP => ⟨hKU hP.1, Set.mem_univ _⟩
  obtain ⟨C, hC⟩ := hKS.exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨max C 0, fun n b hb => ?_⟩
  set f : (Fin g → ℂ) → ℂ := fun z => a (b, z) with hf_def
  have hfd : Differentiable ℂ f := fun z => by
    have hP : (b, z) ∈ cov U g := ⟨hKU hb, Set.mem_univ _⟩
    have h1 : DifferentiableAt ℂ a (b, z) := ha.differentiableAt (hcovopen.mem_nhds hP)
    exact h1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)
  have hfp : ∀ (i : Fin g) z, f (z + Pi.single i 1) = f z := fun i z =>
    hper i (b, z) ⟨hKU hb, Set.mem_univ _⟩
  have hs : ∀ i, (n i : ℝ) * ((Int.sign (n i) : ℤ) : ℝ) = |(n i : ℝ)| ∧
      |((Int.sign (n i) : ℤ) : ℝ)| ≤ 1 := by
    intro i
    rcases lt_trichotomy (n i) 0 with h | h | h
    · have h' : (n i : ℝ) < 0 := by exact_mod_cast h
      simp [Int.sign_eq_neg_one_of_neg h, abs_of_neg h']
    · simp [h]
    · have h' : (0 : ℝ) < n i := by exact_mod_cast h
      simp [Int.sign_eq_one_of_pos h, abs_of_pos h']
  set w : Fin g → ℂ := fun i => Complex.I * (((-(R * ((Int.sign (n i) : ℤ) : ℝ))) : ℝ) : ℂ)
    with hw
  have htr := cf_translate f hfd hfp n w
  have hsum : ∑ i, (n i : ℝ) * (w i).im = -R * l1 n := by
    rw [l1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have him : (w i).im = -(R * ((Int.sign (n i) : ℤ) : ℝ)) := by simp [hw]
    rw [him, ← (hs i).1]
    ring
  have hex : ‖ex n w‖ = Real.exp (2 * π * R * l1 n) := by
    rw [norm_ex, hsum]
    congr 1
    ring
  have hvol : volume (Set.Icc (0 : Fin g → ℝ) 1) = 1 := by simp [Real.volume_Icc_pi]
  have hbound : ‖cf (fun z => f (z + w)) n‖ ≤ C := by
    unfold cf
    have hvr : (volume : Measure (Fin g → ℝ)).real (Set.Icc (0 : Fin g → ℝ) 1) = 1 := by
      simp [Measure.real, hvol]
    calc _ ≤ C * (volume : Measure (Fin g → ℝ)).real (Set.Icc (0 : Fin g → ℝ) 1) :=
          norm_setIntegral_le_of_norm_le_const (by rw [hvol]; exact ENNReal.one_lt_top)
            (fun x hx => ?_)
      _ = C := by rw [hvr, mul_one]
    rw [norm_mul]
    have h1 : ‖cexp (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (-(2 * π * I) * ∑ i, (n i : ℂ) * (x i : ℂ)).re = 0 := by
        have e : ∑ i, (n i : ℂ) * (x i : ℂ) = ((∑ i, (n i : ℝ) * x i : ℝ) : ℂ) := by
          push_cast; rfl
        rw [e]; simp
      rw [this, Real.exp_zero]
    rw [h1, mul_one]
    apply hC
    refine ⟨hb, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => ?_
    have hx1 : ‖((x i : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor
      · have h0 : (0 : ℝ) ≤ x i := hx.1 i
        linarith
      · exact hx.2 i
    have hw1 : ‖w i‖ ≤ R := by
      simp only [hw, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_neg, abs_mul, abs_of_nonneg hR]
      calc R * |((Int.sign (n i) : ℤ) : ℝ)| ≤ R * 1 := mul_le_mul_of_nonneg_left (hs i).2 hR
        _ = R := mul_one R
    calc ‖((fun i => ((x i : ℝ) : ℂ)) + w) i‖ = ‖((x i : ℝ) : ℂ) + w i‖ := rfl
      _ ≤ ‖((x i : ℝ) : ℂ)‖ + ‖w i‖ := norm_add_le _ _
      _ ≤ 1 + R := add_le_add hx1 hw1
  have hmain : ‖cf f n‖ * Real.exp (2 * π * R * l1 n) ≤ C := by
    rw [mul_comm, ← hex, ← norm_mul, ← htr]
    exact hbound
  have e : Real.exp (2 * π * R * l1 n) * Real.exp (-(2 * π * R) * l1 n) = 1 := by
    rw [← Real.exp_add, show 2 * π * R * l1 n + -(2 * π * R) * l1 n = 0 by ring, Real.exp_zero]
  calc ‖cf f n‖ = (‖cf f n‖ * Real.exp (2 * π * R * l1 n)) * Real.exp (-(2 * π * R) * l1 n) := by
        rw [mul_assoc, e, mul_one]
    _ ≤ max C 0 * Real.exp (-(2 * π * R) * l1 n) :=
        mul_le_mul_of_nonneg_right (hmain.trans (le_max_left _ _)) (Real.exp_pos _).le

end GlobalTheory.TauPeriod
