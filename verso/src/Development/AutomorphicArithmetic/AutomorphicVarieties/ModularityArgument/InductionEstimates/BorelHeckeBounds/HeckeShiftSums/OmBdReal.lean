import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PkLaws
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.BlkCont
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

/- English proof (translation)
Establish `key : ∀ i : Fin (2 + 2), a i ≤ 2 * T + 10 * (C + s) ∧ -(2 * T + 10 * (C + s)) ≤ a i`. Introduce `i`. Establish `hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3` using `by revert i; decide`. Apply the tactic sequence `rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> linarith`. Combine the linear relations using `[(key i).1, (key j).2]`.
-/
private theorem omBd_real (a : Fin (2 + 2) → ℝ) (s C T : ℝ) (hs : 0 ≤ s) (hC : 0 ≤ C) (hT : 0 ≤ T)
    (h0 : a 1 ≤ a 0 + s) (h1 : a 2 ≤ a 1 + s) (h2 : a 3 ≤ a 2 + s) (h3 : a 0 + a 1 ≤ T + C)
    (h4 : -C ≤ a 0 + a 1 + (a 2 + a 3)) (i j : Fin (2 + 2)) : a i - a j ≤ 4 * T + 20 * (C + s) := by
  have key : ∀ i : Fin (2 + 2), a i ≤ 2 * T + 10 * (C + s) ∧ -(2 * T + 10 * (C + s)) ≤ a i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by revert i; decide
    rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> linarith
  linarith [(key i).1, (key j).2]

/- English proof (translation)
Introduce `K _ _`. Take `⟨ω, t, hred⟩` from `redEx (K := K)`. Take `⟨C, c, hC, hsg⟩` from `sgBasics ω hred.bor`. Take `⟨c', C', hc', hq⟩` from `hpQht (K := K)`. Take `⟨hq1, hqinv, -⟩` from `qhtBasic K (2 + 2)`.

Establish `hC0 : 0 ≤ C` using `zero_le_one.trans hC`. Use `set s : ℝ := |Real.log t| with hsdef`. Establish `hs : 0 ≤ s` using `abs_nonneg _`. Use `set A : ℝ := C * Real.exp (c * (20 * (C + s))) with hA`. Establish `hA0 : 0 ≤ A` using `by positivity`.

Use `⟨A + |C' / c'|, c'⁻¹, 4 * c, inv_pos.2 hc', by positivity, fun T x hT => ⟨fun hom => ?_, fun hom => ?_⟩⟩` and prove the remaining obligations. Take `⟨γ, hγ, ρ, hS, hF⟩` from `hred.full x`. Take `⟨h1, h2, h3⟩` from `hsg ρ _ hS`. Take `⟨hρ, -⟩` from `hS`. Establish `hH : HH (γ * x) ≤ T`.

Take `⟨δ, hδ, e⟩` from `(pkLaws (K := K)).2.2.2 ⟨γ, hγ⟩`. Establish `h` using `hom (Quotient.mk _ ⟨γ, hγ⟩)`. Unfold `qx at h`. Rewrite `h` using `[e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ]`. Conclude with `h`.

Establish `hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ)`. Conclude with `(Module.finrank_pos (R := ℚ) (M := K))` after adjusting the coercions. Establish `hL : Real.log (ρ 0 * ρ 1) ≤ T + C`. Establish `h4` using `(abs_le.1 h1).1`. Break down `le_total 0 (Real.log (ρ 0 * ρ 1)) with h | h` into its components or cases.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstep : ∀ i j : Fin (2 + 2), (j : ℕ) = i + 1 → Real.log (ρ j) ≤ Real.log (ρ i) + s`. Introduce `i j hij`. Establish `h` using `Real.log_le_log (mul_pos hred.pos (hρ j)) (hF i j hij)`.

Rewrite `h` using `[Real.log_mul hred.pos.ne' (hρ j).ne']`. Combine the linear relations using `[neg_abs_le (Real.log t)]`. Rewrite `h2` using `[Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul (hρ 0).ne' (hρ 1).ne', Real.log_mul (hρ 2).ne' (hρ 3).ne']`. Rewrite `hL` using `[Real.log_mul (hρ 0).ne' (hρ 1).ne']`. Establish `hR` using `omBd_real (fun i => Real.log (ρ i)) s C T hs hC0 hT (hstep 0 1 rfl) (hstep 1 2 rfl) (hstep 2 3 rfl) hL (abs_le.1 h2).1`.

Establish `h5` using `h3 (Real.exp (4 * T + 20 * (C + s))) (Real.one_le_exp (by positivity)) fun i j => by`. Rewrite using `[← Real.exp_log (div_pos (hρ i) (hρ j)), Real.log_div (hρ i).ne' (hρ j).ne']`. Conclude with `Real.exp_le_exp.2 (hR i j)`. Establish `h6 : qht x ≤ AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))` using `ciInf_le (f := fun δ : Gam K (2 + 2) => AutomorphicForm.height (((δ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2))) ⟨0, by rintro _ ⟨δ, rfl⟩; exact (height_pos _).le⟩ ⟨γ, hγ⟩`. Establish `h7 : C * Real.exp (4 * T + 20 * (C + s)) ^ c = A * Real.exp (((4 * c : ℕ) : ℝ) * T)`.

Rewrite using `[hA, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `h6.trans (h5.trans ?_)` and prove the remaining obligations.

Rewrite using `[h7]`. Conclude with `mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (Real.exp_pos _).le`. Unfold `Om at hom push Not at hom`. Take `⟨q, hq'⟩` from `hom`. Establish `h1` using `hq (qx q x)`.

Establish `h2 : qht (qx q x) = qht x` using `hqinv _ (q.out : Gam K (2 + 2)).2 x`. Rewrite `h1` using `[h2]`. Rewrite using `[← Real.le_log_iff_exp_le (zero_lt_one.trans_le (hq1 x))]`. Establish `h3 : (T - C') / c' ≤ Real.log (qht x)`. Rewrite using `[div_le_iff₀ hc']`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `h3` using `[sub_div, div_eq_inv_mul T]`. Combine the linear relations using `[le_abs_self (C' / c')]`.
-/
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.omBd :
    ∀ {K : Type} [Field K] [NumberField K], ∃ (C c : ℝ) (N : ℕ), 0 < c ∧ 0 ≤ C ∧ ∀ (T : ℝ) (x : G1 K (2 + 2)), 0 ≤ T → (Om T x → qht x ≤ C * Real.exp (N * T)) ∧ (¬ Om T x → Real.exp (c * T - C) ≤ qht x) := by
  intro K _ _
  obtain ⟨ω, t, hred⟩ := redEx (K := K)
  obtain ⟨C, c, hC, hsg⟩ := sgBasics ω hred.bor
  obtain ⟨c', C', hc', hq⟩ := hpQht (K := K)
  obtain ⟨hq1, hqinv, -⟩ := qhtBasic K (2 + 2)
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  set s : ℝ := |Real.log t| with hsdef
  have hs : 0 ≤ s := abs_nonneg _
  set A : ℝ := C * Real.exp (c * (20 * (C + s))) with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨A + |C' / c'|, c'⁻¹, 4 * c, inv_pos.2 hc', by positivity, fun T x hT => ⟨fun hom => ?_, fun hom => ?_⟩⟩
  · obtain ⟨γ, hγ, ρ, hS, hF⟩ := hred.full x
    obtain ⟨h1, h2, h3⟩ := hsg ρ _ hS
    obtain ⟨hρ, -⟩ := hS
    have hH : HH (γ * x) ≤ T := by
      obtain ⟨δ, hδ, e⟩ := (pkLaws (K := K)).2.2.2 ⟨γ, hγ⟩
      have h := hom (Quotient.mk _ ⟨γ, hγ⟩)
      unfold qx at h
      rw [e, mul_assoc, (hpSpec (K := K)).2.2.1 δ hδ] at h
      exact h
    have hd : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    have hL : Real.log (ρ 0 * ρ 1) ≤ T + C := by
      have h4 := (abs_le.1 h1).1
      rcases le_total 0 (Real.log (ρ 0 * ρ 1)) with h | h
      · nlinarith
      · linarith
    have hstep : ∀ i j : Fin (2 + 2), (j : ℕ) = i + 1 → Real.log (ρ j) ≤ Real.log (ρ i) + s := by
      intro i j hij
      have h := Real.log_le_log (mul_pos hred.pos (hρ j)) (hF i j hij)
      rw [Real.log_mul hred.pos.ne' (hρ j).ne'] at h
      linarith [neg_abs_le (Real.log t)]
    rw [Real.log_mul (mul_pos (hρ 0) (hρ 1)).ne' (mul_pos (hρ 2) (hρ 3)).ne', Real.log_mul (hρ 0).ne' (hρ 1).ne',
      Real.log_mul (hρ 2).ne' (hρ 3).ne'] at h2
    rw [Real.log_mul (hρ 0).ne' (hρ 1).ne'] at hL
    have hR := omBd_real (fun i => Real.log (ρ i)) s C T hs hC0 hT (hstep 0 1 rfl) (hstep 1 2 rfl) (hstep 2 3 rfl) hL
      (abs_le.1 h2).1
    have h5 := h3 (Real.exp (4 * T + 20 * (C + s))) (Real.one_le_exp (by positivity)) fun i j => by
      rw [← Real.exp_log (div_pos (hρ i) (hρ j)), Real.log_div (hρ i).ne' (hρ j).ne']
      exact Real.exp_le_exp.2 (hR i j)
    have h6 : qht x ≤ AutomorphicForm.height ((γ * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) :=
      ciInf_le (f := fun δ : Gam K (2 + 2) =>
        AutomorphicForm.height (((δ : G1 K (2 + 2)) * x : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)))
        ⟨0, by rintro _ ⟨δ, rfl⟩; exact (height_pos _).le⟩ ⟨γ, hγ⟩
    have h7 : C * Real.exp (4 * T + 20 * (C + s)) ^ c = A * Real.exp (((4 * c : ℕ) : ℝ) * T) := by
      rw [hA, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring
    refine h6.trans (h5.trans ?_)
    rw [h7]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _)) (Real.exp_pos _).le
  · unfold Om at hom
    push Not at hom
    obtain ⟨q, hq'⟩ := hom
    have h1 := hq (qx q x)
    have h2 : qht (qx q x) = qht x := hqinv _ (q.out : Gam K (2 + 2)).2 x
    rw [h2] at h1
    rw [← Real.le_log_iff_exp_le (zero_lt_one.trans_le (hq1 x))]
    have h3 : (T - C') / c' ≤ Real.log (qht x) := by
      rw [div_le_iff₀ hc']
      linarith
    rw [sub_div, div_eq_inv_mul T] at h3
    linarith [le_abs_self (C' / c')]
