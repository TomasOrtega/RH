import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
import ReciprocityTheory.ThetaQuasiPeriods.Change
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

open Complex Matrix
open scoped Real

noncomputable section

namespace GlobalTheory.RiemannThetaModel

variable {ι : Type*} [Fintype ι]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem riemannThetaTerm_eq_thetaTerm (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) (n : ι → ℤ) :
    riemannThetaTerm a b Ω v n = ReciprocityTheory.PTheta.thetaTerm a b v Ω n := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem riemannTheta_eq_theta (a b : ι → ℝ) (Ω : Matrix ι ι ℂ) (v : ι → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.PTheta.theta a b v Ω := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩`.
-/
theorem isSiegel_iff_mem_siegelH {Ω : Matrix ι ι ℂ} :
    IsSiegel Ω ↔ Ω ∈ ReciprocityTheory.PTheta.SiegelH ι :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/- English proof (translation)
The claim follows from `Set.ext fun _ => mem_siegelUpperHalfSpace.trans isSiegel_iff_mem_siegelH`.
-/
theorem siegelUpperHalfSpace_eq_siegelH :
    siegelUpperHalfSpace ι = ReciprocityTheory.PTheta.SiegelH ι :=
  Set.ext fun _ => mem_siegelUpperHalfSpace.trans isSiegel_iff_mem_siegelH

/- English proof (translation)
Rewrite using `[isSiegel_unique_iff]`. Simplify using the standard rewrite rules.
-/
theorem not_isSiegel_neg_I : ¬ IsSiegel !![-I] := by
  rw [isSiegel_unique_iff]
  simp

/- English proof (translation)
Introduce `h`. Use `h.dotProduct_pos (x := ![1, -1]) (by` as an intermediate fact. Introduce `e`. Simplify using `using congrFun e 0)`. Simplify using `[dotProduct, mulVec, Fin.sum_univ_two] at this`.
-/
theorem not_isSiegel_indefinite : ¬ IsSiegel !![I, 2 * I; 2 * I, I] := by
  intro h
  have := h.dotProduct_pos (x := ![1, -1]) (by
    intro e
    simpa using congrFun e 0)
  simp [dotProduct, mulVec, Fin.sum_univ_two] at this

/- English proof (translation)
Introduce `h`. Simplify using `using h.isSymm.apply 0 1`.
-/
theorem not_isSiegel_nonsymm : ¬ IsSiegel !![I, 1; 0, I] := by
  intro h
  simpa using h.isSymm.apply 0 1

/- English proof (translation)
Establish `hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Both sides reduce to the same expression.

Establish `h0 : riemannTheta (fun _ : Fin 1 => ((1 : ℤ) : ℝ) / 2) (fun _ => ((1 : ℤ) : ℝ) / 2) !![τ] 0 = 0`. Use `riemannTheta_half_neg (fun _ : Fin 1 => 1) (fun _ => 1) !![τ] 0` as an intermediate fact. Simplify using `only [neg_zero, dotProduct, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul, zpow_one] at this`. Take the linear combination `this / 2`. Rewrite `h0` using `[riemannTheta_eq_cexp_mul_zero_zero hs, mul_eq_zero]`.

Break down `h0 with h0 | h0` into its components or cases. Conclude with `absurd h0 (Complex.exp_ne_zero _)`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Simplify using `[dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem riemannTheta_zero_zero_half_period (τ : ℂ) :
    riemannTheta 0 0 !![τ] ![(1 + τ) / 2] = 0 := by
  have hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have h0 : riemannTheta (fun _ : Fin 1 => ((1 : ℤ) : ℝ) / 2) (fun _ => ((1 : ℤ) : ℝ) / 2)
      !![τ] 0 = 0 := by
    have := riemannTheta_half_neg (fun _ : Fin 1 => 1) (fun _ => 1) !![τ] 0
    simp only [neg_zero, dotProduct, mul_one, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, one_smul, zpow_one] at this
    linear_combination this / 2
  rw [riemannTheta_eq_cexp_mul_zero_zero hs, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Complex.exp_ne_zero _)
  · convert h0 using 2
    funext i
    fin_cases i
    simp [dotProduct]
    ring

/- English proof (translation)
Establish `hs` using `(isSiegel_I_smul_one (ι := ι)).hasSum_riemannTheta 0 0 0`. Establish `hr` using `Complex.hasSum_re hs`. Establish `ht (n : ι → ℤ) : riemannThetaTerm (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0 n = (Real.exp (-π * ∑ i, (n i : ℝ) ^ 2) : ℝ)`. Rewrite using `[riemannThetaTerm_zero_zero, Complex.ofReal_exp]`. Use `congr 1`.

Simplify using `only [smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_zero, smul_eq_mul]`. Simplify using `only [dotProduct]`. Use `push_cast`. Simplify using `only [sq]`. Take the linear combination `(π * ∑ i, (n i : ℂ) * n i) * I_mul_I`.

Use `le_hasSum hr 0 (fun n _ => by rw [ht, ofReal_re]; exact (Real.exp_pos _).le)` as an intermediate fact. Rewrite `this` using `[ht]`. Simplify using `using this`.
-/
theorem one_le_re_riemannTheta_I_smul_one [DecidableEq ι] :
    1 ≤ (riemannTheta (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0).re := by
  have hs := (isSiegel_I_smul_one (ι := ι)).hasSum_riemannTheta 0 0 0
  have hr := Complex.hasSum_re hs
  have ht (n : ι → ℤ) : riemannThetaTerm (0 : ι → ℝ) 0 (I • (1 : Matrix ι ι ℂ)) 0 n =
      (Real.exp (-π * ∑ i, (n i : ℝ) ^ 2) : ℝ) := by
    rw [riemannThetaTerm_zero_zero, Complex.ofReal_exp]
    congr 1
    simp only [smul_mulVec, one_mulVec, dotProduct_smul, dotProduct_zero, smul_eq_mul]
    simp only [dotProduct]
    push_cast
    simp only [sq]
    linear_combination (π * ∑ i, (n i : ℂ) * n i) * I_mul_I
  have := le_hasSum hr 0 (fun n _ => by rw [ht, ofReal_re]; exact (Real.exp_pos _).le)
  rw [ht] at this
  simpa using this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `∑' n, riemannThetaTerm a b Ω v n = _`. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 + (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) = _`. Use `congr 1`.

Establish `e1 : ((fun i => (n i : ℂ)) + fun i => (a i : ℂ)) = fun i => (n i : ℂ) + a i` using `rfl`. Establish `e2 : (v + fun i => (b i : ℂ)) = fun i => v i + b i` using `rfl`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem riemannTheta_eq_thetaChar {g : ℕ} (a b : Fin g → ℝ) (Ω : Matrix (Fin g) (Fin g) ℂ)
    (v : Fin g → ℂ) :
    riemannTheta a b Ω v = ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar Ω (fun i => a i) (fun i => b i) v := by
  change ∑' n, riemannThetaTerm a b Ω v n = _
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.thetaChar
  refine tsum_congr fun n => ?_
  change cexp (2 * π * I * (((fun i => (n i : ℂ) + a i) ⬝ᵥ (Ω *ᵥ fun i => (n i : ℂ) + a i)) / 2 +
    (fun i => (n i : ℂ) + a i) ⬝ᵥ fun i => v i + b i)) = _
  congr 1
  have e1 : ((fun i => (n i : ℂ)) + fun i => (a i : ℂ)) = fun i => (n i : ℂ) + a i := rfl
  have e2 : (v + fun i => (b i : ℂ)) = fun i => v i + b i := rfl
  rw [e1, e2]
  ring

/- English proof (translation)
Rewrite using `[riemannTheta_fin_one, jacobiTheta₂_undef]`. Simplify using the standard rewrite rules.
-/
theorem riemannTheta_zero_matrix : riemannTheta 0 0 !![(0 : ℂ)] ![0] = 0 := by
  rw [riemannTheta_fin_one, jacobiTheta₂_undef]
  simp

/- English proof (translation)
Introduce `ι _ a b z τ hτ`. Take `⟨c, hc, hY⟩` from `posDef_exists_mul_dotProduct_le hτ`. Establish `hY' (x : ι → ℝ) : c / 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x)`. Use `hY x` as an intermediate fact. Rewrite `this` using `[add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_comm x (x ᵥ* _), ← dotProduct_mulVec]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(summable_riemannThetaBound a (half_pos hc) ‖z‖).of_nonneg_of_le (fun _ => norm_nonneg _) (norm_riemannThetaTerm_le a b hY' (abs_im_apply_le_norm z))`.
-/
theorem thetaSummable : ReciprocityTheory.PTheta.ThetaSummableStatement := by
  intro ι _ a b z τ hτ
  obtain ⟨c, hc, hY⟩ := posDef_exists_mul_dotProduct_le hτ
  have hY' (x : ι → ℝ) : c / 2 * (x ⬝ᵥ x) ≤ x ⬝ᵥ (τ.map Complex.im *ᵥ x) := by
    have := hY x
    rw [add_mulVec, dotProduct_add, mulVec_transpose, dotProduct_comm x (x ᵥ* _),
      ← dotProduct_mulVec] at this
    linarith
  exact (summable_riemannThetaBound a (half_pos hc) ‖z‖).of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_riemannThetaTerm_le a b hY' (abs_im_apply_le_norm z))

/- English proof (translation)
Rewrite using `[riemannTheta_zero_zero_half_period]`. Establish `h` using `one_le_re_riemannTheta_I_smul_one (ι := Fin 1)`. Establish `e : (I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = !![I]`. Use extensionality with `i j`. Use `fin_cases i`.

Use `fin_cases j`. Simplify using the standard rewrite rules. Rewrite `h` using `[e]`. Introduce `h0`. Rewrite `h` using `[← h0]`.

Evaluate the numerical expressions using `at h`.
-/
theorem riemannTheta_not_constant :
    riemannTheta 0 0 !![I] ![(1 + I) / 2] ≠ riemannTheta 0 0 !![I] 0 := by
  rw [riemannTheta_zero_zero_half_period]
  have h := one_le_re_riemannTheta_I_smul_one (ι := Fin 1)
  have e : (I • (1 : Matrix (Fin 1) (Fin 1) ℂ)) = !![I] := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [e] at h
  intro h0
  rw [← h0] at h
  norm_num at h

/- English proof (translation)
Establish `hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm`. Use extensionality with `i j`. Use `fin_cases i`. Use `fin_cases j`. Both sides reduce to the same expression.

Use `riemannTheta_add_mulVec_intCast hs (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) ![z] (fun _ => 1)` as an intermediate fact. Establish `e : (![z] + !![τ] *ᵥ fun _ => ((1 : ℤ) : ℂ)) = ![z + τ]`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Simplify using `[mulVec, dotProduct]`.

Rewrite using `[← e, this]`. Use `congr 1`. Establish `: ((-1 : ℂ)) ^ β = cexp ((β : ℂ) * -(π * I))`. Rewrite using `[Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]`. Simplify using the standard rewrite rules.

Rewrite using `[this, ← Complex.exp_add]`. Use `congr 1`. Simplify using `[mulVec, dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem riemannTheta_half_add_tau (α β : ℤ) (z τ : ℂ) :
    riemannTheta (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) !![τ] ![z + τ] =
      (-1) ^ β * cexp (-π * I * τ - 2 * π * I * z) *
        riemannTheta (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) !![τ] ![z] := by
  have hs : (!![τ] : Matrix (Fin 1) (Fin 1) ℂ).IsSymm := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  have := riemannTheta_add_mulVec_intCast hs (fun _ => (α : ℝ) / 2) (fun _ => (β : ℝ) / 2) ![z]
    (fun _ => 1)
  have e : (![z] + !![τ] *ᵥ fun _ => ((1 : ℤ) : ℂ)) = ![z + τ] := by
    funext i
    fin_cases i
    simp [mulVec, dotProduct]
  rw [← e, this]
  congr 1
  have : ((-1 : ℂ)) ^ β = cexp ((β : ℂ) * -(π * I)) := by
    rw [Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
    simp
  rw [this, ← Complex.exp_add]
  congr 1
  simp [mulVec, dotProduct]
  ring

/- English proof (translation)
Rewrite using `[riemannTheta_add_mulVec_ofReal h, norm_mul, Complex.norm_exp, ← riemannTheta_add_ofReal, zero_add]`. Use `congr 2`. Simplify using `[dotProduct, mulVec, Finset.mul_sum _ _ (y _ : ℂ), Finset.mul_sum _ _ (y _ : ℝ)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_riemannTheta_real_coords {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm) (a b x y : ι → ℝ) :
    ‖riemannTheta a b Ω ((fun i => (x i : ℂ)) + Ω *ᵥ fun i => (y i : ℂ))‖ =
      Real.exp (π * (y ⬝ᵥ (Ω.map Complex.im *ᵥ y))) * ‖riemannTheta (a + y) (b + x) Ω 0‖ := by
  rw [riemannTheta_add_mulVec_ofReal h, norm_mul, Complex.norm_exp,
    ← riemannTheta_add_ofReal, zero_add]
  congr 2
  simp [dotProduct, mulVec, Finset.mul_sum _ _ (y _ : ℂ), Finset.mul_sum _ _ (y _ : ℝ)]
  ring

/- English proof (translation)
Establish `key (t r : ℝ) : (Real.exp (π * t) * r) ^ 2 * Real.exp (-2 * π * t) = r ^ 2`. Rewrite using `[mul_pow, mul_right_comm, sq, ← Real.exp_add, ← Real.exp_add]`. Simplify using `only [show π * t + π * t + -2 * π * t = 0 by ring, Real.exp_zero, one_mul]`. Rewrite using `[norm_riemannTheta_real_coords h, norm_riemannTheta_real_coords h, key, key, ← add_assoc, ← add_assoc, riemannTheta_char_add_intCast_left, riemannTheta_char_add_intCast_right, norm_mul, Complex.norm_exp]`. Simplify using `[dotProduct]`.
-/
theorem norm_sq_riemannTheta_mul_exp_periodic {Ω : Matrix ι ι ℂ} (h : Ω.IsSymm)
    (a b x y : ι → ℝ) (m k : ι → ℤ) :
    ‖riemannTheta a b Ω ((fun i => ((x + fun i => (m i : ℝ)) i : ℂ)) +
        Ω *ᵥ fun i => ((y + fun i => (k i : ℝ)) i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * ((y + fun i => (k i : ℝ)) ⬝ᵥ
        (Ω.map Complex.im *ᵥ (y + fun i => (k i : ℝ))))) =
    ‖riemannTheta a b Ω ((fun i => (x i : ℂ)) + Ω *ᵥ fun i => (y i : ℂ))‖ ^ 2 *
      Real.exp (-2 * π * (y ⬝ᵥ (Ω.map Complex.im *ᵥ y))) := by
  have key (t r : ℝ) : (Real.exp (π * t) * r) ^ 2 * Real.exp (-2 * π * t) = r ^ 2 := by
    rw [mul_pow, mul_right_comm, sq, ← Real.exp_add, ← Real.exp_add]
    simp only [show π * t + π * t + -2 * π * t = 0 by ring, Real.exp_zero, one_mul]
  rw [norm_riemannTheta_real_coords h, norm_riemannTheta_real_coords h, key, key, ← add_assoc,
    ← add_assoc, riemannTheta_char_add_intCast_left, riemannTheta_char_add_intCast_right,
    norm_mul, Complex.norm_exp]
  simp [dotProduct]

/- English proof (translation)
Establish `: (0 : Matrix ℕ ℕ ℂ) = diagonal fun _ => 0` using `by simp`. Rewrite using `[this, isSiegel_diagonal_iff]`. Simplify using the standard rewrite rules.
-/
theorem not_isSiegel_zero_nat : ¬ IsSiegel (0 : Matrix ℕ ℕ ℂ) := by
  have : (0 : Matrix ℕ ℕ ℂ) = diagonal fun _ => 0 := by simp
  rw [this, isSiegel_diagonal_iff]
  simp

end GlobalTheory.RiemannThetaModel
