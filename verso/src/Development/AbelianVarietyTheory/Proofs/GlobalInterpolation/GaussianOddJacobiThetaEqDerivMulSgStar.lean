import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex

noncomputable section

namespace GlobalTheory.SgStarOddTheta

open Formalism.L2.Th1.F

/- English proof (translation)
Rewrite using `[jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ), ← tsum_mul_left]`. Use `tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]`. Use `Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.coe_addRight]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jacobiTheta₂_add_int_lattice (z τ : ℂ) (m k : ℤ) :
    jacobiTheta₂ (z + (m * τ + k)) τ =
      cexp (-(Real.pi : ℂ) * I * (m ^ 2 * τ + 2 * m * z)) * jacobiTheta₂ z τ := by
  rw [jacobiTheta₂, jacobiTheta₂, ← (Equiv.addRight m).tsum_eq (fun n => jacobiTheta₂_term n z τ),
    ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term, jacobiTheta₂_term, ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨n * k, ?_⟩
  simp only [Equiv.coe_addRight]
  push_cast
  ring

/- English proof (translation)
Unfold `GlobalTheory.ThetaWeberRoad.oddTheta`. Rewrite using `[show z + (m * (τ : ℂ) + k) + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + (m * (τ : ℂ) + k) by ring, jacobiTheta₂_add_int_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddTheta_add (τ : UpperHalfPlane) (z : ℂ) (m k : ℤ) :
    GlobalTheory.ThetaWeberRoad.oddTheta τ (z + (m * (τ : ℂ) + k)) =
      cexp ((Real.pi : ℂ) * I * (k - m - m ^ 2 * (τ : ℂ) - 2 * m * z)) *
        GlobalTheory.ThetaWeberRoad.oddTheta τ z := by
  unfold GlobalTheory.ThetaWeberRoad.oddTheta
  rw [show z + (m * (τ : ℂ) + k) + ((τ : ℂ) + 1) / 2 = (z + ((τ : ℂ) + 1) / 2) + (m * (τ : ℂ) + k) by ring,
    jacobiTheta₂_add_int_lattice, ← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  ring

/- English proof (translation)
Rewrite using `[mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]`. Use `split_ifs with h`. Conclude with `h.neg_one_zpow`. Conclude with `(Int.not_even_iff_odd.1 h).neg_one_zpow`.
-/
theorem exp_pi_I_int (j : ℤ) : cexp ((Real.pi : ℂ) * I * j) = if Even j then 1 else -1 := by
  rw [mul_comm, Complex.exp_int_mul, Complex.exp_pi_mul_I]
  split_ifs with h
  · exact h.neg_one_zpow
  · exact (Int.not_even_iff_odd.1 h).neg_one_zpow

/- English proof (translation)
Simplify using `[area, GlobalTheory.periodPairOfTau, abs_of_pos τ.im_pos]`.
-/
theorem area_periodPairOfTau (τ : UpperHalfPlane) : area (GlobalTheory.periodPairOfTau τ) = τ.im := by
  simp [area, GlobalTheory.periodPairOfTau, abs_of_pos τ.im_pos]

/- English proof (translation)
Establish `hpar : Even (k - m + m * k) ↔ Even m ∧ Even k`. Simplify using `only [parity_simps]`. The claim follows by propositional logic. Establish `hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k`. Rewrite using `[GlobalTheory.mem_lattice_periodPairOfTau]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨p, q, e⟩`. Establish `e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ)`. Use `push_cast`. Take the linear combination `-2 * e`.

Establish `h1` using `congrArg Complex.im e1`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1`. Rewrite `e1` using `[h1, add_right_inj, Int.cast_inj]`. Conclude with `⟨⟨p, h1⟩, ⟨q, e1⟩⟩`. Introduce and unpack `⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩`.

Conclude with `⟨p, q, by push_cast; ring⟩`. Rewrite using `[exp_pi_I_int, semiChar]`. Distinguish the cases in `h : Even m ∧ Even k`. Rewrite using `[if_pos (hmem.2 h), if_pos (hpar.2 h)]`. Rewrite using `[if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]`.
-/
theorem semiChar_periodPairOfTau (τ : UpperHalfPlane) (m k : ℤ) :
    semiChar (GlobalTheory.periodPairOfTau τ) (m * (τ : ℂ) + k) =
      cexp ((Real.pi : ℂ) * I * ((k - m + m * k : ℤ) : ℂ)) := by
  have hpar : Even (k - m + m * k) ↔ Even m ∧ Even k := by
    simp only [parity_simps]; tauto
  have hmem : (m * (τ : ℂ) + k) / 2 ∈ (GlobalTheory.periodPairOfTau τ).lattice ↔ Even m ∧ Even k := by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    constructor
    · rintro ⟨p, q, e⟩
      have e1 : (m * (τ : ℂ) + k) = (p + p : ℤ) * (τ : ℂ) + (q + q : ℤ) := by
        push_cast
        linear_combination -2 * e
      have h1 := congrArg Complex.im e1
      simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, zero_mul,
        add_zero, UpperHalfPlane.coe_im, mul_left_inj' τ.im_ne_zero, Int.cast_inj] at h1
      rw [h1, add_right_inj, Int.cast_inj] at e1
      exact ⟨⟨p, h1⟩, ⟨q, e1⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, by push_cast; ring⟩
  rw [exp_pi_I_int, semiChar]
  by_cases h : Even m ∧ Even k
  · rw [if_pos (hmem.2 h), if_pos (hpar.2 h)]
  · rw [if_neg (fun h' => h (hmem.1 h')), if_neg (fun h' => h (hpar.1 h'))]

def expOddTheta (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z

/- English proof (translation)
Use `GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ` as an intermediate fact. Unfold `expOddTheta`. Use `fun_prop`.
-/
theorem differentiable_expOddTheta (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by
  have := GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ
  unfold expOddTheta
  fun_prop

/- English proof (translation)
Introduce `ω hω z`. Take `⟨m, k, rfl⟩` from `(GlobalTheory.mem_lattice_periodPairOfTau τ ω).1 hω`. Simplify using `only [one_mul]`. Rewrite using `[semiChar_periodPairOfTau, opU, herm, herm, area_periodPairOfTau, expOddTheta, expOddTheta, oddTheta_add]`. Establish `hE : ∀ A B C D w : ℂ, cexp A * (cexp B * (cexp C * w) * cexp D) = cexp (A + B + C + D) * w`.

Use `intros`. Simplify using `only [Complex.exp_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE]`. Use `congr 1`.

Use `Complex.exp_eq_exp_iff_exists_int.2 ⟨k - m + m * k, ?_⟩` and prove the remaining obligations. Establish `hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Expand and normalize the polynomial expressions, which then agree. Establish `hy : ((τ.im : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast τ.im_ne_zero`.

Simplify using `only [map_add, map_mul, map_intCast, hc]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expOddTheta_law (τ : UpperHalfPlane) : ∀ ω ∈ (GlobalTheory.periodPairOfTau τ).lattice, ∀ z,
    semiChar (GlobalTheory.periodPairOfTau τ) ω * opU (GlobalTheory.periodPairOfTau τ) ω (expOddTheta τ) z =
      expOddTheta τ z := by
  intro ω hω z
  obtain ⟨m, k, rfl⟩ := (GlobalTheory.mem_lattice_periodPairOfTau τ ω).1 hω
  simp only [one_mul]
  rw [semiChar_periodPairOfTau, opU, herm, herm, area_periodPairOfTau, expOddTheta, expOddTheta,
    oddTheta_add]
  have hE : ∀ A B C D w : ℂ, cexp A * (cexp B * (cexp C * w) * cexp D) = cexp (A + B + C + D) * w := by
    intros
    simp only [Complex.exp_add]
    ring
  rw [hE]
  congr 1
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨k - m + m * k, ?_⟩
  have hc : (starRingEnd ℂ) (τ : ℂ) = τ - 2 * τ.im * I := by
    apply Complex.ext <;> simp
    ring
  have hy : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_ne_zero
  simp only [map_add, map_mul, map_intCast, hc]
  field_simp
  push_cast
  ring

/- English proof (translation)
Introduce `hTL hSB τ z`. Take `⟨c, hc⟩` from `hTL _ (expOddTheta τ) (differentiable_expOddTheta τ) (expOddTheta_law τ)`. Establish `hfun : expOddTheta τ = fun z => c * sgStar (GlobalTheory.periodPairOfTau τ) z` using `funext hc`. Take `⟨hdiff, -, -, hd1, -⟩` from `hSB (GlobalTheory.periodPairOfTau τ)`. Establish `h1 : deriv (expOddTheta τ) 0 = c`.

Rewrite using `[hfun]`. Use `((hdiff 0).hasDerivAt.const_mul c).deriv` as an intermediate fact. Rewrite `this` using `[hd1, mul_one]`. Conclude with `this`. Establish `he : HasDerivAt (fun z : ℂ => cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ)))) 0 0`.

Use `(((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const (2 * ((τ.im : ℝ) : ℂ))).cexp` as an intermediate fact. Simplify using `using this`. Establish `h2 : deriv (expOddTheta τ) 0 = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0`. Use `(he.mul (GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ 0).hasDerivAt).deriv` as an intermediate fact. Simplify using `only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, Complex.exp_zero, one_mul] at this`.

Conclude with `this`. Use `hc z` as an intermediate fact. Rewrite `this` using `[expOddTheta]`. Rewrite using `[this, ← h1, h2]`.
-/
theorem exp_mul_oddTheta_eq_deriv_mul_sgStar :
    Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ),
      Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z =
        deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  intro hTL hSB τ z
  obtain ⟨c, hc⟩ := hTL _ (expOddTheta τ) (differentiable_expOddTheta τ) (expOddTheta_law τ)
  have hfun : expOddTheta τ = fun z => c * sgStar (GlobalTheory.periodPairOfTau τ) z := funext hc
  obtain ⟨hdiff, -, -, hd1, -⟩ := hSB (GlobalTheory.periodPairOfTau τ)
  have h1 : deriv (expOddTheta τ) 0 = c := by
    rw [hfun]
    have := ((hdiff 0).hasDerivAt.const_mul c).deriv
    rw [hd1, mul_one] at this
    exact this
  have he : HasDerivAt (fun z : ℂ => cexp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ)))) 0 0 := by
    have := (((hasDerivAt_pow 2 (0 : ℂ)).const_mul (Real.pi : ℂ)).div_const
      (2 * ((τ.im : ℝ) : ℂ))).cexp
    simpa using this
  have h2 : deriv (expOddTheta τ) 0 = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 := by
    have := (he.mul (GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ 0).hasDerivAt).deriv
    simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, Complex.exp_zero, one_mul] at this
    exact this
  have := hc z
  rw [expOddTheta] at this
  rw [this, ← h1, h2]

end GlobalTheory.SgStarOddTheta
