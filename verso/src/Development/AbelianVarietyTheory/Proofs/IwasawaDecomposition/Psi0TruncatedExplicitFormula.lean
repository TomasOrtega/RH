import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrderStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetryStatement
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ExplUsed

/- English proof (translation)
Unfold `zsumR`. Use `finsum_nonneg fun ρ => finsum_nonneg fun _ => ?_` and prove the remaining obligations. Check the signs of the components of the expression.
-/
theorem zsumR_inv_norm_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  unfold zsumR
  refine finsum_nonneg fun ρ => finsum_nonneg fun _ => ?_
  positivity

/- English proof (translation)
Unfold `zsum`. Use `symm`. Use `finsum_mem_eq_of_bijOn (fun ρ => 1 - ρ) ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce and unpack `ρ ⟨h0, h1, h2, h3⟩`. Use `⟨by simp; linarith, by simp; linarith, by simpa using h2, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).1.1 h3`. Introduce `a _ b _ h`. Simplify using `using h`. Introduce and unpack `ρ ⟨h0, h1, h2, h3⟩`. Establish `a0 : 0 < (1 - ρ).re` using `by simp; linarith`.

Establish `a1 : (1 - ρ).re < 1` using `by simp; linarith`. Use `⟨1 - ρ, ⟨a0, a1, by simpa using h2, ?_⟩, by simp⟩` and prove the remaining obligations. Apply the tactic sequence `exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ _ a0 a1).1.2 (by simpa using h3)`. Introduce and unpack `ρ ⟨h0, h1, h2, h3⟩`. Apply the tactic sequence `rw [(GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).2]`.

Simplify using the standard rewrite rules.
-/
theorem zsum_inv_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    zsum χ⁻¹ 0 1 (fun ρ => 1 / (1 - ρ)) = zsum χ 0 1 (fun ρ => 1 / ρ) := by
  unfold zsum
  symm
  refine finsum_mem_eq_of_bijOn (fun ρ => 1 - ρ) ⟨?_, ?_, ?_⟩ ?_
  · rintro ρ ⟨h0, h1, h2, h3⟩
    refine ⟨by simp; linarith, by simp; linarith, by simpa using h2, ?_⟩
    exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).1.1 h3
  · intro a _ b _ h
    simpa using h
  · rintro ρ ⟨h0, h1, h2, h3⟩
    have a0 : 0 < (1 - ρ).re := by simp; linarith
    have a1 : (1 - ρ).re < 1 := by simp; linarith
    refine ⟨1 - ρ, ⟨a0, a1, by simpa using h2, ?_⟩, by simp⟩
    exact (GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ _ a0 a1).1.2 (by simpa using h3)
  · rintro ρ ⟨h0, h1, h2, h3⟩
    rw [(GlobalTheory.T.dirichlet_L_zero_symmetry q χ hχ ρ h0 h1).2]
    simp

/- English proof (translation)
Unfold `zsum zsumR`. Establish `hf` using `(GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 1).1`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem norm_zsum_inv_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖zsum χ 0 1 (fun ρ => 1 / ρ)‖ ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
  unfold zsum zsumR
  have hf := (GlobalTheory.T.dirichletLZerosInWindow_finite_and_pos_order q χ 0 1).1
  rw [finsum_mem_eq_finite_toFinset_sum _ hf, finsum_mem_eq_finite_toFinset_sum _ hf]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp

/- English proof (translation)
Establish `h3` using `Real.pi_gt_three`. Establish `h4` using `Real.pi_le_four`. Use `⟨Real.log_nonneg (by linarith), ?_⟩` and prove the remaining obligations. Use `Real.log_le_sub_one_of_pos (x := 2 * Real.pi) (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_two_pi_bounds : 0 ≤ Real.log (2 * Real.pi) ∧ Real.log (2 * Real.pi) ≤ 7 := by
  have h3 := Real.pi_gt_three
  have h4 := Real.pi_le_four
  refine ⟨Real.log_nonneg (by linarith), ?_⟩
  have := Real.log_le_sub_one_of_pos (x := 2 * Real.pi) (by linarith)
  linarith

/- English proof (translation)
Establish `h1` using `Real.log_le_log (by norm_num) hu`. Establish `h2` using `Real.log_two_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_le_log {u : ℝ} (hu : 2 ≤ u) : 1 / 2 ≤ Real.log u := by
  have h1 := Real.log_le_log (by norm_num) hu
  have h2 := Real.log_two_gt_d9
  linarith

/- English proof (translation)
The claim follows from `|Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2| ≤ 16 * Real.log u := by have h1 := log_two_pi_bounds have h2 := half_le_log hu have h3 : 1 / u ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by nlinarith) have h4 : 0 < 1 / u ^ 2 := by positivity have h5 : Real.log …`.
-/
theorem zeta_const_bound {u : ℝ} (hu : 2 ≤ u) :
    |Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2| ≤ 16 * Real.log u := by
  have h1 := log_two_pi_bounds
  have h2 := half_le_log hu
  have h3 : 1 / u ^ 2 ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  have h4 : 0 < 1 / u ^ 2 := by positivity
  have h5 : Real.log (1 - 1 / u ^ 2) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have h6 : Real.log (1 / 2) ≤ Real.log (1 - 1 / u ^ 2) := Real.log_le_log (by norm_num) (by linarith)
  have h7 : Real.log (1 / 2) = - Real.log 2 := by rw [one_div, Real.log_inv]
  have h8 := Real.log_two_lt_d9
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

/- English proof (translation)
Introduce and unpack `⟨C₁, h₁⟩ ⟨C₂, h₂⟩ ⟨C₃, h₃⟩`. Use `⟨|C₁| + |C₂| + 4 * |C₃| + 20, fun q _ χ hχ u T hT hTu => ?_⟩` and prove the remaining obligations. Establish `hu : 2 ≤ u` using `hT.trans hTu`. Establish `hL` using `half_le_log hu`. Establish `hS` using `zsumR_inv_norm_nonneg χ`.

Establish `hq0 : 0 < q` using `Nat.pos_of_ne_zero (NeZero.ne q)`. Establish `hq1 : (1 : ℝ) ≤ q` using `by exact_mod_cast hq0`. Establish `hlq : 0 ≤ Real.log q` using `Real.log_nonneg hq1`. Establish `hqu : Real.log (q * u) = Real.log q + Real.log u` using `Real.log_mul (by positivity) (by positivity)`. Establish `hE : u * Real.log (q * u * T) ^ 2 / T = u / T * Real.log (q * u * T) ^ 2` using `by ring`.

Establish `hE0 : 0 ≤ u / T * Real.log (q * u * T) ^ 2` using `by positivity`. Establish `a1` using `abs_nonneg C₁`. Establish `a2` using `abs_nonneg C₂`. Establish `a3` using `abs_nonneg C₃`. Rewrite using `[hE, hqu]`.

Break down `Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hq0) with hq | hq` into its components or cases. Establish `hq' : q = 1` using `hq.symm`. Substitute `hq'` using the available equality. Establish `hχ1 : χ = 1` using `DirichletCharacter.level_one χ`. Substitute `hχ1` using the available equality.

Establish `h` using `h₁ u T hu hT`. Establish `hA` using `zeta_const_bound hu`. Simplify using `only [Nat.cast_one, one_mul, Real.log_one, zero_add] at hE0 ⊢`. Use `set E := u / T * Real.log (u * T) ^ 2`. Use `set S := zsumR (1 : DirichletCharacter ℂ 1) 0 1 (fun ρ => 1 / ‖ρ‖)`.

Use `set A := Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2`. Use `set Z := zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)`. Establish `e : GlobalTheoryTheory.psi0 (1 : DirichletCharacter ℂ 1) u + Z = (psiChi (1 : DirichletCharacter ℂ 1) u - (u : ℂ) + Z + (A : ℂ)) - (A : ℂ)`. Simplify using `only [GlobalTheoryTheory.psi0, psiChi, if_true]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_real, Real.norm_eq_abs]`. Establish `h' : C₁ * (Real.log u + E) ≤ |C₁| * (Real.log u + E)` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)`. Establish `hL0 : 0 ≤ Real.log u` using `by linarith`.

Use polynomial arithmetic with `[mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a2 hE0, mul_nonneg a3 hE0, mul_nonneg a2 hL0, mul_nonneg a3 hL0]`. Establish `hq' : 1 < q` using `hq`. Establish `hne : χ ≠ 1`. Introduce and unpack `rfl`. Use `hχ` as an intermediate fact.

Rewrite `this` using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one]`. Use linear arithmetic over natural numbers and integers. Establish `hχ' : χ⁻¹.IsPrimitive`. Rewrite using `[DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]`. Conclude with `hχ`.

Establish `h` using `h₂ q χ hq' hχ u T hu hT`. Establish `g` using `h₃ q χ⁻¹ hq' hχ'`. Rewrite `g` using `[zsum_inv_eq χ hχ]`. Establish `gz` using `norm_zsum_inv_le χ`. Use `set E := u / T * Real.log (q * u * T) ^ 2`.

Use `set S := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)`. Use `set Z := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)`. Use `set Y := zsum χ 0 1 (fun ρ => 1 / ρ)`. Use `set D := deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1`. Use `set a : ℂ := ((Real.log (u - 1) / 2 : ℝ) : ℂ) with ha`.

Use `set b : ℂ := χ (-1) / 2 * ((Real.log (u + 1) : ℝ) : ℂ) with hb`. Use `set c : ℂ := ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) with hc`. Establish `hL0 : 0 ≤ Real.log u` using `by linarith`. Establish `na : ‖a‖ ≤ Real.log u`. Rewrite using `[ha, Complex.norm_real, Real.norm_eq_abs, abs_le]`.

Establish `b1 : 0 ≤ Real.log (u - 1)` using `Real.log_nonneg (by linarith)`. Establish `b2 : Real.log (u - 1) ≤ Real.log u` using `Real.log_le_log (by linarith) (by linarith)`. Apply the tactic sequence `constructor <;> linarith`. Establish `nb : ‖b‖ ≤ Real.log u`. Establish `b1 : 0 ≤ Real.log (u + 1)` using `Real.log_nonneg (by linarith)`.

Establish `b2 : Real.log (u + 1) ≤ Real.log (u ^ 2)` using `Real.log_le_log (by linarith) (by nlinarith)`. Rewrite `b2` using `[Real.log_pow]`. Establish `b3` using `χ.norm_le_one (-1)`. Rewrite using `[hb, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b1]`. Simplify using `only [Complex.norm_ofNat]`.

Move the coercions through the operations in `at b2`. Use the polynomial consequences of the given equalities and inequalities. Establish `nc : ‖c‖ ≤ Real.log q + 16 * Real.log u`. Establish `b1` using `log_two_pi_bounds`. Establish `b2` using `Real.one_half_lt_eulerMascheroniConstant`.

Establish `b3` using `Real.eulerMascheroniConstant_lt_two_thirds`. Rewrite using `[hc, Complex.norm_real, Real.norm_eq_abs, abs_le, Real.log_div (by positivity) (by positivity)]`. Apply the tactic sequence `constructor <;> linarith [b1.1, b1.2]`. Establish `n3 : Real.log (3 * q) ≤ 4 * (Real.log q + Real.log u)`. Rewrite using `[Real.log_mul (by positivity) (by positivity)]`.

Use `Real.log_le_sub_one_of_pos (x := 3) (by norm_num)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `n30 : 0 ≤ Real.log (3 * q)` using `Real.log_nonneg (by linarith)`. Establish `g' : ‖D - Y‖ ≤ |C₃| * (4 * (Real.log q + Real.log u))` using `g.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) n30).trans (mul_le_mul_of_nonneg_left n3 a3))`. Establish `h' : C₂ * (Real.log u + E) ≤ |C₂| * (Real.log u + E)` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)`.

Establish `e : GlobalTheoryTheory.psi0 χ u + Z = (psiChi χ u + Z + a + b - (D + c)) - a - b + (D - Y) + Y + c`. Simplify using `only [GlobalTheoryTheory.psi0, psiChi, if_neg hne]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `t : ∀ w : ℂ, ‖w - a - b + (D - Y) + Y + c‖ ≤ ‖w‖ + ‖a‖ + ‖b‖ + ‖D - Y‖ + ‖Y‖ + ‖c‖`.

Introduce `w`. Establish `t1` using `norm_add_le (w - a - b + (D - Y) + Y) c`. Establish `t2` using `norm_add_le (w - a - b + (D - Y)) Y`. Establish `t3` using `norm_add_le (w - a - b) (D - Y)`. Establish `t4` using `norm_sub_le (w - a) b`.

Establish `t5` using `norm_sub_le w a`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(t _).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a1 hE0, mul_nonneg a3 hE0, mul_nonneg a1 hL0, mul_nonneg a1 hlq, mul_nonneg a2 hlq]`.
-/
theorem explicit_formula_used : GlobalTheory.Mem.An.ExplZeta → GlobalTheory.Mem.An.ExplChi → GlobalTheory.Mem.An.LogDerOne → ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (q * u * T) ^ 2 / T + Real.log (q * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) := by
  rintro ⟨C₁, h₁⟩ ⟨C₂, h₂⟩ ⟨C₃, h₃⟩
  refine ⟨|C₁| + |C₂| + 4 * |C₃| + 20, fun q _ χ hχ u T hT hTu => ?_⟩
  have hu : 2 ≤ u := hT.trans hTu
  have hL := half_le_log hu
  have hS := zsumR_inv_norm_nonneg χ
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hqu : Real.log (q * u) = Real.log q + Real.log u :=
    Real.log_mul (by positivity) (by positivity)
  have hE : u * Real.log (q * u * T) ^ 2 / T = u / T * Real.log (q * u * T) ^ 2 := by ring
  have hE0 : 0 ≤ u / T * Real.log (q * u * T) ^ 2 := by positivity
  have a1 := abs_nonneg C₁
  have a2 := abs_nonneg C₂
  have a3 := abs_nonneg C₃
  rw [hE, hqu]
  rcases Nat.eq_or_lt_of_le (Nat.succ_le_of_lt hq0) with hq | hq
  · have hq' : q = 1 := hq.symm
    subst hq'
    have hχ1 : χ = 1 := DirichletCharacter.level_one χ
    subst hχ1
    have h := h₁ u T hu hT
    have hA := zeta_const_bound hu
    simp only [Nat.cast_one, one_mul, Real.log_one, zero_add] at hE0 ⊢
    set E := u / T * Real.log (u * T) ^ 2
    set S := zsumR (1 : DirichletCharacter ℂ 1) 0 1 (fun ρ => 1 / ‖ρ‖)
    set A := Real.log (2 * Real.pi) + Real.log (1 - 1 / u ^ 2) / 2
    set Z := zsum (1 : DirichletCharacter ℂ 1) 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
    have e : GlobalTheoryTheory.psi0 (1 : DirichletCharacter ℂ 1) u + Z =
        (psiChi (1 : DirichletCharacter ℂ 1) u - (u : ℂ) + Z + (A : ℂ)) - (A : ℂ) := by
      simp only [GlobalTheoryTheory.psi0, psiChi, if_true]
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h' : C₁ * (Real.log u + E) ≤ |C₁| * (Real.log u + E) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have hL0 : 0 ≤ Real.log u := by linarith
    nlinarith [mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a2 hE0, mul_nonneg a3 hE0,
      mul_nonneg a2 hL0, mul_nonneg a3 hL0]
  · have hq' : 1 < q := hq
    have hne : χ ≠ 1 := by
      rintro rfl
      have := hχ
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at this
      omega
    have hχ' : χ⁻¹.IsPrimitive := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hχ
    have h := h₂ q χ hq' hχ u T hu hT
    have g := h₃ q χ⁻¹ hq' hχ'
    rw [zsum_inv_eq χ hχ] at g
    have gz := norm_zsum_inv_le χ
    set E := u / T * Real.log (q * u * T) ^ 2
    set S := zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
    set Z := zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)
    set Y := zsum χ 0 1 (fun ρ => 1 / ρ)
    set D := deriv (DirichletCharacter.LFunction χ⁻¹) 1 / DirichletCharacter.LFunction χ⁻¹ 1
    set a : ℂ := ((Real.log (u - 1) / 2 : ℝ) : ℂ) with ha
    set b : ℂ := χ (-1) / 2 * ((Real.log (u + 1) : ℝ) : ℂ) with hb
    set c : ℂ := ((Real.log (q / (2 * Real.pi)) - Real.eulerMascheroniConstant : ℝ) : ℂ) with hc
    have hL0 : 0 ≤ Real.log u := by linarith
    have na : ‖a‖ ≤ Real.log u := by
      rw [ha, Complex.norm_real, Real.norm_eq_abs, abs_le]
      have b1 : 0 ≤ Real.log (u - 1) := Real.log_nonneg (by linarith)
      have b2 : Real.log (u - 1) ≤ Real.log u := Real.log_le_log (by linarith) (by linarith)
      constructor <;> linarith
    have nb : ‖b‖ ≤ Real.log u := by
      have b1 : 0 ≤ Real.log (u + 1) := Real.log_nonneg (by linarith)
      have b2 : Real.log (u + 1) ≤ Real.log (u ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
      rw [Real.log_pow] at b2
      have b3 := χ.norm_le_one (-1)
      rw [hb, norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b1]
      simp only [Complex.norm_ofNat]
      push_cast at b2
      nlinarith
    have nc : ‖c‖ ≤ Real.log q + 16 * Real.log u := by
      have b1 := log_two_pi_bounds
      have b2 := Real.one_half_lt_eulerMascheroniConstant
      have b3 := Real.eulerMascheroniConstant_lt_two_thirds
      rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_le,
        Real.log_div (by positivity) (by positivity)]
      constructor <;> linarith [b1.1, b1.2]
    have n3 : Real.log (3 * q) ≤ 4 * (Real.log q + Real.log u) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (x := 3) (by norm_num)
      linarith
    have n30 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
    have g' : ‖D - Y‖ ≤ |C₃| * (4 * (Real.log q + Real.log u)) :=
      g.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) n30).trans (mul_le_mul_of_nonneg_left n3 a3))
    have h' : C₂ * (Real.log u + E) ≤ |C₂| * (Real.log u + E) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e : GlobalTheoryTheory.psi0 χ u + Z =
        (psiChi χ u + Z + a + b - (D + c)) - a - b + (D - Y) + Y + c := by
      simp only [GlobalTheoryTheory.psi0, psiChi, if_neg hne]
      ring
    rw [e]
    have t : ∀ w : ℂ, ‖w - a - b + (D - Y) + Y + c‖ ≤ ‖w‖ + ‖a‖ + ‖b‖ + ‖D - Y‖ + ‖Y‖ + ‖c‖ := by
      intro w
      have t1 := norm_add_le (w - a - b + (D - Y) + Y) c
      have t2 := norm_add_le (w - a - b + (D - Y)) Y
      have t3 := norm_add_le (w - a - b) (D - Y)
      have t4 := norm_sub_le (w - a) b
      have t5 := norm_sub_le w a
      linarith
    refine (t _).trans ?_
    nlinarith [mul_nonneg a1 hS, mul_nonneg a2 hS, mul_nonneg a3 hS, mul_nonneg a1 hE0, mul_nonneg a3 hE0,
      mul_nonneg a1 hL0, mul_nonneg a1 hlq, mul_nonneg a2 hlq]

end GlobalTheory.Mem.An.ExplUsed
