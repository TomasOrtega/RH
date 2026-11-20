import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DCalcB

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

namespace DCalcCH

open DCalcH DCalcBH

variable {m n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_one : mR (1 : GR n) = 1 := rfl

/- English proof (translation)
Unfold `cnt`. Rewrite using `[Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]`. Establish `h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1`. Apply the tactic sequence `intro a; cases ε a <;> simp`. Simplify using `[h]`.
-/
theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  unfold cnt
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h : ∀ a : Fin m, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a; cases ε a <;> simp
  simp [h]

/- English proof (translation)
Rewrite using `[det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]`.
-/
theorem det_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j))).det = Complex.exp (-(z * ∑ j, (X j : ℂ))) := by
  rw [det_diagonal, ← Complex.exp_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]

/- English proof (translation)
Unfold `aC`. Rewrite using `[det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.exp_add, add_neg_cancel, Complex.exp_zero]`.
-/
theorem det_aC (X : Fin n → ℝ) (z : ℂ) : (aC X z).det = 1 := by
  unfold aC
  rw [det_fromBlocks_zero₂₁, det_diagonal, det_diagonal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/- English proof (translation)
Rewrite using `[← Complex.exp_int_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zpow_exp_neg (w : ℂ) (p : ℕ) : Complex.exp (-w) ^ (-(p : ℤ)) = Complex.exp ((p : ℂ) * w) := by
  rw [← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Unfold `jC`. Simplify using `only [mR_one, Matrix.one_mul]`. Rewrite using `[det_aC]`. Unfold `aC`. Simplify using `only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]`.

Rewrite using `[det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jC_one (e : ℤ) (p q : ℕ) (X : Fin n → ℝ) (z : ℂ) :
    jC e p q 1 X z = Complex.exp (((p : ℂ) + q) * (z * ∑ j, (X j : ℂ))) := by
  unfold jC
  simp only [mR_one, Matrix.one_mul]
  rw [det_aC]
  unfold aC
  simp only [toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, _root_.one_zpow, one_mul]
  rw [det_diag_exp, zpow_exp_neg, zpow_exp_neg, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[diagonal_mul_diagonal]`. Use `conv_rhs => rw [← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Rewrite using `[← Complex.exp_add, add_neg_cancel, Complex.exp_zero]`.
-/
theorem inv_diag_exp (X : Fin n → ℝ) (z : ℂ) :
    (diagonal fun j => Complex.exp (-(z * X j)))⁻¹ = diagonal fun j => Complex.exp (z * X j) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [diagonal_mul_diagonal]
  conv_rhs => rw [← diagonal_one]
  congr 1
  funext j
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/- English proof (translation)
Unfold `ptZ`. Simplify using `only [mR_one, Matrix.one_mul]`. Unfold `aC`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.zero_mul, zero_add, add_zero]`. Rewrite using `[inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ptZ_one (X : Fin n → ℝ) (z s₀ : ℂ) :
    ptZ 1 X z s₀ = s₀ • diagonal fun j => Complex.exp (2 * z * X j) := by
  unfold ptZ
  simp only [mR_one, Matrix.one_mul]
  unfold aC
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.zero_mul, zero_add, add_zero]
  rw [inv_diag_exp, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, diagonal_mul_diagonal]
  congr 2
  funext j
  rw [← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Simplify using `[gramB, Qb, evX, map_sum, eval_X]`.
-/
theorem gramB_diag (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (j : Fin n) :
    gramB ε b u j j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a j) * u a j := by
  simp [gramB, Qb, evX, map_sum, eval_X]

/- English proof (translation)
Rewrite using `[Matrix.smul_mul, trace_smul, smul_eq_mul]`. Use `congr 1`. Simplify using `[trace, diagonal_mul]`.
-/
theorem trace_sdiag (s₀ : ℂ) (w : Fin n → ℂ) (G : Matrix (Fin n) (Fin n) ℂ) :
    ((s₀ • diagonal w) * G).trace = s₀ * ∑ j, w j * G j j := by
  rw [Matrix.smul_mul, trace_smul, smul_eq_mul]
  congr 1
  simp [trace, diagonal_mul]

/- English proof (translation)
Unfold `famC fF fP`. Rewrite using `[jC_one, ptZ_one, ptZ_one, gs_vS]`. Unfold `gC`. Rewrite using `[trace_sdiag, trace_sdiag]`. Simplify using `only [gramB_diag, evX_eq, map_one, one_mul]`.

Establish `hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ)`. Rewrite using `[← Nat.cast_add, cnt_add]`. Rewrite using `[hpq, ← Complex.exp_add, Complex.ofReal_exp]`. Establish `hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) + (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) = ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)`. Introduce `j`.

Use `Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)` as an intermediate fact. Simplify using `only [Bool.not_eq_true] at this`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ)`. Introduce `j`. Use `push_cast`.

Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `nS`.

Use `push_cast`. Simplify using `only [e2]`. Establish `key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) - Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a ∈ Finset.univ.filter (fun a => epsT …`. Establish `hI : Complex.I * Complex.I = -1` using `Complex.I_mul_I`. Simplify using `only [← hsum, mul_add, Finset.sum_add_distrib]`.

Take the linear combination `((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j + (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI`. Rewrite using `[key, ← Complex.exp_add]`. Establish `hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j`. Introduce `E N`. Simplify using `only [Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _`. Use `congr 1`. Use `push_cast`. Rewrite using `[hswap]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem famC_one (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ) (u : Fin m → Fin n → ℂ) (s : ℝ) :
    famC ε t c e 1 X (s : ℂ) u = fF c X 1 u s := by
  unfold famC fF fP
  rw [jC_one, ptZ_one, ptZ_one, gs_vS]
  unfold gC
  rw [trace_sdiag, trace_sdiag]
  simp only [gramB_diag, evX_eq, map_one, one_mul]
  have hpq : ((cnt (epsT t ε) true : ℂ) + (cnt (epsT t ε) false : ℂ)) = (m : ℂ) := by
    rw [← Nat.cast_add, cnt_add]
  rw [hpq, ← Complex.exp_add, Complex.ofReal_exp]
  have hsum : ∀ j, (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) +
      (∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ) := by
    intro j
    have := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin m)))
      (p := fun a => epsT t ε a = true) (f := fun a => star (u a j) * u a j)
    simp only [Bool.not_eq_true] at this
    rw [this]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  have e2 : ∀ j, Complex.exp (2 * (s : ℂ) * (X j : ℂ)) = ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) := by
    intro j
    push_cast
    rw [← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  unfold nS
  push_cast
  simp only [e2]
  have key : Complex.I * (c : ℂ) * (Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j) -
      Complex.I * (c : ℂ) * (-Complex.I * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) =
      -((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) * ∑ a, ((‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    simp only [← hsum, mul_add, Finset.sum_add_distrib]
    linear_combination ((c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = true), star (u a j) * u a j +
      (c : ℂ) * ∑ j, ((Real.exp (s * X j) ^ 2 : ℝ) : ℂ) *
        ∑ a ∈ Finset.univ.filter (fun a => epsT t ε a = false), star (u a j) * u a j) * hI
  rw [key, ← Complex.exp_add]
  have hswap : ∀ (E : Fin n → ℂ) (N : Fin m → Fin n → ℂ), (∑ j, E j * ∑ a, N a j) = ∑ a, ∑ j, N a j * E j := by
    intro E N
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  congr 1
  push_cast
  rw [hswap]
  ring

end DCalcCH

end PositivityTheory.Rg.Sw.Glob
