import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.DivisionPoints

namespace GroundTheory.Arith.Abelian

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

section Coprime

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

/- English proof (translation)
Use `set b := W.a₁ * x + W.a₃`. Use `set c := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆`. Establish `hD : b ^ 2 + 4 * c = W.Ψ₂Sq.eval x`. Simplify using `only [Ψ₂Sq, b, c, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]`. Expand and normalize the polynomial expressions, which then agree.

Use `set q : F[X] := X ^ 2 + C b * X - C c`. Establish `hq' : derivative q = C 2 * X + C b`. Simplify using `only [q, derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X, derivative_C]`. Simplify using the standard rewrite rules. Establish `hsep : q.Separable`.

Rewrite using `[Polynomial.separable_def, hq']`. Establish `hD0 : b ^ 2 + 4 * c ≠ 0` using `hD ▸ hx`. Use `⟨C (-4 * (b ^ 2 + 4 * c)⁻¹), C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b), ?_⟩` and prove the remaining obligations. Establish `e : (C 2 * X + C b) ^ 2 - 4 * q = C (b ^ 2 + 4 * c)`. Simplify using `only [q, map_add, map_pow, map_mul, map_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_mul, map_neg, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ hD0, C_1]`.

Establish `hdeg : q.degree ≠ 0`. Establish `: q.natDegree = 2` using `by simp only [q]; compute_degree!`. Introduce `h`. Rewrite `h` using `[degree_eq_natDegree (fun h0 => by rw [h0] at this; simp at this), this]`. Conclude with `absurd h (by decide)`.

Take `⟨y, hy⟩` from `IsSepClosed.exists_root q hdeg hsep`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[equation_iff]`. Simplify using `only [IsRoot, q, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy`. Simplify using `only [b, c] at hy`.

Take the linear combination `hy`.
-/
theorem exists_equation_of_Ψ₂Sq_ne_zero [IsSepClosed F] {x : F} (hx : W.Ψ₂Sq.eval x ≠ 0) :
    ∃ y, W.toAffine.Equation x y := by
  set b := W.a₁ * x + W.a₃
  set c := x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆
  have hD : b ^ 2 + 4 * c = W.Ψ₂Sq.eval x := by
    simp only [Ψ₂Sq, b, c, b₂, b₄, b₆, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    ring
  set q : F[X] := X ^ 2 + C b * X - C c
  have hq' : derivative q = C 2 * X + C b := by
    simp only [q, derivative_sub, derivative_add, derivative_X_pow, derivative_C_mul_X,
      derivative_C]
    simp
  have hsep : q.Separable := by
    rw [Polynomial.separable_def, hq']
    have hD0 : b ^ 2 + 4 * c ≠ 0 := hD ▸ hx
    refine ⟨C (-4 * (b ^ 2 + 4 * c)⁻¹), C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b), ?_⟩
    have e : (C 2 * X + C b) ^ 2 - 4 * q = C (b ^ 2 + 4 * c) := by
      simp only [q, map_add, map_pow, map_mul, map_ofNat]; ring
    calc C (-4 * (b ^ 2 + 4 * c)⁻¹) * q + C (b ^ 2 + 4 * c)⁻¹ * (C 2 * X + C b) * (C 2 * X + C b)
        = C (b ^ 2 + 4 * c)⁻¹ * ((C 2 * X + C b) ^ 2 - 4 * q) := by
          simp only [map_mul, map_neg, map_ofNat]; ring
      _ = 1 := by rw [e, ← C_mul, inv_mul_cancel₀ hD0, C_1]
  have hdeg : q.degree ≠ 0 := by
    have : q.natDegree = 2 := by simp only [q]; compute_degree!
    intro h
    rw [degree_eq_natDegree (fun h0 => by rw [h0] at this; simp at this), this] at h
    exact absurd h (by decide)
  obtain ⟨y, hy⟩ := IsSepClosed.exists_root q hdeg hsep
  refine ⟨y, ?_⟩
  rw [equation_iff]
  simp only [IsRoot, q, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hy
  simp only [b, c] at hy
  linear_combination hy

/- English proof (translation)
Assume the negation of the conclusion as `hfin`. Rewrite `hfin` using `[not_infinite_iff_finite]`. Use `Fintype.ofFinite k` as an intermediate fact. Use `set q := Fintype.card k`. Establish `hq : (q : k) = 0` using `FiniteField.cast_card_eq_zero k`.

Establish `hq1 : 1 < q` using `Fintype.one_lt_card`. Use `set p : k[X] := X ^ q - (X + 1)`. Establish `hp' : derivative p = -1`. Simplify using `only [p, derivative_sub, derivative_X_pow, derivative_add, derivative_X, derivative_one, hq, map_zero, zero_mul, add_zero, zero_sub]`. Establish `hsep : p.Separable`.

Rewrite using `[Polynomial.separable_def, hp']`. Conclude with `⟨0, -1, by ring⟩`. Establish `hdeg : p.natDegree = q`. Simplify using `only [p]`. Apply the tactic sequence `rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨x, hx⟩` from `IsSepClosed.exists_root p (by rw [degree_eq_natDegree (fun h => by rw [h] at hdeg; simp at hdeg; omega), hdeg]; simp; omega) hsep`. Simplify using `only [IsRoot, p, eval_sub, eval_pow, eval_X, eval_add, eval_one] at hx`. Rewrite `hx` using `[show x ^ q = x from FiniteField.pow_card x]`. Conclude with `one_ne_zero (by linear_combination -hx : (1 : k) = 0)`.
-/
theorem infinite_of_isSepClosed (k : Type*) [Field k] [IsSepClosed k] : Infinite k := by
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have := Fintype.ofFinite k
  set q := Fintype.card k
  have hq : (q : k) = 0 := FiniteField.cast_card_eq_zero k
  have hq1 : 1 < q := Fintype.one_lt_card
  set p : k[X] := X ^ q - (X + 1)
  have hp' : derivative p = -1 := by
    simp only [p, derivative_sub, derivative_X_pow, derivative_add, derivative_X, derivative_one,
      hq, map_zero, zero_mul, add_zero, zero_sub]
  have hsep : p.Separable := by
    rw [Polynomial.separable_def, hp']
    exact ⟨0, -1, by ring⟩
  have hdeg : p.natDegree = q := by
    simp only [p]
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp only [natDegree_X_pow]
    calc (X + 1 : k[X]).natDegree ≤ 1 := by compute_degree
      _ < q := hq1
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root p
    (by rw [degree_eq_natDegree (fun h => by rw [h] at hdeg; simp at hdeg; omega), hdeg]; simp; omega)
    hsep
  simp only [IsRoot, p, eval_sub, eval_pow, eval_X, eval_add, eval_one] at hx
  rw [show x ^ q = x from FiniteField.pow_card x] at hx
  exact one_ne_zero (by linear_combination -hx : (1 : k) = 0)

variable [W.IsElliptic]

/- English proof (translation)
Use `set K := AlgebraicClosure F`. Rewrite using `[Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K]`. Introduce `a`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or, not_not, not_not]`.

Take `⟨h1, h2⟩` from `hcon`. Use `set W' := W.map (algebraMap F K)`. Establish `e1 : (W'.Φ n).eval a = 0` using `by rw [map_Φ, eval_map_algebraMap, h1]`. Establish `e2 : (W'.ΨSq n).eval a = 0` using `by rw [map_ΨSq, eval_map_algebraMap, h2]`. Take `⟨y, hy⟩ : ∃ y, W'.toAffine.Equation a y` from `by set b := W'.a₁ * a + W'.a₃ set c := a ^ 3 + W'.a₂ * a ^ 2 + W'.a₄ * a + W'.a₆`.

Establish `hdeg : (X ^ 2 + C b * X - C c : K[X]).degree = 2` using `by compute_degree!`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_root (X ^ 2 + C b * X - C c : K[X]) (by rw [hdeg]; exact two_ne_zero)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[equation_iff]`. Simplify using `only [IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, b, c] at hy`.

Take the linear combination `hy`. Establish `h : W'.toAffine.Nonsingular a y` using `(equation_iff_nonsingular).mp hy`. Establish `hn0 : n • Point.some a y h = 0` using `(zsmul_eq_zero_iff W' h n).mpr e2`. Establish `hw : psiAt W' a y n = 0` using `(psiAt_eq_zero_iff W' h n).mpr e2`. Establish `hphi` using `Phi_eval W' h.1 n`.

Rewrite `hphi` using `[e1, hw]`. Establish `hprod : psiAt W' a y (n + 1) * psiAt W' a y (n - 1) = 0` using `by linear_combination hphi`. Break down `mul_eq_zero.mp hprod with hp | hp` into its components or cases. Use `(zsmul_eq_zero_iff W' h (n + 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)` as an intermediate fact. Rewrite `this` using `[add_zsmul, one_zsmul, hn0, zero_add]`.

Conclude with `Point.some_ne_zero h this`. Use `(zsmul_eq_zero_iff W' h (n - 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)` as an intermediate fact. Rewrite `this` using `[sub_zsmul, one_zsmul, hn0, zero_add, neg_eq_zero]`. Conclude with `Point.some_ne_zero h this`.
-/
theorem isCoprime_Φ_ΨSq (n : ℤ) : IsCoprime (W.Φ n) (W.ΨSq n) := by
  classical
  set K := AlgebraicClosure F
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K]
  intro a
  by_contra hcon
  rw [not_or, not_not, not_not] at hcon
  obtain ⟨h1, h2⟩ := hcon
  set W' := W.map (algebraMap F K)
  have e1 : (W'.Φ n).eval a = 0 := by rw [map_Φ, eval_map_algebraMap, h1]
  have e2 : (W'.ΨSq n).eval a = 0 := by rw [map_ΨSq, eval_map_algebraMap, h2]
  obtain ⟨y, hy⟩ : ∃ y, W'.toAffine.Equation a y := by
    set b := W'.a₁ * a + W'.a₃
    set c := a ^ 3 + W'.a₂ * a ^ 2 + W'.a₄ * a + W'.a₆
    have hdeg : (X ^ 2 + C b * X - C c : K[X]).degree = 2 := by compute_degree!
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (X ^ 2 + C b * X - C c : K[X])
      (by rw [hdeg]; exact two_ne_zero)
    refine ⟨y, ?_⟩
    rw [equation_iff]
    simp only [IsRoot, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X, b, c] at hy
    linear_combination hy
  have h : W'.toAffine.Nonsingular a y := (equation_iff_nonsingular).mp hy
  have hn0 : n • Point.some a y h = 0 := (zsmul_eq_zero_iff W' h n).mpr e2
  have hw : psiAt W' a y n = 0 := (psiAt_eq_zero_iff W' h n).mpr e2
  have hphi := Phi_eval W' h.1 n
  rw [e1, hw] at hphi
  have hprod : psiAt W' a y (n + 1) * psiAt W' a y (n - 1) = 0 := by linear_combination hphi
  rcases mul_eq_zero.mp hprod with hp | hp
  · have := (zsmul_eq_zero_iff W' h (n + 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)
    rw [add_zsmul, one_zsmul, hn0, zero_add] at this
    exact Point.some_ne_zero h this
  · have := (zsmul_eq_zero_iff W' h (n - 1)).mpr ((psiAt_eq_zero_iff W' h _).mp hp)
    rw [sub_zsmul, one_zsmul, hn0, zero_add, neg_eq_zero] at this
    exact Point.some_ne_zero h this

/- English proof (translation)
Introduce `h`. Use `isCoprime_Φ_ΨSq W n` as an intermediate fact. Rewrite `this` using `[h, isCoprime_zero_right]`. Establish `hdeg` using `natDegree_eq_zero_of_isUnit this`. Rewrite `hdeg` using `[natDegree_Φ]`.

Establish `: 0 < n.natAbs` using `Int.natAbs_pos.mpr hn`. Use `pow_pos this 2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem ΨSq_ne_zero_of_ne_zero {n : ℤ} (hn : n ≠ 0) : W.ΨSq n ≠ 0 := by
  intro h
  have := isCoprime_Φ_ΨSq W n
  rw [h, isCoprime_zero_right] at this
  have hdeg := natDegree_eq_zero_of_isUnit this
  rw [natDegree_Φ] at hdeg
  have : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have := pow_pos this 2
  omega

end Coprime

section Count

variable {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic]

/- English proof (translation)
Introduce `h`. Establish `h3 : (4 : F) = 0` using `by rw [← W.coeff_Ψ₂Sq, h, coeff_zero]`. Establish `h2 : W.b₂ = 0`. Use `congrArg (coeff · 2) h` as an intermediate fact. Simplify using `only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this`.

Simplify using `using this`. Establish `h0 : W.b₆ = 0`. Use `congrArg (coeff · 0) h` as an intermediate fact. Simplify using `only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this`. Simplify using `using this`.

Establish `hΔ : W.Δ = 0`. Rewrite using `[Δ, h2, h0]`. Take the linear combination `(-2 * W.b₄ ^ 3) * h3`. Conclude with `W.isUnit_Δ.ne_zero hΔ`.
-/
theorem Ψ₂Sq_ne_zero : W.Ψ₂Sq ≠ 0 := by
  intro h
  have h3 : (4 : F) = 0 := by rw [← W.coeff_Ψ₂Sq, h, coeff_zero]
  have h2 : W.b₂ = 0 := by
    have := congrArg (coeff · 2) h
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    simpa using this
  have h0 : W.b₆ = 0 := by
    have := congrArg (coeff · 0) h
    simp only [Ψ₂Sq, coeff_add, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_zero] at this
    simpa using this
  have hΔ : W.Δ = 0 := by
    rw [Δ, h2, h0]; linear_combination (-2 * W.b₄ ^ 3) * h3
  exact W.isUnit_Δ.ne_zero hΔ

omit [W.IsElliptic] in

/- English proof (translation)
Use `set m := n.natAbs ^ 2 - 1 with hm`. Establish `h4 : 4 ≤ n.natAbs ^ 2` using `by nlinarith`. Establish `hm1 : n.natAbs ^ 2 = m + 1` using `by omega`. Establish `hΦ : (W.Φ n).natDegree = m + 1` using `by rw [natDegree_Φ, hm1]`. Establish `hΨ : (W.ΨSq n).natDegree = m` using `natDegree_ΨSq W hn`.

Establish `cΦ : (W.Φ n).coeff (m + 1) = 1` using `by rw [← hm1, coeff_Φ]`. Establish `cΨ : (W.ΨSq n).coeff m = (n : F) ^ 2` using `by rw [hm, coeff_ΨSq]`. Establish `dΦ : (derivative (W.Φ n)).natDegree ≤ m` using `(natDegree_derivative_le _).trans (by rw [hΦ]; omega)`. Establish `dΨ : (derivative (W.ΨSq n)).natDegree ≤ m - 1` using `(natDegree_derivative_le _).trans (by rw [hΨ])`. Rewrite using `[coeff_sub, coeff_mul_add_eq_of_natDegree_le dΦ hΨ.le, coeff_derivative, show m + m = (m + 1) + (m - 1) by omega, coeff_mul_add_eq_of_natDegree_le hΦ.le dΨ, coeff_derivative, show m - 1 + 1 = m by omega, cΦ, cΨ]`.

Establish `: ((m - 1 : ℕ) : F) + 1 = m`. Rewrite using `[Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wronskian_coeff {n : ℤ} (hn : (n : F) ≠ 0) (h2 : 2 ≤ n.natAbs) :
    (derivative (W.Φ n) * W.ΨSq n - W.Φ n * derivative (W.ΨSq n)).coeff
      ((n.natAbs ^ 2 - 1) + (n.natAbs ^ 2 - 1)) = (n : F) ^ 2 := by
  set m := n.natAbs ^ 2 - 1 with hm
  have h4 : 4 ≤ n.natAbs ^ 2 := by nlinarith
  have hm1 : n.natAbs ^ 2 = m + 1 := by omega
  have hΦ : (W.Φ n).natDegree = m + 1 := by rw [natDegree_Φ, hm1]
  have hΨ : (W.ΨSq n).natDegree = m := natDegree_ΨSq W hn
  have cΦ : (W.Φ n).coeff (m + 1) = 1 := by rw [← hm1, coeff_Φ]
  have cΨ : (W.ΨSq n).coeff m = (n : F) ^ 2 := by rw [hm, coeff_ΨSq]
  have dΦ : (derivative (W.Φ n)).natDegree ≤ m :=
    (natDegree_derivative_le _).trans (by rw [hΦ]; omega)
  have dΨ : (derivative (W.ΨSq n)).natDegree ≤ m - 1 :=
    (natDegree_derivative_le _).trans (by rw [hΨ])
  rw [coeff_sub, coeff_mul_add_eq_of_natDegree_le dΦ hΨ.le, coeff_derivative,
    show m + m = (m + 1) + (m - 1) by omega, coeff_mul_add_eq_of_natDegree_le hΦ.le dΨ,
    coeff_derivative, show m - 1 + 1 = m by omega, cΦ, cΨ]
  have : ((m - 1 : ℕ) : F) + 1 = m := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring
  rw [this]
  ring

/- English proof (translation)
Use `infinite_of_isSepClosed F` as an intermediate fact. Establish `hprod : W.ΨSq n * W.Ψ₂Sq ≠ 0` using `mul_ne_zero (ΨSq_ne_zero_of_ne_zero W hn) (Ψ₂Sq_ne_zero W)`. Take `⟨x, hx⟩` from `Infinite.exists_notMem_finset (W.ΨSq n * W.Ψ₂Sq).roots.toFinset`. Rewrite `hx` using `[Multiset.mem_toFinset, mem_roots hprod, IsRoot, eval_mul, mul_eq_zero, not_or]`. Take `⟨y, hy⟩` from `exists_equation_of_Ψ₂Sq_ne_zero W hx.2`.

Establish `h : W.toAffine.Nonsingular x y` using `equation_iff_nonsingular.mp hy`. Conclude with `⟨.some x y h, fun h0 => hx.1 ((zsmul_eq_zero_iff W h n).mp h0)⟩`.
-/
theorem exists_zsmul_ne_zero [IsSepClosed F] [DecidableEq F] {n : ℤ} (hn : n ≠ 0) :
    ∃ P : W.toAffine.Point, n • P ≠ 0 := by
  have := infinite_of_isSepClosed F
  have hprod : W.ΨSq n * W.Ψ₂Sq ≠ 0 := mul_ne_zero (ΨSq_ne_zero_of_ne_zero W hn) (Ψ₂Sq_ne_zero W)
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (W.ΨSq n * W.Ψ₂Sq).roots.toFinset
  rw [Multiset.mem_toFinset, mem_roots hprod, IsRoot, eval_mul, mul_eq_zero, not_or] at hx
  obtain ⟨y, hy⟩ := exists_equation_of_Ψ₂Sq_ne_zero W hx.2
  have h : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
  exact ⟨.some x y h, fun h0 => hx.1 ((zsmul_eq_zero_iff W h n).mp h0)⟩

end Count

section Kernel

variable {F : Type*} [Field F] [IsSepClosed F] [DecidableEq F] (W : WeierstrassCurve F)
  [W.IsElliptic]

/- English proof (translation)
Establish `hn0 : n ≠ 0` using `by rintro rfl; simp at hn`. Break down `(by omega : n.natAbs = 1 ∨ 2 ≤ n.natAbs) with h1 | h2` into its components or cases. Establish `key : ∀ P : W.toAffine.Point, n • P = 0 ↔ P = 0`. Introduce `P`. Apply the tactic sequence `rcases Int.natAbs_eq_iff.mp h1 with h | h <;> rw [h] <;> simp [neg_zsmul]`.

Rewrite using `[h1, one_pow, Nat.card_eq_one_iff_exists]`. Conclude with `⟨⟨0, zsmul_zero n⟩, fun P => Subtype.ext ((key P.1).mp P.2)⟩`. Establish `hinf` using `infinite_of_isSepClosed F`. Establish `hcop` using `isCoprime_Φ_ΨSq W n`. Use `set K := AlgebraicClosure F`.

Use `set ι := algebraMap F K`. Establish `hcopK` using `(Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K (W.Φ n) (W.ΨSq n)).mp hcop`. Establish `noCommon : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0` using `fun x h1 h2 => by`. Take `⟨u, v, huv⟩` from `hcop`. Use `congrArg (eval x) huv` as an intermediate fact.

Simplify using `only [eval_add, eval_mul, h1, h2, mul_zero, add_zero, eval_one] at this`. Conclude with `zero_ne_one this`. Use `set Wr := derivative (W.Φ n) * (W.ΨSq n) - (W.Φ n) * derivative (W.ΨSq n) with hWrdef`. Establish `hWr : Wr ≠ 0` using `fun h => by`. Use `wronskian_coeff W hn h2` as an intermediate fact.

Rewrite `this` using `[← hWrdef, h, coeff_zero]`. Conclude with `pow_ne_zero 2 hn this.symm`. Establish `hΨ2 : W.Ψ₂Sq ≠ 0` using `Ψ₂Sq_ne_zero W`. Establish `hWrK : Wr.map ι ≠ 0` using `(Polynomial.map_ne_zero_iff ι.injective).mpr hWr`. Establish `hΨ2K : W.Ψ₂Sq.map ι ≠ 0` using `(Polynomial.map_ne_zero_iff ι.injective).mpr hΨ2`.

Use `set S1 : Finset K := (Wr.map ι).roots.toFinset ∪ (W.Ψ₂Sq.map ι).roots.toFinset`. Use `set Bad : Finset K := S1.image (fun a => aeval a (W.Φ n) / aeval a (W.ΨSq n)) ∪ (W.Ψ₂Sq.map ι).roots.toFinset`. Take `⟨t, ht⟩` from `Infinite.exists_notMem_finset (Bad.preimage ι ι.injective.injOn)`. Rewrite `ht` using `[Finset.mem_preimage]`. Establish `map_eval : ∀ (p : F[X]) (x : F), (p.map ι).eval (ι x) = ι (p.eval x)` using `fun p x => by`.

Rewrite using `[eval_map, eval₂_at_apply]`. Establish `hΨ2t : W.Ψ₂Sq.eval t ≠ 0`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Use `Finset.mem_union_right _ ?_` and prove the remaining obligations.

Rewrite using `[Multiset.mem_toFinset, mem_roots hΨ2K, IsRoot, map_eval, h, map_zero]`. Take `⟨yR, hyR⟩` from `exists_equation_of_Ψ₂Sq_ne_zero W hΨ2t`. Establish `hR : W.toAffine.Nonsingular t yR` using `equation_iff_nonsingular.mp hyR`. Use `set R : W.toAffine.Point := .some t yR hR`. Establish `hR0 : R ≠ 0` using `Point.some_ne_zero hR`.

Establish `hRR : R ≠ -R`. Introduce `h`. Rewrite `h` using `[Point.neg_some, Point.some.injEq]`. Apply `hΨ2t` to reduce the goal to its premises. Establish `e` using `two_y_sq W hyR`.

Establish `hy : 2 * yR + W.a₁ * t + W.a₃ = 0` using `by rw [negY] at h; linear_combination h.2`. Rewrite `e` using `[hy]`. Simplify using `only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X]`. Take the linear combination `-e`. Use `set G := (W.Φ n) - C t * (W.ΨSq n) with hGdef`.

Establish `hΦdeg : (W.Φ n).natDegree = n.natAbs ^ 2` using `natDegree_Φ W n`. Establish `hΨdeg : (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1` using `natDegree_ΨSq W hn`. Establish `h4 : 4 ≤ n.natAbs ^ 2` using `by nlinarith`. Establish `hlt : (C t * W.ΨSq n).natDegree < (W.Φ n).natDegree`. Combine the equalities or inequalities in the displayed calculation.

Establish `hGdeg : G.natDegree = n.natAbs ^ 2` using `by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hΦdeg]`. Establish `hG0 : G ≠ 0`. Introduce `h`. Rewrite `hGdeg` using `[h, natDegree_zero]`. Use linear arithmetic over natural numbers and integers.

Establish `hGsep : G.Separable`. Rewrite using `[Polynomial.separable_def, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K]`. Introduce `a`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or, not_not, not_not]`.

Take `⟨g1, g2⟩` from `hcon`. Simplify using `only [G, derivative_sub, derivative_C_mul, map_sub, map_mul, aeval_C] at g1 g2`. Establish `hΨa : aeval a (W.ΨSq n) ≠ 0`. Introduce `h0`. Rewrite `g1` using `[h0, mul_zero, sub_zero]`.

Break down `hcopK a with h | h` into its components or cases. Conclude with `h g1`. Conclude with `h h0`. Establish `hWa : aeval a Wr = 0`. Simplify using `only [Wr, map_sub, map_mul]`.

Take the linear combination `(aeval a (W.ΨSq n)) * g2 - (aeval a (derivative (W.ΨSq n))) * g1`. Apply `ht` to reduce the goal to its premises. Use `Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ?_, ?_⟩)` and prove the remaining obligations. Use `Finset.mem_union_left _ ?_` and prove the remaining obligations. Rewrite using `[Multiset.mem_toFinset, mem_roots hWrK, IsRoot, eval_map_algebraMap, hWa]`.

Rewrite using `[div_eq_iff hΨa]`. Take the linear combination `g1`. Establish `hsplit : G.Splits` using `IsSepClosed.splits_of_separable G hGsep`. Establish `hcard : G.roots.toFinset.card = n.natAbs ^ 2`. Rewrite using `[Multiset.toFinset_card_of_nodup (nodup_roots hGsep), ← hGdeg]`.

Conclude with `(splits_iff_card_roots.mp hsplit)`. Establish `root_facts : ∀ x ∈ G.roots.toFinset, (W.ΨSq n).eval x ≠ 0 ∧ (W.Φ n).eval x / (W.ΨSq n).eval x = t ∧ W.Ψ₂Sq.eval x ≠ 0`. Introduce `x hx`. Rewrite `hx` using `[Multiset.mem_toFinset, mem_roots hG0, IsRoot]`. Simplify using `only [G, eval_sub, eval_mul, eval_C] at hx`.

Establish `hΨx : (W.ΨSq n).eval x ≠ 0` using `fun h => noCommon x h (by rw [h, mul_zero, sub_zero] at hx; exact hx)`. Establish `hq : (W.Φ n).eval x / (W.ΨSq n).eval x = t` using `by rw [div_eq_iff hΨx]; linear_combination hx`. Use `⟨hΨx, hq, fun h => ht ?_⟩` and prove the remaining obligations. Use `Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ι x, ?_, ?_⟩)` and prove the remaining obligations. Use `Finset.mem_union_right _ ?_` and prove the remaining obligations.

Rewrite using `[Multiset.mem_toFinset, mem_roots hΨ2K, IsRoot, map_eval, h, map_zero]`. Use `show aeval (ι x) (W.Φ n) / aeval (ι x) (W.ΨSq n) = ι t`. Rewrite using `[aeval_algebraMap_apply_eq_algebraMap_eval, aeval_algebraMap_apply_eq_algebraMap_eval, ← map_div₀, hq]`. Establish `fibre_root : ∀ Q : W.toAffine.Point, n • Q = R → xOf W Q ∈ G.roots.toFinset`. Introduce `Q hQ`.

Establish `hQ0 : Q ≠ 0` using `by rintro rfl; rw [zsmul_zero] at hQ; exact hR0 hQ.symm`. Take `⟨y, h, hQe⟩` from `exists_eq_some_xOf W hQ0`. Rewrite `hQ` using `[hQe]`. Establish `hΨx : (W.ΨSq n).eval (xOf W Q) ≠ 0`. Introduce `h0`.

Conclude with `hR0 (hQ ▸ (zsmul_eq_zero_iff W h n).mpr h0)`. Use `xOf_zsmul W h n hΨx` as an intermediate fact. Rewrite `this` using `[hQ]`. Rewrite using `[Multiset.mem_toFinset, mem_roots hG0, IsRoot]`. Simplify using `only [G, eval_sub, eval_mul, eval_C]`.

Rewrite using `[show t = xOf W R from rfl, this, div_mul_cancel₀ _ hΨx, sub_self]`. Establish `root_fibre : ∀ x ∈ G.roots.toFinset, ∃ Q : W.toAffine.Point, n • Q = R ∧ xOf W Q = x`. Introduce `x hx`. Take `⟨hΨx, hq, hΨ2x⟩` from `root_facts x hx`. Take `⟨y, hy⟩` from `exists_equation_of_Ψ₂Sq_ne_zero W hΨ2x`.

Establish `h : W.toAffine.Nonsingular x y` using `equation_iff_nonsingular.mp hy`. Establish `hne : n • Point.some x y h ≠ 0` using `fun h0 => hΨx ((zsmul_eq_zero_iff W h n).mp h0)`. Take `⟨y', h', he⟩` from `exists_eq_some_xOf W hne`. Establish `hx' : xOf W (n • Point.some x y h) = t` using `by rw [xOf_zsmul W h n hΨx, hq]`. Establish `hor` using `(Point.X_eq_iff (h₁ := h') (h₂ := hR)).mp hx'`.

Rewrite `hor` using `[← he]`. Break down `hor with hor | hor` into its components or cases. Conclude with `⟨_, hor, rfl⟩`. Conclude with `⟨-Point.some x y h, by rw [zsmul_neg, hor, neg_neg], by rw [xOf_neg, xOf_some]⟩`. Establish `hfib : Nat.card {Q : W.toAffine.Point // n • Q = R} = n.natAbs ^ 2`.

Rewrite using `[← hcard, ← Nat.card_eq_finsetCard]`. Use `Nat.card_congr (Equiv.ofBijective (fun Q => ⟨xOf W Q.1, fibre_root Q.1 Q.2⟩) ⟨?_, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨Q1, hQ1⟩ ⟨Q2, hQ2⟩ heq`. Simplify using `only [Subtype.mk.injEq] at heq`. Establish `hQ10 : Q1 ≠ 0` using `by rintro rfl; rw [zsmul_zero] at hQ1; exact hR0 hQ1.symm`.

Establish `hQ20 : Q2 ≠ 0` using `by rintro rfl; rw [zsmul_zero] at hQ2; exact hR0 hQ2.symm`. Take `⟨y1, h1, e1⟩` from `exists_eq_some_xOf W hQ10`. Take `⟨y2, h2, e2⟩` from `exists_eq_some_xOf W hQ20`. Establish `hor` using `(Point.X_eq_iff (h₁ := h1) (h₂ := h2)).mp heq`. Rewrite `hor` using `[← e1, ← e2]`.

Break down `hor with hor | hor` into its components or cases. Conclude with `Subtype.ext hor`. It suffices to derive a contradiction. Apply `hRR` to reduce the goal to its premises. Establish `: n • Q1 = -(n • Q2)` using `by rw [hor, zsmul_neg]`.

Rewrite `this` using `[hQ1, hQ2]`. Then use the resulting hypothesis. Introduce and unpack `⟨x, hx⟩`. Take `⟨Q, hQ, hxQ⟩` from `root_fibre x hx`. Conclude with `⟨⟨Q, hQ⟩, Subtype.ext hxQ⟩`. Choose the witnesses or unpack the hypotheses as in `⟨x0, hx0⟩ : G.roots.toFinset.Nonempty := by`.

Rewrite using `[← Finset.card_pos, hcard]`. Check the signs of the components of the expression. Take `⟨Q0, hQ0, -⟩` from `root_fibre x0 hx0`. Rewrite using `[← hfib]`. Conclude with `Nat.card_congr { toFun := fun P => ⟨P.1 + Q0, by rw [zsmul_add, P.2, hQ0, zero_add]⟩ invFun := fun Q => ⟨Q.1 - Q0, by rw [zsmul_sub, Q.2, hQ0, sub_self]⟩ left_inv := fun P => Subtype.ext (add_sub_cancel_right _ _) right_inv := fun Q => Subtype.ext (sub_add_cancel _ _) }`.
-/
theorem card_zsmul_eq_zero {n : ℤ} (hn : (n : F) ≠ 0) :
    Nat.card {P : W.toAffine.Point // n • P = 0} = n.natAbs ^ 2 := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  rcases (by omega : n.natAbs = 1 ∨ 2 ≤ n.natAbs) with h1 | h2
  · have key : ∀ P : W.toAffine.Point, n • P = 0 ↔ P = 0 := by
      intro P
      rcases Int.natAbs_eq_iff.mp h1 with h | h <;> rw [h] <;> simp [neg_zsmul]
    rw [h1, one_pow, Nat.card_eq_one_iff_exists]
    exact ⟨⟨0, zsmul_zero n⟩, fun P => Subtype.ext ((key P.1).mp P.2)⟩
  have hinf := infinite_of_isSepClosed F
  have hcop := isCoprime_Φ_ΨSq W n
  set K := AlgebraicClosure F
  set ι := algebraMap F K
  have hcopK := (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K (W.Φ n) (W.ΨSq n)).mp hcop
  have noCommon : ∀ x : F, (W.ΨSq n).eval x = 0 → (W.Φ n).eval x ≠ 0 := fun x h1 h2 => by
    obtain ⟨u, v, huv⟩ := hcop
    have := congrArg (eval x) huv
    simp only [eval_add, eval_mul, h1, h2, mul_zero, add_zero, eval_one] at this
    exact zero_ne_one this
  set Wr := derivative (W.Φ n) * (W.ΨSq n) - (W.Φ n) * derivative (W.ΨSq n) with hWrdef
  have hWr : Wr ≠ 0 := fun h => by
    have := wronskian_coeff W hn h2
    rw [← hWrdef, h, coeff_zero] at this
    exact pow_ne_zero 2 hn this.symm
  have hΨ2 : W.Ψ₂Sq ≠ 0 := Ψ₂Sq_ne_zero W
  have hWrK : Wr.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hWr
  have hΨ2K : W.Ψ₂Sq.map ι ≠ 0 := (Polynomial.map_ne_zero_iff ι.injective).mpr hΨ2
  set S1 : Finset K := (Wr.map ι).roots.toFinset ∪ (W.Ψ₂Sq.map ι).roots.toFinset
  set Bad : Finset K :=
    S1.image (fun a => aeval a (W.Φ n) / aeval a (W.ΨSq n)) ∪ (W.Ψ₂Sq.map ι).roots.toFinset
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (Bad.preimage ι ι.injective.injOn)
  rw [Finset.mem_preimage] at ht
  have map_eval : ∀ (p : F[X]) (x : F), (p.map ι).eval (ι x) = ι (p.eval x) := fun p x => by
    rw [eval_map, eval₂_at_apply]

  have hΨ2t : W.Ψ₂Sq.eval t ≠ 0 := by
    intro h
    apply ht
    refine Finset.mem_union_right _ ?_
    rw [Multiset.mem_toFinset, mem_roots hΨ2K, IsRoot, map_eval, h, map_zero]
  obtain ⟨yR, hyR⟩ := exists_equation_of_Ψ₂Sq_ne_zero W hΨ2t
  have hR : W.toAffine.Nonsingular t yR := equation_iff_nonsingular.mp hyR
  set R : W.toAffine.Point := .some t yR hR
  have hR0 : R ≠ 0 := Point.some_ne_zero hR
  have hRR : R ≠ -R := by
    intro h
    rw [Point.neg_some, Point.some.injEq] at h
    apply hΨ2t
    have e := two_y_sq W hyR
    have hy : 2 * yR + W.a₁ * t + W.a₃ = 0 := by rw [negY] at h; linear_combination h.2
    rw [hy] at e
    simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination -e

  set G := (W.Φ n) - C t * (W.ΨSq n) with hGdef
  have hΦdeg : (W.Φ n).natDegree = n.natAbs ^ 2 := natDegree_Φ W n
  have hΨdeg : (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 := natDegree_ΨSq W hn
  have h4 : 4 ≤ n.natAbs ^ 2 := by nlinarith
  have hlt : (C t * W.ΨSq n).natDegree < (W.Φ n).natDegree := by
    calc (C t * W.ΨSq n).natDegree ≤ (W.ΨSq n).natDegree := natDegree_C_mul_le _ _
      _ < (W.Φ n).natDegree := by rw [hΦdeg, hΨdeg]; omega
  have hGdeg : G.natDegree = n.natAbs ^ 2 := by rw [natDegree_sub_eq_left_of_natDegree_lt hlt, hΦdeg]
  have hG0 : G ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hGdeg; omega
  have hGsep : G.Separable := by
    rw [Polynomial.separable_def, Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed F K]
    intro a
    by_contra hcon
    rw [not_or, not_not, not_not] at hcon
    obtain ⟨g1, g2⟩ := hcon
    simp only [G, derivative_sub, derivative_C_mul, map_sub, map_mul, aeval_C] at g1 g2
    have hΨa : aeval a (W.ΨSq n) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, sub_zero] at g1
      rcases hcopK a with h | h
      · exact h g1
      · exact h h0
    have hWa : aeval a Wr = 0 := by
      simp only [Wr, map_sub, map_mul]
      linear_combination (aeval a (W.ΨSq n)) * g2 - (aeval a (derivative (W.ΨSq n))) * g1
    apply ht
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ?_, ?_⟩)
    · refine Finset.mem_union_left _ ?_
      rw [Multiset.mem_toFinset, mem_roots hWrK, IsRoot, eval_map_algebraMap, hWa]
    · rw [div_eq_iff hΨa]; linear_combination g1
  have hsplit : G.Splits := IsSepClosed.splits_of_separable G hGsep
  have hcard : G.roots.toFinset.card = n.natAbs ^ 2 := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hGsep), ← hGdeg]
    exact (splits_iff_card_roots.mp hsplit)

  have root_facts : ∀ x ∈ G.roots.toFinset,
      (W.ΨSq n).eval x ≠ 0 ∧ (W.Φ n).eval x / (W.ΨSq n).eval x = t ∧ W.Ψ₂Sq.eval x ≠ 0 := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hG0, IsRoot] at hx
    simp only [G, eval_sub, eval_mul, eval_C] at hx
    have hΨx : (W.ΨSq n).eval x ≠ 0 := fun h => noCommon x h (by rw [h, mul_zero, sub_zero] at hx; exact hx)
    have hq : (W.Φ n).eval x / (W.ΨSq n).eval x = t := by rw [div_eq_iff hΨx]; linear_combination hx
    refine ⟨hΨx, hq, fun h => ht ?_⟩
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ι x, ?_, ?_⟩)
    · refine Finset.mem_union_right _ ?_
      rw [Multiset.mem_toFinset, mem_roots hΨ2K, IsRoot, map_eval, h, map_zero]
    · show aeval (ι x) (W.Φ n) / aeval (ι x) (W.ΨSq n) = ι t
      rw [aeval_algebraMap_apply_eq_algebraMap_eval, aeval_algebraMap_apply_eq_algebraMap_eval,
        ← map_div₀, hq]

  have fibre_root : ∀ Q : W.toAffine.Point, n • Q = R → xOf W Q ∈ G.roots.toFinset := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := by rintro rfl; rw [zsmul_zero] at hQ; exact hR0 hQ.symm
    obtain ⟨y, h, hQe⟩ := exists_eq_some_xOf W hQ0
    rw [hQe] at hQ
    have hΨx : (W.ΨSq n).eval (xOf W Q) ≠ 0 := by
      intro h0; exact hR0 (hQ ▸ (zsmul_eq_zero_iff W h n).mpr h0)
    have := xOf_zsmul W h n hΨx
    rw [hQ] at this
    rw [Multiset.mem_toFinset, mem_roots hG0, IsRoot]
    simp only [G, eval_sub, eval_mul, eval_C]
    rw [show t = xOf W R from rfl, this, div_mul_cancel₀ _ hΨx, sub_self]
  have root_fibre : ∀ x ∈ G.roots.toFinset, ∃ Q : W.toAffine.Point, n • Q = R ∧ xOf W Q = x := by
    intro x hx
    obtain ⟨hΨx, hq, hΨ2x⟩ := root_facts x hx
    obtain ⟨y, hy⟩ := exists_equation_of_Ψ₂Sq_ne_zero W hΨ2x
    have h : W.toAffine.Nonsingular x y := equation_iff_nonsingular.mp hy
    have hne : n • Point.some x y h ≠ 0 := fun h0 => hΨx ((zsmul_eq_zero_iff W h n).mp h0)
    obtain ⟨y', h', he⟩ := exists_eq_some_xOf W hne
    have hx' : xOf W (n • Point.some x y h) = t := by rw [xOf_zsmul W h n hΨx, hq]
    have hor := (Point.X_eq_iff (h₁ := h') (h₂ := hR)).mp hx'
    rw [← he] at hor
    rcases hor with hor | hor
    · exact ⟨_, hor, rfl⟩
    · exact ⟨-Point.some x y h, by rw [zsmul_neg, hor, neg_neg], by rw [xOf_neg, xOf_some]⟩

  have hfib : Nat.card {Q : W.toAffine.Point // n • Q = R} = n.natAbs ^ 2 := by
    rw [← hcard, ← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.ofBijective (fun Q => ⟨xOf W Q.1, fibre_root Q.1 Q.2⟩) ⟨?_, ?_⟩)
    · rintro ⟨Q1, hQ1⟩ ⟨Q2, hQ2⟩ heq
      simp only [Subtype.mk.injEq] at heq
      have hQ10 : Q1 ≠ 0 := by rintro rfl; rw [zsmul_zero] at hQ1; exact hR0 hQ1.symm
      have hQ20 : Q2 ≠ 0 := by rintro rfl; rw [zsmul_zero] at hQ2; exact hR0 hQ2.symm
      obtain ⟨y1, h1, e1⟩ := exists_eq_some_xOf W hQ10
      obtain ⟨y2, h2, e2⟩ := exists_eq_some_xOf W hQ20
      have hor := (Point.X_eq_iff (h₁ := h1) (h₂ := h2)).mp heq
      rw [← e1, ← e2] at hor
      rcases hor with hor | hor
      · exact Subtype.ext hor
      · exfalso; apply hRR
        have : n • Q1 = -(n • Q2) := by rw [hor, zsmul_neg]
        rwa [hQ1, hQ2] at this
    · rintro ⟨x, hx⟩
      obtain ⟨Q, hQ, hxQ⟩ := root_fibre x hx
      exact ⟨⟨Q, hQ⟩, Subtype.ext hxQ⟩
  obtain ⟨x0, hx0⟩ : G.roots.toFinset.Nonempty := by
    rw [← Finset.card_pos, hcard]; positivity
  obtain ⟨Q0, hQ0, -⟩ := root_fibre x0 hx0
  rw [← hfib]
  exact Nat.card_congr
    { toFun := fun P => ⟨P.1 + Q0, by rw [zsmul_add, P.2, hQ0, zero_add]⟩
      invFun := fun Q => ⟨Q.1 - Q0, by rw [zsmul_sub, Q.2, hQ0, sub_self]⟩
      left_inv := fun P => Subtype.ext (add_sub_cancel_right _ _)
      right_inv := fun Q => Subtype.ext (sub_add_cancel _ _) }

omit [IsSepClosed F] [W.IsElliptic] in

/- English proof (translation)
Consider the cases of `P with`. Consider the case `zero => rw [← Point.zero_def]`. Simplify using the standard rewrite rules. Consider the case `some x y h`. Rewrite using `[zsmul_eq_zero_iff W h n]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `Or.inr ⟨x, y, h, rfl, hx⟩`. Introduce and unpack `(h0 | ⟨x', y', h', he, hx⟩)`. Conclude with `absurd h0 (Point.some_ne_zero h)`.

Rewrite `he` using `[Point.some.injEq]`. Rewrite using `[he.1]`. Conclude with `hx`.
-/
theorem zsmul_eq_zero_iff_ΨSq (n : ℤ) (P : W.toAffine.Point) :
    n • P = 0 ↔ P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0 := by
  cases P with
  | zero => rw [← Point.zero_def]; simp
  | some x y h =>
    rw [zsmul_eq_zero_iff W h n]
    constructor
    · intro hx; exact Or.inr ⟨x, y, h, rfl, hx⟩
    · rintro (h0 | ⟨x', y', h', he, hx⟩)
      · exact absurd h0 (Point.some_ne_zero h)
      · rw [Point.some.injEq] at he; rw [he.1]; exact hx

/- English proof (translation)
Rewrite using `[← card_zsmul_eq_zero W hn]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun P => (zsmul_eq_zero_iff_ΨSq W n P).symm)`.
-/
theorem card_ΨSq_eq_zero {n : ℤ} (hn : (n : F) ≠ 0) :
    Nat.card {P : W.toAffine.Point // P = 0 ∨ ∃ (x y : F) (h : W.toAffine.Nonsingular x y),
      P = .some x y h ∧ (W.ΨSq n).eval x = 0} = n.natAbs ^ 2 := by
  rw [← card_zsmul_eq_zero W hn]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun P => (zsmul_eq_zero_iff_ΨSq W n P).symm)

end Kernel

end GroundTheory.Arith.Abelian
