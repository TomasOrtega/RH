import Formalism.WachModuleLifts.Statement

open Finset

noncomputable section

namespace Formalism.CL

namespace CSOddG

section Digits

variable {p : ℕ} [hp : Fact p.Prime]

def S (p n : ℕ) : ℕ := (Nat.digits p n).sum

end Digits

section Poly

variable {p : ℕ} [hp : Fact p.Prime]

def U (p : ℕ) [Fact p.Prime] (g : ℕ) : Polynomial ℚ_[p] :=
  Polynomial.C ((p : ℚ_[p])⁻¹) * phiIter p g

/- English proof (translation)
Conclude with `hp.1.ne_zero` after adjusting the coercions.
-/
lemma pQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.1.ne_zero

/- English proof (translation)
Simplify using `only [phiIter, Function.iterate_succ_apply']`.
-/
lemma phiIter_succ' (g : ℕ) : phiIter p (g + 1) = (phiPoly p).comp (phiIter p g) := by
  simp only [phiIter, Function.iterate_succ_apply']

/- English proof (translation)
Simplify using `[U, phiIter]`.
-/
lemma U_zero : U p 0 = Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.X := by
  simp [U, phiIter]

/- English proof (translation)
Establish `hab : Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.C (p : ℚ_[p]) = 1`. Rewrite using `[← Polynomial.C_mul, inv_mul_cancel₀ pQ_ne, Polynomial.C_1]`. Establish `hQ : phiIter p g = Polynomial.C (p : ℚ_[p]) * U p g`. Rewrite using `[U, ← mul_assoc, mul_comm (Polynomial.C (p : ℚ_[p])), hab, one_mul]`. Establish `hpow : ∀ x : Polynomial ℚ_[p], x ^ p = x ^ (p - 1) * x` using `fun x => by`.

Rewrite using `[← pow_succ, Nat.sub_add_cancel hp.1.one_le]`. Rewrite using `[U, phiIter_succ', hQ]`. Simplify using `only [phiPoly, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]`. Rewrite using `[hpow, mul_pow, Polynomial.C_pow]`. Use `set a := Polynomial.C (p : ℚ_[p])`.

Use `set b := Polynomial.C ((p : ℚ_[p])⁻¹)`. Use `set u := U p g`. Take the linear combination `(a ^ (p - 1) * u ^ (p - 1) * u - a ^ (p - 1) * u ^ (p - 1) + 1) * hab`.
-/
lemma U_succ (g : ℕ) : U p (g + 1) =
    Polynomial.C ((p : ℚ_[p]) ^ (p - 1)) * U p g ^ (p - 1) * (U p g - 1) + 1 := by
  have hab : Polynomial.C ((p : ℚ_[p])⁻¹) * Polynomial.C (p : ℚ_[p]) = 1 := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ pQ_ne, Polynomial.C_1]
  have hQ : phiIter p g = Polynomial.C (p : ℚ_[p]) * U p g := by
    rw [U, ← mul_assoc, mul_comm (Polynomial.C (p : ℚ_[p])), hab, one_mul]
  have hpow : ∀ x : Polynomial ℚ_[p], x ^ p = x ^ (p - 1) * x := fun x => by
    rw [← pow_succ, Nat.sub_add_cancel hp.1.one_le]
  rw [U, phiIter_succ', hQ]
  simp only [phiPoly, Polynomial.add_comp, Polynomial.sub_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.X_pow_comp]
  rw [hpow, mul_pow, Polynomial.C_pow]
  set a := Polynomial.C (p : ℚ_[p])
  set b := Polynomial.C ((p : ℚ_[p])⁻¹)
  set u := U p g
  linear_combination (a ^ (p - 1) * u ^ (p - 1) * u - a ^ (p - 1) * u ^ (p - 1) + 1) * hab

/- English proof (translation)
Proceed by induction on `g with`. Consider the case `zero`. Rewrite using `[U_zero, pow_zero]`. Use `⟨(Polynomial.natDegree_C_mul_le _ _).trans (by simp), by simp⟩` and prove the remaining obligations. Consider the case `succ g ih`.

Take `⟨h1, h2⟩` from `ih`. Establish `hp1` using `hp.1.one_le`. Establish `hdegpow : (U p g ^ (p - 1)).natDegree ≤ (p - 1) * p ^ g` using `Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ h1)`. Establish `hdegsub : (U p g - 1).natDegree ≤ p ^ g` using `(Polynomial.natDegree_sub_le _ _).trans (max_le h1 (by simp))`. Establish `hsum : (p - 1) * p ^ g + p ^ g = p ^ (g + 1)`.

Rewrite using `[pow_succ, mul_comm (p ^ g) p]`. Use `nth_rw 2 [← one_mul (p ^ g)]`. Rewrite using `[← Nat.add_mul, Nat.sub_add_cancel hp1]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[U_succ]`.

Use `(Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))` and prove the remaining obligations. Use `(Polynomial.natDegree_mul_le).trans ?_` and prove the remaining obligations. Use `(Nat.add_le_add_right ((Polynomial.natDegree_C_mul_le _ _).trans hdegpow) _).trans ?_` and prove the remaining obligations. Conclude with `(Nat.add_le_add_left hdegsub _).trans hsum.le`. Establish `hform : U p (g + 1) = Polynomial.C ((p : ℚ_[p]) ^ (p - 1)) * (U p g ^ p - U p g ^ (p - 1)) + 1`.

Rewrite using `[U_succ]`. Establish `: U p g ^ p = U p g ^ (p - 1) * U p g`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hp1]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hne : p ^ (g + 1) ≠ 0` using `pow_ne_zero _ hp.1.ne_zero`. Establish `hc1 : (U p g ^ p).coeff (p ^ (g + 1)) = ((p : ℚ_[p])⁻¹) ^ p`. Rewrite using `[pow_succ', Polynomial.coeff_pow_of_natDegree_le h1, h2]`. Establish `hc2 : (U p g ^ (p - 1)).coeff (p ^ (g + 1)) = 0`. Apply `Polynomial.coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises.

Use `lt_of_le_of_lt hdegpow ?_` and prove the remaining obligations. Rewrite using `[← hsum]`. Use `pow_pos hp.1.pos g` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[hform, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub, hc1, hc2, Polynomial.coeff_one, if_neg hne, sub_zero, add_zero]`.

Establish `: ((p : ℚ_[p])⁻¹) ^ p = ((p : ℚ_[p])⁻¹) ^ (p - 1) * (p : ℚ_[p])⁻¹`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hp1]`. Rewrite using `[this, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ pQ_ne, one_pow, one_mul]`.
-/
lemma U_deg (g : ℕ) : (U p g).natDegree ≤ p ^ g ∧ (U p g).coeff (p ^ g) = (p : ℚ_[p])⁻¹ := by
  induction g with
  | zero =>
    rw [U_zero, pow_zero]
    refine ⟨(Polynomial.natDegree_C_mul_le _ _).trans (by simp), by simp⟩
  | succ g ih =>
    obtain ⟨h1, h2⟩ := ih
    have hp1 := hp.1.one_le
    have hdegpow : (U p g ^ (p - 1)).natDegree ≤ (p - 1) * p ^ g :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ h1)
    have hdegsub : (U p g - 1).natDegree ≤ p ^ g :=
      (Polynomial.natDegree_sub_le _ _).trans (max_le h1 (by simp))
    have hsum : (p - 1) * p ^ g + p ^ g = p ^ (g + 1) := by
      rw [pow_succ, mul_comm (p ^ g) p]
      nth_rw 2 [← one_mul (p ^ g)]
      rw [← Nat.add_mul, Nat.sub_add_cancel hp1]
    constructor
    · rw [U_succ]
      refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
      refine (Polynomial.natDegree_mul_le).trans ?_
      refine (Nat.add_le_add_right ((Polynomial.natDegree_C_mul_le _ _).trans hdegpow) _).trans ?_
      exact (Nat.add_le_add_left hdegsub _).trans hsum.le
    · have hform : U p (g + 1) =
          Polynomial.C ((p : ℚ_[p]) ^ (p - 1)) * (U p g ^ p - U p g ^ (p - 1)) + 1 := by
        rw [U_succ]
        have : U p g ^ p = U p g ^ (p - 1) * U p g := by
          rw [← pow_succ, Nat.sub_add_cancel hp1]
        rw [this]; ring
      have hne : p ^ (g + 1) ≠ 0 := pow_ne_zero _ hp.1.ne_zero
      have hc1 : (U p g ^ p).coeff (p ^ (g + 1)) = ((p : ℚ_[p])⁻¹) ^ p := by
        rw [pow_succ', Polynomial.coeff_pow_of_natDegree_le h1, h2]
      have hc2 : (U p g ^ (p - 1)).coeff (p ^ (g + 1)) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        refine lt_of_le_of_lt hdegpow ?_
        rw [← hsum]
        have := pow_pos hp.1.pos g
        omega
      rw [hform, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_sub, hc1, hc2,
        Polynomial.coeff_one, if_neg hne, sub_zero, add_zero]
      have : ((p : ℚ_[p])⁻¹) ^ p = ((p : ℚ_[p])⁻¹) ^ (p - 1) * (p : ℚ_[p])⁻¹ := by
        rw [← pow_succ, Nat.sub_add_cancel hp1]
      rw [this, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ pQ_ne, one_pow, one_mul]

/- English proof (translation)
The claim follows from `(Polynomial.natDegree_sub_le _ _).trans (max_le (U_deg g).1 (by simp))`.
-/
lemma Z_deg (g : ℕ) : (U p g - 1).natDegree ≤ p ^ g :=
  (Polynomial.natDegree_sub_le _ _).trans (max_le (U_deg g).1 (by simp))

/- English proof (translation)
Rewrite using `[mul_comm, Polynomial.coeff_pow_of_natDegree_le (Z_deg g), Polynomial.coeff_sub, (U_deg g).2, Polynomial.coeff_one, if_neg (pow_ne_zero _ hp.1.ne_zero), sub_zero]`.
-/
lemma Z_pow_top (g r : ℕ) : ((U p g - 1) ^ r).coeff (p ^ g * r) = ((p : ℚ_[p])⁻¹) ^ r := by
  rw [mul_comm, Polynomial.coeff_pow_of_natDegree_le (Z_deg g), Polynomial.coeff_sub,
    (U_deg g).2, Polynomial.coeff_one, if_neg (pow_ne_zero _ hp.1.ne_zero), sub_zero]

/- English proof (translation)
Apply `Polynomial.coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Use `lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (Z_deg g))) ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `Nat.mul_lt_mul_of_pos_left h (pow_pos hp.1.pos g)`.
-/
lemma Z_pow_lt (g r n : ℕ) (h : n < r) : ((U p g - 1) ^ n).coeff (p ^ g * r) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  refine lt_of_le_of_lt (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (Z_deg g))) ?_
  rw [mul_comm]
  exact Nat.mul_lt_mul_of_pos_left h (pow_pos hp.1.pos g)

end Poly

section Norms

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Rewrite using `[norm_pow, norm_inv, Padic.norm_p, inv_inv, zpow_natCast]`.
-/
lemma norm_pinv_pow (k : ℕ) : ‖((p : ℚ_[p])⁻¹) ^ k‖ = (p : ℝ) ^ (k : ℤ) := by
  rw [norm_pow, norm_inv, Padic.norm_p, inv_inv, zpow_natCast]

/- English proof (translation)
Conclude with `hp.1.one_lt` after adjusting the coercions.
-/
lemma one_lt_p : (1 : ℝ) < p := by exact_mod_cast hp.1.one_lt

end Norms

section Main

variable {p : ℕ} [hp : Fact p.Prime]

def W (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop :=
  ∀ y n : ℕ, n ≤ y →
    ‖(U p g ^ y).coeff (p ^ g * n)‖ ≤ (p : ℝ) ^ ((n : ℤ) - padicValNat p (y.choose n))

def K (p : ℕ) [Fact p.Prime] (g : ℕ) : Prop :=
  ∀ r n : ℕ, r < n →
    ‖((U p g - 1) ^ n).coeff (p ^ g * r)‖ ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖((n.choose r : ℕ) : ℚ_[p])‖

/- English proof (translation)
Rewrite using `[← Finset.add_sum_erase s _ hr]`. Establish `hmain : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ = (p : ℝ) ^ (r : ℤ) * ‖a r‖`. Rewrite using `[Z_pow_top, norm_mul, norm_pinv_pow]`. Establish `har' : 0 < ‖a r‖` using `norm_pos_iff.mpr har`. Establish `hrest : ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖`.

Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)` to reduce the goal to its premises. Introduce `n hn`. Establish `hnr : n ≠ r` using `Finset.ne_of_mem_erase hn`. Rewrite using `[norm_mul]`. Break down `lt_or_gt_of_ne hnr with hlt | hgt` into its components or cases.

Rewrite using `[Z_pow_lt g r n hlt, norm_zero, zero_mul]`. Check the signs of the components of the expression. Combine the equalities or inequalities in the displayed calculation. Establish `hlt : (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ < (p : ℝ) ^ (r : ℤ) * ‖a r‖` using `by gcongr`. Conclude with `one_lt_p`.

Use linear arithmetic over natural numbers and integers. Establish `hne : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ ≠ ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖`. Rewrite using `[hmain]`. Conclude with `(lt_of_le_of_lt hrest hlt).ne'`. Rewrite using `[Padic.add_eq_max_of_ne hne, hmain]`.

Conclude with `max_eq_left (hrest.trans hlt.le)`.
-/
lemma core (g : ℕ) (hK : K p g) (r : ℕ) (s : Finset ℕ) (hr : r ∈ s) (a : ℕ → ℚ_[p])
    (ha : ∀ n, r < n → ‖a n‖ * ‖((n.choose r : ℕ) : ℚ_[p])‖ ≤ ‖a r‖) (har : a r ≠ 0) :
    ‖∑ n ∈ s, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ = (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
  rw [← Finset.add_sum_erase s _ hr]
  have hmain : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ = (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
    rw [Z_pow_top, norm_mul, norm_pinv_pow]
  have har' : 0 < ‖a r‖ := norm_pos_iff.mpr har
  have hrest : ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ ≤
      (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
    intro n hn
    have hnr : n ≠ r := Finset.ne_of_mem_erase hn
    rw [norm_mul]
    rcases lt_or_gt_of_ne hnr with hlt | hgt
    · rw [Z_pow_lt g r n hlt, norm_zero, zero_mul]; positivity
    · calc ‖((U p g - 1) ^ n).coeff (p ^ g * r)‖ * ‖a n‖
          ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖((n.choose r : ℕ) : ℚ_[p])‖ * ‖a n‖ := by
            gcongr; exact hK r n hgt
        _ = (p : ℝ) ^ ((r : ℤ) - 1) * (‖a n‖ * ‖((n.choose r : ℕ) : ℚ_[p])‖) := by ring
        _ ≤ (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ := by gcongr; exact ha n hgt
  have hlt : (p : ℝ) ^ ((r : ℤ) - 1) * ‖a r‖ < (p : ℝ) ^ (r : ℤ) * ‖a r‖ := by
    gcongr
    · exact one_lt_p
    · omega
  have hne : ‖((U p g - 1) ^ r).coeff (p ^ g * r) * a r‖ ≠
      ‖∑ n ∈ s.erase r, ((U p g - 1) ^ n).coeff (p ^ g * r) * a n‖ := by
    rw [hmain]; exact (lt_of_le_of_lt hrest hlt).ne'
  rw [Padic.add_eq_max_of_ne hne, hmain]
  exact max_eq_left (hrest.trans hlt.le)

end Main

end CSOddG

end Formalism.CL
