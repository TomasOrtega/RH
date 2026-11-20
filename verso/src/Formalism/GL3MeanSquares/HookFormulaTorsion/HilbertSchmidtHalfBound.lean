import Mathlib
import Formalism.GL3MeanSquares.QuadraticFormLowerBound

namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

section A
open Finset

/- English proof (translation)
Unfold `VolumeDependsOnSumOfRecurrence`. Introduce `vol ρ h1 h2 P Q hP`. Proceed by induction on `Q generalizing P with`. Consider the case `zero => simp`. Consider the case `succ Q ih`.

Rewrite using `[h2 P Q (by omega), ih P hP]`. Establish `h3` using `h1 (P + Q) 0 (by omega)`. Simplify using `only [Nat.add_zero] at h3`. Rewrite using `[show P + (Q + 1) = P + Q + 1 by omega, h3]`.
-/
theorem t2vol : VolumeDependsOnSumOfRecurrence := by
  unfold VolumeDependsOnSumOfRecurrence
  intro vol ρ h1 h2 P Q hP
  induction Q generalizing P with
  | zero => simp
  | succ Q ih =>
    rw [h2 P Q (by omega), ih P hP]
    have h3 := h1 (P + Q) 0 (by omega)
    simp only [Nat.add_zero] at h3
    rw [show P + (Q + 1) = P + Q + 1 by omega, h3]

/- English proof (translation)
Unfold `CumulantUpperBound`. Introduce `ι _ P y hP hsum hmean hy`. Establish `hpos : 0 < ∑ j, P j * Real.exp (y j)`. Establish `h1 : ∑ j, P j * Real.exp (-1) ≤ ∑ j, P j * Real.exp (y j)` using `Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hy j)).1])) (hP j)`. Rewrite `h1` using `[← Finset.sum_mul, hsum, one_mul]`.

Combine the linear relations using `[Real.exp_pos (-1)]`. Establish `hle : ∑ j, P j * Real.exp (y j) ≤ ∑ j, P j * (1 + y j + y j ^ 2)` using `Finset.sum_le_sum fun j _ => by`. Establish `h2` using `Real.abs_exp_sub_one_sub_id_le (hy j)`. Conclude with `mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h2).2]) (hP j)`. Establish `hexp : ∑ j, P j * (1 + y j + y j ^ 2) = ∑ j, P j + ∑ j, P j * y j + ∑ j, P j * y j ^ 2`.

Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `hlog` using `Real.log_le_sub_one_of_pos hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cumU : CumulantUpperBound := by
  unfold CumulantUpperBound
  intro ι _ P y hP hsum hmean hy
  have hpos : 0 < ∑ j, P j * Real.exp (y j) := by
    have h1 : ∑ j, P j * Real.exp (-1) ≤ ∑ j, P j * Real.exp (y j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hy j)).1])) (hP j)
    rw [← Finset.sum_mul, hsum, one_mul] at h1
    linarith [Real.exp_pos (-1)]
  have hle : ∑ j, P j * Real.exp (y j) ≤ ∑ j, P j * (1 + y j + y j ^ 2) :=
    Finset.sum_le_sum fun j _ => by
      have h2 := Real.abs_exp_sub_one_sub_id_le (hy j)
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h2).2]) (hP j)
  have hexp : ∑ j, P j * (1 + y j + y j ^ 2) = ∑ j, P j + ∑ j, P j * y j + ∑ j, P j * y j ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith

/- English proof (translation)
Unfold `DecayExponentLowerBound`. Introduce `C hC`. Use `⟨3, 2 * C + 2, by norm_num, by linarith, ?_⟩` and prove the remaining obligations. Introduce `C₁ C₂ h1 h2 p q ε₀ Q₀ hp hq he0 he1 hQ`. Simplify using `only`.

Move the coercions through the operations in `at hQ ⊢`. Establish `hpR : (1:ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hqR : (1:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hpq : (1:ℝ) ≤ (p:ℝ) * q` using `by nlinarith`. Establish `hC2 : 0 < C₂` using `by linarith`.

Establish `hN : (2:ℝ) ≤ 2 * (p:ℝ) * q` using `by nlinarith`. Establish `hL : 2 / 3 < Real.log (2 * (p:ℝ) * q)`. Establish `h2l : Real.log 2 ≤ Real.log (2 * (p:ℝ) * q)` using `Real.log_le_log (by norm_num) hN`. Establish `h3` using `Real.log_two_gt_d9`. Establish `h4 : (2:ℝ) / 3 < 0.6931471803` using `by norm_num`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hNL : 0 ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)`. Apply the tactic sequence `apply mul_nonneg <;> linarith`. Establish `e1 : 3 * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)) ≤ C₁ * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q))` using `mul_le_mul_of_nonneg_right h1 hNL`. Establish `e2 : 2 * (p:ℝ) * q * (2 / 3) ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)` using `mul_le_mul_of_nonneg_left hL.le (by linarith)`.

Establish `hQ2 : 4 * ((p:ℝ) * q) ≤ Q₀` using `by linarith`. Use `⟨?_, by linarith⟩` and prove the remaining obligations. Use `set ε := ε₀ / (C₂ * ((p:ℝ) * q)) with hε`. Establish `hD : 0 < C₂ * ((p:ℝ) * q)` using `mul_pos hC2 (by linarith)`. Establish `hε0 : 0 < ε` using `div_pos he0 hD`.

Establish `hεm : ε * (C₂ * ((p:ℝ) * q)) = ε₀`. Rewrite using `[hε, div_mul_eq_mul_div, mul_div_assoc, div_self hD.ne', mul_one]`. Establish `a1 : ε * C₂ ≤ ε * C₂ * ((p:ℝ) * q)` using `le_mul_of_one_le_right (mul_pos hε0 hC2).le hpq`. Establish `a0 : C * ε ≤ (C₂ / 2) * ε` using `mul_le_mul_of_nonneg_right (by linarith) hε0.le`. Establish `a2 : C * ε ≤ 1 / 4` using `by linarith`.

Establish `b1 : C * ε * Q₀ ≤ 1 / 4 * Q₀` using `mul_le_mul_of_nonneg_right a2 (by linarith)`. Establish `c1 : (p:ℝ) + q ≤ 2 * ((p:ℝ) * q)`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]`. Establish `c2` using `mul_le_mul_of_nonneg_right c1 hε0.le`. Establish `c3 : 2 * ((p:ℝ) * q * ε) ≤ C₂ * ((p:ℝ) * q * ε)` using `mul_le_mul_of_nonneg_right (by linarith) (mul_pos (by linarith) hε0).le`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem alphaT : DecayExponentLowerBound := by
  unfold DecayExponentLowerBound
  intro C hC
  refine ⟨3, 2 * C + 2, by norm_num, by linarith, ?_⟩
  intro C₁ C₂ h1 h2 p q ε₀ Q₀ hp hq he0 he1 hQ
  dsimp only
  push_cast at hQ ⊢
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hpq : (1:ℝ) ≤ (p:ℝ) * q := by nlinarith
  have hC2 : 0 < C₂ := by linarith
  have hN : (2:ℝ) ≤ 2 * (p:ℝ) * q := by nlinarith
  have hL : 2 / 3 < Real.log (2 * (p:ℝ) * q) := by
    have h2l : Real.log 2 ≤ Real.log (2 * (p:ℝ) * q) := Real.log_le_log (by norm_num) hN
    have h3 := Real.log_two_gt_d9
    have h4 : (2:ℝ) / 3 < 0.6931471803 := by norm_num
    linarith
  have hNL : 0 ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q) := by
    apply mul_nonneg <;> linarith
  have e1 : 3 * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)) ≤
      C₁ * (2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q)) := mul_le_mul_of_nonneg_right h1 hNL
  have e2 : 2 * (p:ℝ) * q * (2 / 3) ≤ 2 * (p:ℝ) * q * Real.log (2 * (p:ℝ) * q) :=
    mul_le_mul_of_nonneg_left hL.le (by linarith)
  have hQ2 : 4 * ((p:ℝ) * q) ≤ Q₀ := by linarith
  refine ⟨?_, by linarith⟩
  set ε := ε₀ / (C₂ * ((p:ℝ) * q)) with hε
  have hD : 0 < C₂ * ((p:ℝ) * q) := mul_pos hC2 (by linarith)
  have hε0 : 0 < ε := div_pos he0 hD
  have hεm : ε * (C₂ * ((p:ℝ) * q)) = ε₀ := by
    rw [hε, div_mul_eq_mul_div, mul_div_assoc, div_self hD.ne', mul_one]
  have a1 : ε * C₂ ≤ ε * C₂ * ((p:ℝ) * q) := le_mul_of_one_le_right (mul_pos hε0 hC2).le hpq
  have a0 : C * ε ≤ (C₂ / 2) * ε := mul_le_mul_of_nonneg_right (by linarith) hε0.le
  have a2 : C * ε ≤ 1 / 4 := by linarith
  have b1 : C * ε * Q₀ ≤ 1 / 4 * Q₀ := mul_le_mul_of_nonneg_right a2 (by linarith)
  have c1 : (p:ℝ) + q ≤ 2 * ((p:ℝ) * q) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]
  have c2 := mul_le_mul_of_nonneg_right c1 hε0.le
  have c3 : 2 * ((p:ℝ) * q * ε) ≤ C₂ * ((p:ℝ) * q * ε) :=
    mul_le_mul_of_nonneg_right (by linarith) (mul_pos (by linarith) hε0).le
  linarith

end A

section B
open Finset
open scoped ComplexOrder

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound`. Introduce `d A hA`. Establish `hdiag : ∀ i, (1:ℝ) / 4 ≤ ‖A i i‖ ^ 2`. Introduce `i`. Establish `h0` using `(Complex.le_def.1 (hA.diag_nonneg (i := i))).1`.

Simplify using `[Matrix.sub_apply, Matrix.one_apply] at h0`. Establish `hn` using `Complex.re_le_norm (A i i)`. Establish `h1 : 1 / 2 ≤ ‖A i i‖` using `by linarith`. Use polynomial arithmetic with `[h1]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_le_sum fun i _ => hdiag i`. Use `_ ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)`.
-/
theorem hsHalf : Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.HilbertSchmidtHalfBound
  intro d A hA
  have hdiag : ∀ i, (1:ℝ) / 4 ≤ ‖A i i‖ ^ 2 := by
    intro i
    have h0 := (Complex.le_def.1 (hA.diag_nonneg (i := i))).1
    simp [Matrix.sub_apply, Matrix.one_apply] at h0
    have hn := Complex.re_le_norm (A i i)
    have h1 : 1 / 2 ≤ ‖A i i‖ := by linarith
    nlinarith [h1]
  calc (d : ℝ) / 4 = ∑ _i : Fin d, (1:ℝ) / 4 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_le_sum fun i _ => hdiag i
    _ ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := Finset.sum_le_sum fun i _ =>
        Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)

end B

section C
open Finset MeasureTheory
open scoped ComplexOrder

/- English proof (translation)
Establish `split : ∀ a b, f a b = (if b < a then f a b else 0) + (if a < b then f a b else 0)`. Introduce `a b`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, lt_asymm h]`. Substitute `h` using the available equality.

Simplify using `[h0 a a rfl]`. Simplify using `[h, lt_asymm h]`. Establish `swap : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ a, ∑ b, (if b < a then f a b else 0)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Rewrite using `[hs]`. Establish `filt : ∀ a, ∑ b, (if b < a then f a b else 0) = ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b`. Introduce `a`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `by_cases hb : b < a <;> by_cases hsg : sg a = sg b <;> simp [hb, hsg, h0 a b]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun b _ => split a b`. Use `_ = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by`. Rewrite using `[swap, ← two_mul]`. Simplify using `only [filt]`.
-/
lemma halfSum (N : ℕ) (sg : Fin N → Bool) (f : Fin N → Fin N → ℝ)
    (hs : ∀ a b, f a b = f b a) (h0 : ∀ a b, sg a = sg b → f a b = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
  have split : ∀ a b, f a b = (if b < a then f a b else 0) + (if a < b then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      simp [h0 a a rfl]
    · simp [h, lt_asymm h]
  have swap : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ a, ∑ b, (if b < a then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs]
  have filt : ∀ a, ∑ b, (if b < a then f a b else 0) =
      ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
    intro a
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b < a <;> by_cases hsg : sg a = sg b <;> simp [hb, hsg, h0 a b]
  calc ∑ a, ∑ b, f a b = ∑ a, ∑ b, (if b < a then f a b else 0) +
        ∑ a, ∑ b, (if a < b then f a b else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => split a b
    _ = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
        rw [swap, ← two_mul]
        simp only [filt]

/- English proof (translation)
Rewrite using `[← hX.apply a b, norm_star]`.
-/
lemma normSymm (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ) (hX : X.IsHermitian) (a b : Fin N) :
    ‖X a b‖ ^ 2 = ‖X b a‖ ^ 2 := by
  rw [← hX.apply a b, norm_star]

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound`. Introduce `N lam sg X h₀ hX hz hgap`. Rewrite using `[halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b) (fun a b h => by simp [hz a b h])]`. Rewrite using `[show ∀ S : ℝ, h₀ * (2 * S) / 2 = h₀ * S from fun S => by ring, Finset.mul_sum]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun b hb => ?_` and prove the remaining obligations. Take `⟨hlt, hne⟩` from `(Finset.mem_filter.1 hb).2`. Establish `h1` using `hgap a b hlt hne`. Establish `h2 : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ)` using `by exact_mod_cast hlt`.

Conclude with `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`.
-/
theorem qLower : Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound
  intro N lam sg X h₀ hX hz hgap
  rw [halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b)
    (fun a b h => by simp [hz a b h])]
  rw [show ∀ S : ℝ, h₀ * (2 * S) / 2 = h₀ * S from fun S => by ring, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨hlt, hne⟩ := (Finset.mem_filter.1 hb).2
  have h1 := hgap a b hlt hne
  have h2 : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast hlt
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound`. Introduce `N lam sg X lamAbs hX hz hbd`. Rewrite using `[halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b) (fun a b h => by simp [hz a b h])]`. Rewrite using `[show ∀ S : ℝ, (lamAbs + N) * (2 * S) / 2 = (lamAbs + N) * S from fun S => by ring, Finset.mul_sum]`. Use `Finset.sum_le_sum fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun b _ => ?_` and prove the remaining obligations. Establish `h1` using `le_trans (le_abs_self (lam b - lam a)) (hbd b a)`. Establish `h2 : ((a : ℕ) : ℝ) < N` using `by exact_mod_cast a.isLt`. Establish `h3 : (0 : ℝ) ≤ ((b : ℕ) : ℝ)` using `Nat.cast_nonneg _`.

Conclude with `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`.
-/
theorem qUpper : Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound
  intro N lam sg X lamAbs hX hz hbd
  rw [halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b)
    (fun a b h => by simp [hz a b h])]
  rw [show ∀ S : ℝ, (lamAbs + N) * (2 * S) / 2 = (lamAbs + N) * S from fun S => by ring,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 := le_trans (le_abs_self (lam b - lam a)) (hbd b a)
  have h2 : ((a : ℕ) : ℝ) < N := by exact_mod_cast a.isLt
  have h3 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay`. Introduce `n t₀ α Q₀ hn ht hnα hQα`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Simplify using `only [Nat.add_sub_cancel]`. Move the coercions through the operations in `at hnα`.

Establish `ha : -t₀⁻¹ < 0` using `neg_lt_zero.2 (inv_pos.2 ht)`. Establish `hK0 : 0 ≤ t₀ ^ m * Real.exp (1 - α)` using `by positivity`. Establish `hgI : IntegrableOn (fun t => t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t)) (Set.Ioi t₀)` using `(integrableOn_exp_mul_Ioi ha t₀).const_mul _`. Establish `hbound : ∀ t ∈ Set.Ioi t₀, t ^ m * Real.exp (-(α * (t / t₀))) ≤ t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t)`. Introduce `t ht'`.

Establish `htt : t₀ < t` using `ht'`. Take `⟨s, hs⟩ : ∃ s, s = t / t₀` from `⟨_, rfl⟩`. Establish `hs1 : 1 ≤ s` using `by rw [hs]; exact (one_le_div ht).2 htt.le`. Establish `hts : t = t₀ * s` using `by rw [hs]; field_simp`. Establish `e1 : -t₀⁻¹ * t = -s` using `by rw [hts]; field_simp`.

Rewrite using `[← hs, e1, hts, mul_pow]`. Establish `hpow : s ^ m ≤ Real.exp ((m : ℝ) * (s - 1))`. Rewrite using `[Real.exp_nat_mul]`. Establish `hse : s ≤ Real.exp (s - 1)` using `by linarith [Real.add_one_le_exp (s - 1)]`. Use `first`.

Consider the case `exact pow_le_pow_left₀ (by linarith) hse m`. Consider the case `exact pow_le_pow_left (by linarith) hse m`. Establish `hexpo : (m : ℝ) * (s - 1) + -(α * s) ≤ (1 - α) + -s`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hnα (sub_nonneg.2 hs1)]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hfI : IntegrableOn (fun t => t ^ m * Real.exp (-(α * (t / t₀)))) (Set.Ioi t₀)`. Use `Integrable.mono' hgI (Continuous.aestronglyMeasurable (by fun_prop)) ?_` and prove the remaining obligations. Use `(ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht' => ?_)` and prove the remaining obligations. Establish `htp : 0 < t` using `lt_trans ht ht'`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.

Conclude with `hbound t ht'`. Use `⟨hfI, ?_⟩` and prove the remaining obligations. Establish `hx : Real.exp (1 - α) * Real.exp (-1) = Real.exp (-α)`. Rewrite using `[← Real.exp_add]`. Put the polynomial expressions in normal form.

Establish `hc : -t₀⁻¹ * t₀ = -1` using `by field_simp`. Combine the equalities or inequalities in the displayed calculation. Consider the case `rw [integral_const_mul, integral_exp_mul_Ioi ha]`. Consider the case `rw [integral_mul_const, integral_exp_mul_Ioi ha]`. Use `_ = t₀ ^ m * t₀ * (Real.exp (1 - α) * Real.exp (-1)) := by`.

Rewrite using `[hc, neg_div_neg_eq, div_inv_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = t₀ ^ (m + 1) * Real.exp (-α) := by rw [hx, pow_succ]`. Use `_ ≤ t₀ ^ (m + 1) * Real.exp (-(Q₀ / 2)) := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)`.
-/
theorem tailRay : Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.TailAlongRay
  intro n t₀ α Q₀ hn ht hnα hQα
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  push_cast at hnα
  have ha : -t₀⁻¹ < 0 := neg_lt_zero.2 (inv_pos.2 ht)
  have hK0 : 0 ≤ t₀ ^ m * Real.exp (1 - α) := by positivity
  have hgI : IntegrableOn (fun t => t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t)) (Set.Ioi t₀) :=
    (integrableOn_exp_mul_Ioi ha t₀).const_mul _
  have hbound : ∀ t ∈ Set.Ioi t₀, t ^ m * Real.exp (-(α * (t / t₀))) ≤
      t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t) := by
    intro t ht'
    have htt : t₀ < t := ht'
    obtain ⟨s, hs⟩ : ∃ s, s = t / t₀ := ⟨_, rfl⟩
    have hs1 : 1 ≤ s := by rw [hs]; exact (one_le_div ht).2 htt.le
    have hts : t = t₀ * s := by rw [hs]; field_simp
    have e1 : -t₀⁻¹ * t = -s := by rw [hts]; field_simp
    rw [← hs, e1, hts, mul_pow]
    have hpow : s ^ m ≤ Real.exp ((m : ℝ) * (s - 1)) := by
      rw [Real.exp_nat_mul]
      have hse : s ≤ Real.exp (s - 1) := by linarith [Real.add_one_le_exp (s - 1)]
      first
        | exact pow_le_pow_left₀ (by linarith) hse m
        | exact pow_le_pow_left (by linarith) hse m
    have hexpo : (m : ℝ) * (s - 1) + -(α * s) ≤ (1 - α) + -s := by
      nlinarith [mul_le_mul_of_nonneg_right hnα (sub_nonneg.2 hs1)]
    calc t₀ ^ m * s ^ m * Real.exp (-(α * s))
        ≤ t₀ ^ m * Real.exp ((m : ℝ) * (s - 1)) * Real.exp (-(α * s)) := by gcongr
      _ = t₀ ^ m * Real.exp ((m : ℝ) * (s - 1) + -(α * s)) := by rw [Real.exp_add]; ring
      _ ≤ t₀ ^ m * Real.exp ((1 - α) + -s) := by gcongr
      _ = t₀ ^ m * Real.exp (1 - α) * Real.exp (-s) := by rw [Real.exp_add]; ring
  have hfI : IntegrableOn (fun t => t ^ m * Real.exp (-(α * (t / t₀)))) (Set.Ioi t₀) := by
    refine Integrable.mono' hgI (Continuous.aestronglyMeasurable (by fun_prop)) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht' => ?_)
    have htp : 0 < t := lt_trans ht ht'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t ht'
  refine ⟨hfI, ?_⟩
  have hx : Real.exp (1 - α) * Real.exp (-1) = Real.exp (-α) := by
    rw [← Real.exp_add]
    ring_nf
  have hc : -t₀⁻¹ * t₀ = -1 := by field_simp
  calc ∫ t in Set.Ioi t₀, t ^ m * Real.exp (-(α * (t / t₀)))
      ≤ ∫ t in Set.Ioi t₀, t₀ ^ m * Real.exp (1 - α) * Real.exp (-t₀⁻¹ * t) :=
        setIntegral_mono_on hfI hgI measurableSet_Ioi hbound
    _ = t₀ ^ m * Real.exp (1 - α) * (-Real.exp (-t₀⁻¹ * t₀) / -t₀⁻¹) := by
        first
          | rw [integral_const_mul, integral_exp_mul_Ioi ha]
          | rw [integral_mul_const, integral_exp_mul_Ioi ha]
    _ = t₀ ^ m * t₀ * (Real.exp (1 - α) * Real.exp (-1)) := by
        rw [hc, neg_div_neg_eq, div_inv_eq_mul]
        ring
    _ = t₀ ^ (m + 1) * Real.exp (-α) := by rw [hx, pow_succ]
    _ ≤ t₀ ^ (m + 1) * Real.exp (-(Q₀ / 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (by positivity)

/- English proof (translation)
Distinguish the cases in `hp2 : 2 ≤ p`. Establish `h1 : p * 1 ≤ p * q` using `Nat.mul_le_mul le_rfl hq`. Establish `h2 : 2 * q ≤ p * q` using `Nat.mul_le_mul hp2 le_rfl`. Use the polynomial consequences of the given equalities and inequalities. Establish `hp1 : p = 1` using `by omega`.

Substitute `hp1` using the available equality. Use linear arithmetic over natural numbers and integers.
-/
lemma natIneq (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : ¬ (p = 1 ∧ q = 1)) :
    p + q + 1 ≤ 2 * p * q := by
  by_cases hp2 : 2 ≤ p
  · have h1 : p * 1 ≤ p * q := Nat.mul_le_mul le_rfl hq
    have h2 : 2 * q ≤ p * q := Nat.mul_le_mul hp2 le_rfl
    nlinarith
  · have hp1 : p = 1 := by omega
    subst hp1
    omega

set_option maxHeartbeats 800000 in

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound`. Introduce `C' hC'`. Use `⟨8 * C' + 1, by linarith, ?_⟩` and prove the remaining obligations. Introduce `C'' hC'' p q ε₀ hp hq hexp he1`. Move the coercions through the operations in `at hexp ⊢`.

Establish `hpR : (1:ℝ) ≤ p` using `by exact_mod_cast hp`. Establish `hqR : (1:ℝ) ≤ q` using `by exact_mod_cast hq`. Establish `hM : (1:ℝ) ≤ (p:ℝ) * q` using `by nlinarith`. Establish `hε0 : 0 < ε₀` using `lt_of_lt_of_le (Real.exp_pos _) hexp`. Establish `hCpos : 0 < C''` using `by linarith`.

Take `⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C' * (ε₀ / (C'' * ((p:ℝ) * q)))` from `⟨_, rfl⟩`. Rewrite using `[← hδ]`. Establish `hCi : C'' * C''⁻¹ = 1` using `mul_inv_cancel₀ hCpos.ne'`. Establish `hMi : ((p:ℝ) * q) * ((p:ℝ) * q)⁻¹ = 1` using `mul_inv_cancel₀ (by linarith)`. Establish `hCi0 : 0 < C''⁻¹` using `inv_pos.2 hCpos`.

Establish `hMi0 : 0 < ((p:ℝ) * q)⁻¹` using `inv_pos.2 (by linarith)`. Establish `hδ' : δ = C' * ε₀ * C''⁻¹ * ((p:ℝ) * q)⁻¹`. Rewrite using `[hδ, div_eq_mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `k1 : 8 * C' * C''⁻¹ ≤ C'' * C''⁻¹` using `mul_le_mul_of_nonneg_right (by linarith) hCi0.le`.

Establish `hMδ : ((p:ℝ) * q) * δ = C' * C''⁻¹ * ε₀`. Rewrite using `[hδ']`. Take the linear combination `(C' * ε₀ * C''⁻¹) * hMi`. Establish `k2` using `mul_le_mul_of_nonneg_right k1 hε0.le`. Establish `k2' : C'' * C''⁻¹ * ε₀ = ε₀` using `by rw [hCi, one_mul]`.

Establish `hMδ8 : ((p:ℝ) * q) * δ ≤ ε₀ / 8` using `by linarith`. Establish `hδ0 : 0 ≤ δ`. Rewrite using `[hδ']`. Conclude with `mul_nonneg (mul_nonneg (mul_nonneg hC' hε0.le) hCi0.le) hMi0.le`. Establish `hδ1 : δ ≤ ε₀ / 8` using `by linarith [mul_le_mul_of_nonneg_right hM hδ0]`.

Use `⟨by linarith, ?_⟩` and prove the remaining obligations. Establish `hb` using `one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) (p * q)`. Move the coercions through the operations in `at hb`. Rewrite `hb` using `[← sub_eq_add_neg]`. Take `⟨Y, hY⟩ : ∃ Y : ℝ, Y = (1 - δ) ^ (p * q)` from `⟨_, rfl⟩`.

Rewrite using `[inv_pow, ← hY]`. Rewrite `hb` using `[← hY]`. Establish `hYlow : 1 - ε₀ / 8 ≤ Y` using `by linarith`. Establish `hY1 : Y ≤ 1`. Rewrite using `[hY]`.

Use `first`. Consider the case `exact pow_le_one₀ (by linarith) (by linarith)`. Consider the case `exact pow_le_one _ (by linarith) (by linarith)`. Establish `hYpos : 0 < Y` using `by linarith`. Establish `hU : (1 - ε₀) * (1 - ε₀)⁻¹ = 1` using `mul_inv_cancel₀ (by linarith)`.

Establish `hV : Y * Y⁻¹ = 1` using `mul_inv_cancel₀ hYpos.ne'`. Establish `hU0 : 0 < (1 - ε₀)⁻¹` using `inv_pos.2 (by linarith)`. Establish `hV0 : 0 < Y⁻¹` using `inv_pos.2 hYpos`. Establish `hU1 : 1 ≤ (1 - ε₀)⁻¹` using `by linarith [mul_pos hε0 hU0]`. Establish `hV1 : 1 ≤ Y⁻¹` using `by linarith [mul_nonneg (sub_nonneg.2 hY1) hV0.le]`.

Establish `hUV : (1 - ε₀)⁻¹ - Y⁻¹ = (1 - ε₀)⁻¹ * Y⁻¹ * (Y - (1 - ε₀))`. Take the linear combination `(-(1 - ε₀)⁻¹) * hV + Y⁻¹ * hU`. Establish `hY7 : 7 * ε₀ / 8 ≤ Y - (1 - ε₀)` using `by linarith`. Establish `hUV0 : 0 ≤ (1 - ε₀)⁻¹ * Y⁻¹` using `(mul_pos hU0 hV0).le`. Establish `key` using `mul_le_mul_of_nonneg_left hY7 hUV0`.

Establish `hUV1 : 1 * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹` using `mul_le_mul hU1 hV1 zero_le_one hU0.le`. Establish `hE0 : Real.exp (-(2 * (p:ℝ) * q)) ≤ ε₀`. Use `le_trans (Real.exp_le_exp.2 ?_) hexp` and prove the remaining obligations. Combine the linear relations using `[mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]`. Distinguish the cases in `h11 : p = 1 ∧ q = 1`.

Take `⟨hp1, hq1⟩` from `h11`. Establish `hp1' : (p:ℝ) = 1` using `by exact_mod_cast hp1`. Establish `hq1' : (q:ℝ) = 1` using `by exact_mod_cast hq1`. Rewrite `hexp` using `[hp1', hq1']`. Establish `he2 : Real.exp 2 ≤ 8`.

Establish `h` using `Real.exp_one_lt_d9`. Establish `h' : Real.exp 2 = Real.exp 1 * Real.exp 1`. Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions. Rewrite using `[h']`.

Establish `h3 : Real.exp 1 ≤ 2.72` using `by linarith`. Combine the equalities or inequalities in the displayed calculation. Establish `hm2 : Real.exp (-2) * Real.exp 2 = 1`. Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions.

Establish `hε8 : 1 / 8 ≤ ε₀`. Establish `: Real.exp (-(1 + 1)) = Real.exp (-2)` using `by norm_num`. Rewrite `hexp` using `[this]`. Establish `h5` using `mul_le_mul_of_nonneg_left he2 (Real.exp_pos (-2)).le`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hU8 : 8 / 7 ≤ (1 - ε₀)⁻¹`. Combine the linear relations using `[mul_le_mul_of_nonneg_right hε8 hU0.le]`. Establish `hUVb : (1 - ε₀)⁻¹ * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹` using `mul_le_mul_of_nonneg_left hV1 hU0.le`. Establish `k3` using `mul_le_mul_of_nonneg_right (show 8 / 7 ≤ (1 - ε₀)⁻¹ * Y⁻¹ by linarith) (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hnat` using `natIneq p q hp hq h11`. Establish `hreal : (p:ℝ) + q + 1 ≤ 2 * p * q` using `by exact_mod_cast hnat`. Establish `hE1 : Real.exp (-(2 * (p:ℝ) * q)) ≤ Real.exp (-((p:ℝ) + q) + -1)` using `Real.exp_le_exp.2 (by linarith)`. Rewrite `hE1` using `[Real.exp_add]`. Establish `hx : Real.exp (-1) * Real.exp 1 = 1`.

Rewrite using `[← Real.exp_add]`. Evaluate the numerical expressions. Establish `h2 : 2 ≤ Real.exp 1` using `by linarith [Real.add_one_le_exp (1:ℝ)]`. Establish `hm1 : Real.exp (-1) ≤ 1 / 2` using `by linarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-1)).le]`. Establish `hE2 : Real.exp (-((p:ℝ) + q)) * Real.exp (-1) ≤ ε₀ * (1 / 2)` using `mul_le_mul hexp hm1 (Real.exp_pos _).le hε0.le`.

Establish `k4` using `mul_le_mul_of_nonneg_right hUV1 (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zBound : Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound
  intro C' hC'
  refine ⟨8 * C' + 1, by linarith, ?_⟩
  intro C'' hC'' p q ε₀ hp hq hexp he1
  push_cast at hexp ⊢
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hM : (1:ℝ) ≤ (p:ℝ) * q := by nlinarith
  have hε0 : 0 < ε₀ := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hCpos : 0 < C'' := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C' * (ε₀ / (C'' * ((p:ℝ) * q))) := ⟨_, rfl⟩
  rw [← hδ]
  have hCi : C'' * C''⁻¹ = 1 := mul_inv_cancel₀ hCpos.ne'
  have hMi : ((p:ℝ) * q) * ((p:ℝ) * q)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hCi0 : 0 < C''⁻¹ := inv_pos.2 hCpos
  have hMi0 : 0 < ((p:ℝ) * q)⁻¹ := inv_pos.2 (by linarith)
  have hδ' : δ = C' * ε₀ * C''⁻¹ * ((p:ℝ) * q)⁻¹ := by
    rw [hδ, div_eq_mul_inv, mul_inv]
    ring
  have k1 : 8 * C' * C''⁻¹ ≤ C'' * C''⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hCi0.le
  have hMδ : ((p:ℝ) * q) * δ = C' * C''⁻¹ * ε₀ := by
    rw [hδ']
    linear_combination (C' * ε₀ * C''⁻¹) * hMi
  have k2 := mul_le_mul_of_nonneg_right k1 hε0.le
  have k2' : C'' * C''⁻¹ * ε₀ = ε₀ := by rw [hCi, one_mul]
  have hMδ8 : ((p:ℝ) * q) * δ ≤ ε₀ / 8 := by linarith
  have hδ0 : 0 ≤ δ := by
    rw [hδ']
    exact mul_nonneg (mul_nonneg (mul_nonneg hC' hε0.le) hCi0.le) hMi0.le
  have hδ1 : δ ≤ ε₀ / 8 := by linarith [mul_le_mul_of_nonneg_right hM hδ0]
  refine ⟨by linarith, ?_⟩
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) (p * q)
  push_cast at hb
  rw [← sub_eq_add_neg] at hb
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (1 - δ) ^ (p * q) := ⟨_, rfl⟩
  rw [inv_pow, ← hY]
  rw [← hY] at hb
  have hYlow : 1 - ε₀ / 8 ≤ Y := by linarith
  have hY1 : Y ≤ 1 := by
    rw [hY]
    first
      | exact pow_le_one₀ (by linarith) (by linarith)
      | exact pow_le_one _ (by linarith) (by linarith)
  have hYpos : 0 < Y := by linarith
  have hU : (1 - ε₀) * (1 - ε₀)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hV : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hYpos.ne'
  have hU0 : 0 < (1 - ε₀)⁻¹ := inv_pos.2 (by linarith)
  have hV0 : 0 < Y⁻¹ := inv_pos.2 hYpos
  have hU1 : 1 ≤ (1 - ε₀)⁻¹ := by linarith [mul_pos hε0 hU0]
  have hV1 : 1 ≤ Y⁻¹ := by linarith [mul_nonneg (sub_nonneg.2 hY1) hV0.le]
  have hUV : (1 - ε₀)⁻¹ - Y⁻¹ = (1 - ε₀)⁻¹ * Y⁻¹ * (Y - (1 - ε₀)) := by
    linear_combination (-(1 - ε₀)⁻¹) * hV + Y⁻¹ * hU
  have hY7 : 7 * ε₀ / 8 ≤ Y - (1 - ε₀) := by linarith
  have hUV0 : 0 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := (mul_pos hU0 hV0).le
  have key := mul_le_mul_of_nonneg_left hY7 hUV0
  have hUV1 : 1 * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul hU1 hV1 zero_le_one hU0.le
  have hE0 : Real.exp (-(2 * (p:ℝ) * q)) ≤ ε₀ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hexp
    linarith [mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]
  by_cases h11 : p = 1 ∧ q = 1
  · obtain ⟨hp1, hq1⟩ := h11
    have hp1' : (p:ℝ) = 1 := by exact_mod_cast hp1
    have hq1' : (q:ℝ) = 1 := by exact_mod_cast hq1
    rw [hp1', hq1'] at hexp
    have he2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [h']
      have h3 : Real.exp 1 ≤ 2.72 := by linarith
      calc Real.exp 1 * Real.exp 1 ≤ 2.72 * 2.72 := mul_le_mul h3 h3 (Real.exp_pos 1).le (by norm_num)
        _ ≤ 8 := by norm_num
    have hm2 : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hε8 : 1 / 8 ≤ ε₀ := by
      have : Real.exp (-(1 + 1)) = Real.exp (-2) := by norm_num
      rw [this] at hexp
      have h5 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (-2)).le
      linarith
    have hU8 : 8 / 7 ≤ (1 - ε₀)⁻¹ := by
      linarith [mul_le_mul_of_nonneg_right hε8 hU0.le]
    have hUVb : (1 - ε₀)⁻¹ * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul_of_nonneg_left hV1 hU0.le
    have k3 := mul_le_mul_of_nonneg_right (show 8 / 7 ≤ (1 - ε₀)⁻¹ * Y⁻¹ by linarith)
      (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith
  · have hnat := natIneq p q hp hq h11
    have hreal : (p:ℝ) + q + 1 ≤ 2 * p * q := by exact_mod_cast hnat
    have hE1 : Real.exp (-(2 * (p:ℝ) * q)) ≤ Real.exp (-((p:ℝ) + q) + -1) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add] at hE1
    have hx : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hm1 : Real.exp (-1) ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-1)).le]
    have hE2 : Real.exp (-((p:ℝ) + q)) * Real.exp (-1) ≤ ε₀ * (1 / 2) :=
      mul_le_mul hexp hm1 (Real.exp_pos _).le hε0.le
    have k4 := mul_le_mul_of_nonneg_right hUV1 (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith

end C

section D
open Finset
open scoped Nat

/- English proof (translation)
Rewrite using `[AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar n), ZMod.card]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem charsumA (n : ℕ) [NeZero n] (t : ZMod n) :
    ∑ b : ZMod n, (ZMod.stdAddChar (b * t) : ℂ) = if t = 0 then (n : ℂ) else 0 := by
  rw [AddChar.sum_mulShift t (ZMod.isPrimitive_stdAddChar n), ZMod.card]
  split_ifs <;> simp

/- English proof (translation)
Use `haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩`. Establish `h1 : ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) = ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ)` using `Fintype.sum_equiv unitsEquivNeZero _ _ (fun c => rfl)`. Establish `h2 : ∑ x ∈ (univ : Finset (ZMod p)).erase 0, (ZMod.stdAddChar (x * t) : ℂ) = ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ)` using `Finset.sum_subtype _ (fun x => by simp) _`. Rewrite using `[h1, ← h2, Finset.sum_erase_eq_sub (mem_univ _), charsumA p t]`. Simplify using `only [zero_mul, AddChar.map_zero_eq_one]`.

Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem charsumB (p : ℕ) [Fact p.Prime] (t : ZMod p) :
    ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) = if t = 0 then (p : ℂ) - 1 else -1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : ∑ c : (ZMod p)ˣ, (ZMod.stdAddChar ((c : ZMod p) * t) : ℂ) =
      ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ) :=
    Fintype.sum_equiv unitsEquivNeZero _ _ (fun c => rfl)
  have h2 : ∑ x ∈ (univ : Finset (ZMod p)).erase 0, (ZMod.stdAddChar (x * t) : ℂ) =
      ∑ x : {a : ZMod p // a ≠ 0}, (ZMod.stdAddChar ((x : ZMod p) * t) : ℂ) :=
    Finset.sum_subtype _ (fun x => by simp) _
  rw [h1, ← h2, Finset.sum_erase_eq_sub (mem_univ _), charsumA p t]
  simp only [zero_mul, AddChar.map_zero_eq_one]
  split_ifs <;> ring

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.SW_hecke_charsums`. Conclude with `⟨fun n inst t => @charsumA n inst t, fun p inst t => @charsumB p inst t⟩`.
-/
theorem charsums : Formalism.HermitianLattices.CumulantEstimateDefs.SW_hecke_charsums := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.SW_hecke_charsums
  exact ⟨fun n inst t => @charsumA n inst t, fun p inst t => @charsumB p inst t⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1 + 1), Nat.factorial_succ (2 * n + 1), Nat.factorial_succ n, pow_succ]`. Establish `h1 : 6 * (n + 1) * (6 ^ n * n !) ≤ 6 * (n + 1) * (2 * n + 1)!` using `Nat.mul_le_mul le_rfl ih`.

Establish `h2 : 6 * (n + 1) ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1)` using `by nlinarith`. Establish `h3` using `Nat.mul_le_mul h2 (le_refl (2 * n + 1)!)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma factIneq (n : ℕ) : 6 ^ n * n ! ≤ (2 * n + 1)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1 + 1),
      Nat.factorial_succ (2 * n + 1), Nat.factorial_succ n, pow_succ]
    have h1 : 6 * (n + 1) * (6 ^ n * n !) ≤ 6 * (n + 1) * (2 * n + 1)! := Nat.mul_le_mul le_rfl ih
    have h2 : 6 * (n + 1) ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) := by nlinarith
    have h3 := Nat.mul_le_mul h2 (le_refl (2 * n + 1)!)
    calc 6 ^ n * 6 * ((n + 1) * n !) = 6 * (n + 1) * (6 ^ n * n !) := by ring
      _ ≤ 6 * (n + 1) * (2 * n + 1)! := h1
      _ ≤ (2 * n + 1 + 1 + 1) * (2 * n + 1 + 1) * (2 * n + 1)! := h3
      _ = (2 * n + 1 + 1 + 1) * ((2 * n + 1 + 1) * (2 * n + 1)!) := by ring

/- English proof (translation)
Establish `hs` using `Real.hasSum_sinh x`. Establish `he : HasSum (fun n : ℕ => (x ^ 2 / 6) ^ n / (n ! : ℝ)) (Real.exp (x ^ 2 / 6))`. Rewrite using `[Real.exp_eq_exp_ℝ]`. Conclude with `NormedSpace.expSeries_div_hasSum_exp (x ^ 2 / 6)`. Establish `hb : HasSum (fun n : ℕ => x * ((x ^ 2 / 6) ^ n / (n ! : ℝ))) (x * Real.exp (x ^ 2 / 6))` using `he.mul_left x`.

Use `hasSum_le (fun n => ?_) hs hb` and prove the remaining obligations. Establish `hf : ((6 ^ n * n ! : ℕ) : ℝ) ≤ ((2 * n + 1)! : ℝ)` using `by exact_mod_cast factIneq n`. Move the coercions through the operations in `at hf`. Establish `hn : (n ! : ℝ) ≠ 0` using `by positivity`. Establish `hpos : (0 : ℝ) < 6 ^ n * n !` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[div_pow]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sinhMid (x : ℝ) (hx : 0 < x) : Real.sinh x ≤ x * Real.exp (x ^ 2 / 6) := by
  have hs := Real.hasSum_sinh x
  have he : HasSum (fun n : ℕ => (x ^ 2 / 6) ^ n / (n ! : ℝ)) (Real.exp (x ^ 2 / 6)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (x ^ 2 / 6)
  have hb : HasSum (fun n : ℕ => x * ((x ^ 2 / 6) ^ n / (n ! : ℝ))) (x * Real.exp (x ^ 2 / 6)) :=
    he.mul_left x
  refine hasSum_le (fun n => ?_) hs hb
  have hf : ((6 ^ n * n ! : ℕ) : ℝ) ≤ ((2 * n + 1)! : ℝ) := by exact_mod_cast factIneq n
  push_cast at hf
  have hn : (n ! : ℝ) ≠ 0 := by positivity
  have hpos : (0 : ℝ) < 6 ^ n * n ! := by positivity
  calc x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) ≤ x ^ (2 * n + 1) / (6 ^ n * n ! : ℝ) := by
        gcongr
    _ = x * ((x ^ 2 / 6) ^ n / (n ! : ℝ)) := by
        rw [div_pow]
        field_simp
        ring

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds`. Introduce `x hx`. Establish `hs` using `Real.hasSum_sinh x`. Establish `hlow : x ≤ Real.sinh x`. Establish `h` using `le_hasSum hs 0 (fun j _ => by positivity)`.

Simplify using `using h`. Establish `hc : HasSum (fun n : ℕ => x * (x ^ (2 * n) / ((2 * n)! : ℝ))) (x * Real.cosh x)` using `(Real.hasSum_cosh x).mul_left x`. Establish `h1 : Real.sinh x ≤ x * Real.cosh x`. Use `hasSum_le (fun n => ?_) hs hc` and prove the remaining obligations. Establish `hfac : ((2 * n)! : ℝ) ≤ ((2 * n + 1)! : ℝ)`.

Conclude with `Nat.factorial_le (by omega)` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ x * (x ^ (2 * n) / ((2 * n)! : ℝ)) := by gcongr`.

Establish `h2 : Real.cosh x ≤ Real.exp x`. Rewrite using `[Real.cosh_eq]`. Use `Real.exp_le_exp.2 (show -x ≤ x by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨hlow, sinhMid x hx, h1.trans (mul_le_mul_of_nonneg_left h2 hx.le)⟩`.
-/
theorem sinhAll : Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.SinhBounds
  intro x hx
  have hs := Real.hasSum_sinh x
  have hlow : x ≤ Real.sinh x := by
    have h := le_hasSum hs 0 (fun j _ => by positivity)
    simpa using h
  have hc : HasSum (fun n : ℕ => x * (x ^ (2 * n) / ((2 * n)! : ℝ))) (x * Real.cosh x) :=
    (Real.hasSum_cosh x).mul_left x
  have h1 : Real.sinh x ≤ x * Real.cosh x := by
    refine hasSum_le (fun n => ?_) hs hc
    have hfac : ((2 * n)! : ℝ) ≤ ((2 * n + 1)! : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    calc x ^ (2 * n + 1) / ((2 * n + 1)! : ℝ) = x * (x ^ (2 * n) / ((2 * n + 1)! : ℝ)) := by
          rw [pow_succ]
          ring
      _ ≤ x * (x ^ (2 * n) / ((2 * n)! : ℝ)) := by
          gcongr
  have h2 : Real.cosh x ≤ Real.exp x := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.2 (show -x ≤ x by linarith)
    linarith
  exact ⟨hlow, sinhMid x hx, h1.trans (mul_le_mul_of_nonneg_left h2 hx.le)⟩

end D

section E
open Finset Matrix Unitary

/- English proof (translation)
Introduce `N X hX`. Establish `hsq : ∑ i, (hX.eigenvalues i) ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2`. Establish `h1 : (X * X).trace = ((∑ i, (hX.eigenvalues i) ^ 2 : ℝ) : ℂ)` using `by set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) with hD`. Establish `hs : X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary D` using `hX.spectral_theorem`. Establish `hXX : X * X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary (D * D)`.

Rewrite using `[map_mul, ← hs]`. Rewrite using `[hXX, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul, hD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]`. Use `push_cast`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`.

Simplify using `[sq]`. Establish `h2 : (X * X).trace = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply]`. Use `push_cast`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `a _`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Establish `: X b a = star (X a b)` using `(hX.apply b a).symm`. Rewrite using `[this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Both sides reduce to the same expression. Conclude with `h1.symm.trans h2` after adjusting the coercions. Establish `hcs` using `Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) (fun i => |hX.eigenvalues i|)`. Establish `e1 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) * |hX.eigenvalues i| = ∑ i, |hX.eigenvalues i|`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Apply the tactic sequence `by_cases h : hX.eigenvalues i = 0 <;> simp [h]`. Establish `e2 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 = (X.rank : ℝ)`. Rewrite using `[hX.rank_eq_card_non_zero_eigs, Fintype.card_subtype]`.

Establish `: ∀ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 = if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0`. Apply the tactic sequence `intro i; split_ifs <;> simp`. Simplify using `only [this, Finset.sum_boole]`. Establish `e3 : ∑ i, |hX.eigenvalues i| ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2`. Rewrite using `[← hsq]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `i _`. Conclude with `sq_abs _`. Rewrite `hcs` using `[e1, e2, e3]`. Conclude with `hcs`.
-/
theorem yBound : Formalism.HermitianLattices.CumulantEstimateDefs.EigenvalueSumBound := by
  intro N X hX
  have hsq : ∑ i, (hX.eigenvalues i) ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    have h1 : (X * X).trace = ((∑ i, (hX.eigenvalues i) ^ 2 : ℝ) : ℂ) := by
      set D : Matrix (Fin N) (Fin N) ℂ := Matrix.diagonal (RCLike.ofReal ∘ hX.eigenvalues) with hD
      have hs : X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary D := hX.spectral_theorem
      have hXX : X * X = conjStarAlgAut ℂ _ hX.eigenvectorUnitary (D * D) := by
        rw [map_mul, ← hs]
      rw [hXX, conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul, hD,
        Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
      push_cast
      apply Finset.sum_congr rfl; intro i _
      simp [sq]
    have h2 : (X * X).trace = ((∑ a, ∑ b, ‖X a b‖ ^ 2 : ℝ) : ℂ) := by
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
      push_cast
      apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _
      have : X b a = star (X a b) := (hX.apply b a).symm
      rw [this, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    exact_mod_cast h1.symm.trans h2
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun i => if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) (fun i => |hX.eigenvalues i|)
  have e1 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) * |hX.eigenvalues i| =
      ∑ i, |hX.eigenvalues i| := by
    apply Finset.sum_congr rfl; intro i _
    by_cases h : hX.eigenvalues i = 0 <;> simp [h]
  have e2 : ∑ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 = (X.rank : ℝ) := by
    rw [hX.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    have : ∀ i, (if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 =
        if hX.eigenvalues i ≠ 0 then (1 : ℝ) else 0 := by
      intro i; split_ifs <;> simp
    simp only [this, Finset.sum_boole]
  have e3 : ∑ i, |hX.eigenvalues i| ^ 2 = ∑ a, ∑ b, ‖X a b‖ ^ 2 := by
    rw [← hsq]; apply Finset.sum_congr rfl; intro i _; exact sq_abs _
  rw [e1, e2, e3] at hcs
  exact hcs

end E

section F
open Finset

/- English proof (translation)
Establish `e : {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} ≃ ({ij : Fin r × Fin r // blk ij.1 < blk ij.2} → F)` using `{ toFun := fun A ij => A.1 ij.1.1 ij.1.2 invFun := fun g => ⟨fun i j => if h : blk i < blk j then g ⟨(i, j), h⟩ else if i = j then 1 else 0, fun i j hij => by simp [not_lt.2 hij]⟩ left_inv := fun A => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i j`. Distinguish the cases in `h : blk i < blk j`. Simplify using `[h]`.

Simplify using `[h, A.2 i j (not_lt.1 h)]`. Use `right_inv := fun g => by`. Use function extensionality and compare the values at `ij`. Simplify using `[ij.2] }`. Rewrite using `[Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]`.
-/
lemma cardUni (F : Type) [Field F] [Fintype F] (r : ℕ) (blk : Fin r → ℕ) :
    Nat.card {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ (univ.filter (fun ij : Fin r × Fin r => blk ij.1 < blk ij.2)).card := by
  classical
  have e : {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} ≃
      ({ij : Fin r × Fin r // blk ij.1 < blk ij.2} → F) :=
    { toFun := fun A ij => A.1 ij.1.1 ij.1.2
      invFun := fun g => ⟨fun i j => if h : blk i < blk j then g ⟨(i, j), h⟩ else if i = j then 1 else 0,
        fun i j hij => by simp [not_lt.2 hij]⟩
      left_inv := fun A => by
        apply Subtype.ext
        funext i j
        by_cases h : blk i < blk j
        · simp [h]
        · simp [h, A.2 i j (not_lt.1 h)]
      right_inv := fun g => by
        funext ij
        simp [ij.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j

/- English proof (translation)
Establish `h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j)`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_range]`. Simplify using `only [bb, cc]`. Prove the components needed by the constructor for the conclusion.

Apply the tactic sequence `rintro ⟨h1, h2⟩ split_ifs at h2 ⊢ <;> omega`. Introduce `h1`. Apply the tactic sequence `refine ⟨by split_ifs at h1 <;> omega, ?_⟩`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> omega`. Rewrite using `[h, card_range]`.
-/
lemma inner (k rS j : ℕ) (hj : j < rS + (k + 1) + rS) :
    ((range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j)).card = cc k rS j := by
  have h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [bb, cc]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 ⊢ <;> omega
    · intro h1
      refine ⟨by split_ifs at h1 <;> omega, ?_⟩
      split_ifs at h1 ⊢ <;> omega
  rw [h, card_range]

/- English proof (translation)
Rewrite using `[Finset.sum_range_add, Finset.sum_range_add]`. Establish `e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x` using `Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]`. Establish `e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS` using `Finset.sum_congr rfl fun x hx => by`. Use `mem_range.1 hx` as an intermediate fact. Simplify using `only [cc]`.

Apply the tactic sequence `split_ifs <;> omega`. Establish `e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x)` using `Finset.sum_congr rfl fun x _ => by`. Simplify using `only [cc]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range, smul_eq_mul, smul_eq_mul]`.

Establish `hS` using `Finset.sum_range_id_mul_two rS`. Break down `rS with _ | m` into its components or cases. Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel] at hS`. Use polynomial arithmetic with `[hS]`.
-/
lemma total (k rS : ℕ) : ∑ j ∈ range (rS + (k + 1) + rS), cc k rS j = rS * (2 * k + 1 + 2 * rS) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x :=
    Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]
  have e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS :=
    Finset.sum_congr rfl fun x hx => by
      have := mem_range.1 hx
      simp only [cc]
      split_ifs <;> omega
  have e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp only [cc]
      split_ifs <;> omega
  rw [e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range,
    smul_eq_mul, smul_eq_mul]
  have hS := Finset.sum_range_id_mul_two rS
  rcases rS with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at hS
    nlinarith [hS]

/- English proof (translation)
Substitute `hr` using the available equality. Simplify using `only [Finset.card_filter, Fintype.sum_prod_type]`. Rewrite using `[Finset.sum_comm]`. Establish `h : ∀ j : Fin (rS + (k + 1) + rS), ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val`. Introduce `j`.

Establish `h1` using `inner k rS j.val j.isLt`. Rewrite `h1` using `[Finset.card_filter]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]`. Rewrite using `[Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]`.
-/
lemma countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by
  subst hr
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (rS + (k + 1) + rS),
      ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val := by
    intro j
    have h1 := inner k rS j.val j.isLt
    rw [Finset.card_filter] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]

/- English proof (translation)
Unfold `Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard`. Introduce `F _ _ _ k m hm hev`. Take `⟨s, rfl⟩` from `hev`. Take `⟨t, rfl⟩ : ∃ t, s = t + 1` from `⟨s - 1, by omega⟩`. Simplify using `only`.

Establish `e1 : (t + 1 + (t + 1)) / 2 - 1 = t` using `by omega`. Establish `e2 : k + (t + 1 + (t + 1)) - 1 = t + (k + 1) + t` using `by omega`. Rewrite using `[e1, e2]`. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Establish `key` using `cardUni F (t + (k + 1) + t) (fun i => bb k t i.val)`.

Establish `cf` using `countFree k t (t + (k + 1) + t) rfl`. Simplify using `only [bb] at key cf`. Rewrite using `[key, cf]`. Use `congr 1`. Establish `h : (t + (k + 1) + t) ^ 2 = (k + 1) ^ 2 + 2 * (t * (2 * k + 1 + 2 * t)) + 2 * t` using `by ring`.

Rewrite using `[h]`. Generalize the expression as in `(k + 1) ^ 2 = A`. Generalize the expression as in `t * (2 * k + 1 + 2 * t) = B`. Use linear arithmetic over natural numbers and integers.
-/
theorem nCard : Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.UnipotentRadicalCard
  intro F _ _ _ k m hm hev
  obtain ⟨s, rfl⟩ := hev
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  dsimp only
  have e1 : (t + 1 + (t + 1)) / 2 - 1 = t := by omega
  have e2 : k + (t + 1 + (t + 1)) - 1 = t + (k + 1) + t := by omega
  rw [e1, e2]
  refine ⟨rfl, ?_⟩
  have key := cardUni F (t + (k + 1) + t) (fun i => bb k t i.val)
  have cf := countFree k t (t + (k + 1) + t) rfl
  simp only [bb] at key cf
  rw [key, cf]
  congr 1
  have h : (t + (k + 1) + t) ^ 2 = (k + 1) ^ 2 + 2 * (t * (2 * k + 1 + 2 * t)) + 2 * t := by ring
  rw [h]
  generalize (k + 1) ^ 2 = A
  generalize t * (2 * k + 1 + 2 * t) = B
  omega

end F

end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

namespace Formalism.HermitianLattices.CumulantEstimateDefs

/- English proof (translation)
The claim follows from `CumulantEstimates.charsums`.
-/
theorem hecke_character_sums : SW_hecke_charsums := CumulantEstimates.charsums
/- English proof (translation)
The claim follows from `CumulantEstimates.t2vol`.
-/
theorem volume_eq_siegel_mass : VolumeDependsOnSumOfRecurrence := CumulantEstimates.t2vol
/- English proof (translation)
The claim follows from `CumulantEstimates.qLower`.
-/
theorem quadratic_form_lower_bound : QuadraticFormLowerBound := CumulantEstimates.qLower
/- English proof (translation)
The claim follows from `CumulantEstimates.qUpper`.
-/
theorem quadratic_form_upper_bound : QuadraticFormUpperBound := CumulantEstimates.qUpper
/- English proof (translation)
The claim follows from `CumulantEstimates.cumU`.
-/
theorem cumulant_upper_bound : CumulantUpperBound := CumulantEstimates.cumU
/- English proof (translation)
The claim follows from `CumulantEstimates.sinhAll`.
-/
theorem hyperbolic_sine_bound : SinhBounds := CumulantEstimates.sinhAll
/- English proof (translation)
The claim follows from `CumulantEstimates.yBound`.
-/
theorem height_parameter_bound : EigenvalueSumBound := CumulantEstimates.yBound
/- English proof (translation)
The claim follows from `CumulantEstimates.alphaT`.
-/
theorem exponent_alpha_bound : DecayExponentLowerBound := CumulantEstimates.alphaT
/- English proof (translation)
The claim follows from `CumulantEstimates.tailRay`.
-/
theorem tail_along_ray_bound : TailAlongRay := CumulantEstimates.tailRay
/- English proof (translation)
The claim follows from `CumulantEstimates.zBound`.
-/
theorem partition_function_bound : PartitionFunctionBound := CumulantEstimates.zBound
/- English proof (translation)
The claim follows from `CumulantEstimates.hsHalf`.
-/
theorem hilbert_schmidt_half_bound : HilbertSchmidtHalfBound := CumulantEstimates.hsHalf
/- English proof (translation)
The claim follows from `CumulantEstimates.nCard`.
-/
theorem lattice_rank_cardinality : UnipotentRadicalCard := CumulantEstimates.nCard

end Formalism.HermitianLattices.CumulantEstimateDefs
