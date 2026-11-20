import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LftMulRgt

noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracK

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

section Cl

variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A] (g : Fin n → Fin n → A)

omit [Ring A] [Algebra ℂ A] in

/- English proof (translation)
Rewrite `h` using `[← two_smul ℂ x, ← two_smul ℂ y]`. Conclude with `smul_right_injective M (two_ne_zero' ℂ) h`.
-/
theorem half_eq {M : Type} [AddCommGroup M] [Module ℂ M] {x y : M} (h : x + x = y + y) : x = y := by
  rw [← two_smul ℂ x, ← two_smul ℂ y] at h
  exact smul_right_injective M (two_ne_zero' ℂ) h

def uF (a b : Fin n) : A := ∑ e, g a e * g e b

variable {g}
variable (hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : A) else 0)
include hg

/- English proof (translation)
Unfold `uF`. Rewrite using `[Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Establish `h1 : ∀ e, g a e * g e b * g d f - g d f * (g a e * g e b) = g a e * (if e = f ∧ b = d then (2 : ℂ) • (1 : A) else 0) - (if a = f ∧ e = d then (2 : ℂ) • (1 : A) else 0) * g e b`. Introduce `e`. Rewrite using `[← hg e b d f, ← hg a e d f]`.

Use `noncomm_ring`. Repeatedly rewrite using `[h1]`. Rewrite using `[Finset.sum_sub_distrib]`. Use `congr 1`. Distinguish the cases in `h : b = d`.

Simplify using `[h]`. Simplify using `[h]`. Distinguish the cases in `h : a = f`. Simplify using `[h]`. Simplify using `[h]`.
-/
theorem u_comm (a b d f : Fin n) :
    uF g a b * g d f - g d f * uF g a b =
      (if b = d then (2 : ℂ) • g a f else 0) - (if a = f then (2 : ℂ) • g d b else 0) := by
  unfold uF
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have h1 : ∀ e, g a e * g e b * g d f - g d f * (g a e * g e b) =
      g a e * (if e = f ∧ b = d then (2 : ℂ) • (1 : A) else 0) -
        (if a = f ∧ e = d then (2 : ℂ) • (1 : A) else 0) * g e b := by
    intro e
    rw [← hg e b d f, ← hg a e d f]
    noncomm_ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases h : b = d
    · simp [h]
    · simp [h]
  · by_cases h : a = f
    · simp [h]
    · simp [h]

/- English proof (translation)
Establish `h1 : uF g a b * uF g d e - uF g d e * uF g a b = ∑ f, ((uF g a b * g d f - g d f * uF g a b) * g f e + g d f * (uF g a b * g f e - g f e * uF g a b))`. Establish `h2 : uF g d e = ∑ f, g d f * g f e` using `rfl`. Rewrite using `[h2, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun f _ => by noncomm_ring`. Rewrite using `[h1]`.

Simplify using `only [u_comm hg, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Apply the tactic sequence `have t1 : ∑ f, (if b = d then (2 : ℂ) • g a f else 0) * g f e = if b = d then (2 : ℂ) • uF g a e else 0 := by split_ifs <;> simp [uF, Finset.smul_sum]`. Establish `t2 : ∑ f, (if a = f then (2 : ℂ) • g d b else 0) * g f e = (2 : ℂ) • (g d b * g a e)`. Simplify using the standard rewrite rules. Establish `t3 : ∑ f, g d f * (if b = f then (2 : ℂ) • g a e else 0) = (2 : ℂ) • (g d b * g a e)`.

Simplify using the standard rewrite rules. Apply the tactic sequence `have t4 : ∑ f, g d f * (if a = e then (2 : ℂ) • g f b else 0) = if a = e then (2 : ℂ) • uF g d b else 0 := by split_ifs <;> simp [uF, Finset.smul_sum]`. Rewrite using `[t1, t2, t3, t4]`. Normalize the expressions using the abelian group laws.
-/
theorem u_bracket (a b d e : Fin n) :
    uF g a b * uF g d e - uF g d e * uF g a b =
      (if b = d then (2 : ℂ) • uF g a e else 0) - (if a = e then (2 : ℂ) • uF g d b else 0) := by
  have h1 : uF g a b * uF g d e - uF g d e * uF g a b =
      ∑ f, ((uF g a b * g d f - g d f * uF g a b) * g f e + g d f * (uF g a b * g f e - g f e * uF g a b)) := by
    have h2 : uF g d e = ∑ f, g d f * g f e := rfl
    rw [h2, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun f _ => by noncomm_ring
  rw [h1]
  simp only [u_comm hg, sub_mul, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have t1 : ∑ f, (if b = d then (2 : ℂ) • g a f else 0) * g f e = if b = d then (2 : ℂ) • uF g a e else 0 := by
    split_ifs <;> simp [uF, Finset.smul_sum]
  have t2 : ∑ f, (if a = f then (2 : ℂ) • g d b else 0) * g f e = (2 : ℂ) • (g d b * g a e) := by
    simp
  have t3 : ∑ f, g d f * (if b = f then (2 : ℂ) • g a e else 0) = (2 : ℂ) • (g d b * g a e) := by
    simp
  have t4 : ∑ f, g d f * (if a = e then (2 : ℂ) • g f b else 0) = if a = e then (2 : ℂ) • uF g d b else 0 := by
    split_ifs <;> simp [uF, Finset.smul_sum]
  rw [t1, t2, t3, t4]
  abel

variable (g) in

def sF (a b : Fin n) : A := (1 / 2 : ℂ) • uF g a b - if a = b then ((n : ℂ) / 2) • (1 : A) else 0

/- English proof (translation)
Introduce `a b d e`. Establish `hz : ∀ (z w : ℂ), ((1 / 2 : ℂ) • uF g a b - z • (1 : A)) * ((1 / 2 : ℂ) • uF g d e - w • (1 : A)) - ((1 / 2 : ℂ) • uF g d e - w • (1 : A)) * ((1 / 2 : ℂ) • uF g a b - z • (1 : A)) = (1 / 4 : ℂ) • (uF g a b * uF g d e - uF g d e * uF g a b)`. Introduce `z w`. Simplify using `only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`. Use `module`.

Establish `hs : ∀ a b : Fin n, sF g a b = (1 / 2 : ℂ) • uF g a b - (if a = b then ((n : ℂ) / 2) else 0) • (1 : A)`. Introduce `a b`. Unfold `sF`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hs a b, hs d e, hz, u_bracket hg]`.

Apply the tactic sequence `by_cases h1 : b = d <;> by_cases h2 : a = e`. Substitute `h1 h2` using the available equality. Simplify using `only [if_true, hs]`. Use `module`. Establish `h3 : ¬ e = a` using `fun h => h2 h.symm`.

Simplify using `only [h1, h2, h3, if_true, if_false, hs]`. Simplify using `[h2]`. Use `module`. Establish `h3 : ¬ d = b` using `fun h => h1 h.symm`. Substitute `h2` using the available equality.

Simplify using `only [h1, h3, if_true, if_false, hs]`. Simplify using `[h3]`. Use `module`. Establish `h3 : ¬ e = a` using `fun h => h2 h.symm`. Simplify using `[h1, h2, h3]`.
-/
theorem s_gl : Formalism.REAL.GlRel (sF g) := by
  intro a b d e
  have hz : ∀ (z w : ℂ), ((1 / 2 : ℂ) • uF g a b - z • (1 : A)) * ((1 / 2 : ℂ) • uF g d e - w • (1 : A)) -
      ((1 / 2 : ℂ) • uF g d e - w • (1 : A)) * ((1 / 2 : ℂ) • uF g a b - z • (1 : A)) =
      (1 / 4 : ℂ) • (uF g a b * uF g d e - uF g d e * uF g a b) := by
    intro z w
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hs : ∀ a b : Fin n, sF g a b = (1 / 2 : ℂ) • uF g a b - (if a = b then ((n : ℂ) / 2) else 0) • (1 : A) := by
    intro a b
    unfold sF
    split_ifs <;> simp
  rw [hs a b, hs d e, hz, u_bracket hg]
  by_cases h1 : b = d <;> by_cases h2 : a = e
  · subst h1 h2
    simp only [if_true, hs]
    module
  · have h3 : ¬ e = a := fun h => h2 h.symm
    simp only [h1, h2, h3, if_true, if_false, hs]
    simp [h2]
    module
  · have h3 : ¬ d = b := fun h => h1 h.symm
    subst h2
    simp only [h1, h3, if_true, if_false, hs]
    simp [h3]
    module
  · have h3 : ¬ e = a := fun h => h2 h.symm
    simp [h1, h2, h3]

/- English proof (translation)
Apply `half_eq` to reduce the goal to its premises. Establish `h1 : ∑ a, uF g a a = ∑ a, ∑ e, g e a * g a e`. Unfold `uF`. Rewrite using `[Finset.sum_comm]`. Establish `h2 : ∑ a, uF g a a + ∑ a, uF g a a = ∑ a : Fin n, ∑ e : Fin n, (2 : ℂ) • (1 : A)` using `by nth_rewrite 2 [h1]`.

Unfold `uF`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations.

Rewrite using `[hg a e e a]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem u_trace : ∑ a, uF g a a = ((n : ℂ) ^ 2) • (1 : A) := by
  apply half_eq
  have h1 : ∑ a, uF g a a = ∑ a, ∑ e, g e a * g a e := by
    unfold uF
    rw [Finset.sum_comm]
  have h2 : ∑ a, uF g a a + ∑ a, uF g a a = ∑ a : Fin n, ∑ e : Fin n, (2 : ℂ) • (1 : A) := by
    nth_rewrite 2 [h1]
    unfold uF
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hg a e e a]
    simp
  rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
  congr 1
  ring

/- English proof (translation)
Apply `half_eq` to reduce the goal to its premises. Establish `h2 : ∑ a, ∑ f, g a a * g f f + ∑ a, ∑ f, g a a * g f f = ∑ a : Fin n, ∑ f : Fin n, if a = f then (2 : ℂ) • (1 : A) else 0` using `by nth_rewrite 2 [Finset.sum_comm]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[hg a a f f]`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Simplify using `only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem c_diag : ∑ a, ∑ f, g a a * g f f = (n : ℂ) • (1 : A) := by
  apply half_eq
  have h2 : ∑ a, ∑ f, g a a * g f f + ∑ a, ∑ f, g a a * g f f =
      ∑ a : Fin n, ∑ f : Fin n, if a = f then (2 : ℂ) • (1 : A) else 0 := by
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [hg a a f f]
    simp
  rw [h2]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← add_smul]
  congr 1
  ring

/- English proof (translation)
Use `set W := ∑ a, ∑ b, uF g a b * uF g b a with hW`. Establish `hA : ∀ a, ∑ b, uF g a b * uF g b a = ∑ e, ∑ f, g a e * (uF g e f * g f a)`. Introduce `a`. Establish `hM : ∀ a b, (Matrix.of g * Matrix.of g) a b = uF g a b` using `fun a b => rfl`. Establish `h1 : (Matrix.of g * Matrix.of g) * (Matrix.of g * Matrix.of g) = Matrix.of g * ((Matrix.of g * Matrix.of g) * Matrix.of g)`.

Simplify using `only [Matrix.mul_assoc]`. Establish `h2` using `congrFun (congrFun h1 a) a`. Rewrite `h2` using `[Matrix.mul_apply, Matrix.mul_apply]`. Simplify using `only [hM] at h2`. Rewrite using `[h2]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Simplify using `only [hM, Matrix.of_apply]`. Establish `hB : ∀ a e f, g a e * (uF g e f * g f a) = g a e * g f a * uF g e f + (2 : ℂ) • (g a e * g e a) - if e = a then (2 : ℂ) • (g a a * g f f) else 0`. Introduce `a e f`.

Establish `h1` using `u_comm hg e f f a`. Rewrite `h1` using `[if_pos rfl]`. Rewrite using `[eq_add_of_sub_eq' h1]`. Distinguish the cases in `h : e = a`. Substitute `h` using the available equality.

Simplify using `[mul_add, mul_sub, mul_assoc]`. Normalize the expressions using the abelian group laws. Simplify using `[h, mul_add, mul_sub, mul_assoc]`. Establish `hC : ∀ e f, ∑ a, g a e * g f a = (n : ℂ) • (if e = f then (2 : ℂ) • (1 : A) else 0) - uF g f e`. Introduce `e f`.

Establish `h1 : ∀ a, g a e * g f a = (if e = f then (2 : ℂ) • (1 : A) else 0) - g f a * g a e`. Introduce `a`. Use `hg a e f a` as an intermediate fact. Simplify using `only [true_and] at this`. Conclude with `eq_sub_of_add_eq this`.

Simplify using `only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]`. Both sides reduce to the same expression. Establish `t1 : ∑ a, ∑ e, ∑ f, g a e * g f a * uF g e f = (2 * (n : ℂ) ^ 3) • (1 : A) - W`. Establish `e1 : ∑ a, ∑ e, ∑ f, g a e * g f a * uF g e f = ∑ e, ∑ f, (∑ a, g a e * g f a) * uF g e f`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Rewrite using `[e1]`.

Simplify using `only [hC, sub_mul, Finset.sum_sub_distrib]`. Establish `e2 : ∑ e, ∑ f, uF g f e * uF g e f = W`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[e2]`. Use `congr 1`.

Establish `e3 : ∀ e, ∑ f, (n : ℂ) • (if e = f then (2 : ℂ) • (1 : A) else 0) * uF g e f = ((n : ℂ) * 2) • uF g e e`. Introduce `e`. Simplify using `[smul_smul, ite_mul]`. Simplify using `only [e3]`. Rewrite using `[← Finset.smul_sum, u_trace hg, smul_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `t2 : ∑ a, ∑ e, ∑ f : Fin n, (2 : ℂ) • (g a e * g e a) = (2 * (n : ℂ) ^ 3) • (1 : A)`. Establish `h1 : ∑ a, uF g a a = ∑ a, ∑ e, g a e * g e a` using `rfl`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]`.

Simplify using `only [← Finset.smul_sum]`. Rewrite using `[← h1, u_trace hg]`. Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `t3 : ∑ a, ∑ e, ∑ f, (if e = a then (2 : ℂ) • (g a a * g f f) else 0) = (2 * (n : ℂ)) • (1 : A)`. Establish `h1 : ∀ a, ∑ e, ∑ f, (if e = a then (2 : ℂ) • (g a a * g f f) else 0) = (2 : ℂ) • ∑ f, g a a * g f f`. Introduce `a`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[Finset.smul_sum]`.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Simplify using `only [h1]`. Rewrite using `[← Finset.smul_sum, c_diag hg, smul_smul]`.

Establish `hT : W = ((2 * (n : ℂ) ^ 3) • (1 : A) - W) + (2 * (n : ℂ) ^ 3) • (1 : A) - (2 * (n : ℂ)) • (1 : A)`. Rewrite using `[← t1, ← t2, ← t3, hW]`. Simplify using `only [hA, hB, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Establish `: W + W = W + (((2 * (n : ℂ) ^ 3) • (1 : A) - W) + (2 * (n : ℂ) ^ 3) • (1 : A) - (2 * (n : ℂ)) • (1 : A))` using `by nth_rewrite 2 [hT]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Use `module`.
-/
theorem u_four : (∑ a, ∑ b, uF g a b * uF g b a) + (∑ a, ∑ b, uF g a b * uF g b a) =
    (4 * (n : ℂ) ^ 3 - 2 * n) • (1 : A) := by
  set W := ∑ a, ∑ b, uF g a b * uF g b a with hW
  have hA : ∀ a, ∑ b, uF g a b * uF g b a = ∑ e, ∑ f, g a e * (uF g e f * g f a) := by
    intro a
    have hM : ∀ a b, (Matrix.of g * Matrix.of g) a b = uF g a b := fun a b => rfl
    have h1 : (Matrix.of g * Matrix.of g) * (Matrix.of g * Matrix.of g) =
        Matrix.of g * ((Matrix.of g * Matrix.of g) * Matrix.of g) := by
      simp only [Matrix.mul_assoc]
    have h2 := congrFun (congrFun h1 a) a
    rw [Matrix.mul_apply, Matrix.mul_apply] at h2
    simp only [hM] at h2
    rw [h2]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Matrix.mul_apply, Finset.mul_sum]
    simp only [hM, Matrix.of_apply]
  have hB : ∀ a e f, g a e * (uF g e f * g f a) =
      g a e * g f a * uF g e f + (2 : ℂ) • (g a e * g e a) - if e = a then (2 : ℂ) • (g a a * g f f) else 0 := by
    intro a e f
    have h1 := u_comm hg e f f a
    rw [if_pos rfl] at h1
    rw [eq_add_of_sub_eq' h1]
    by_cases h : e = a
    · subst h
      simp [mul_add, mul_sub, mul_assoc]
      abel
    · simp [h, mul_add, mul_sub, mul_assoc]
  have hC : ∀ e f, ∑ a, g a e * g f a = (n : ℂ) • (if e = f then (2 : ℂ) • (1 : A) else 0) - uF g f e := by
    intro e f
    have h1 : ∀ a, g a e * g f a = (if e = f then (2 : ℂ) • (1 : A) else 0) - g f a * g a e := by
      intro a
      have := hg a e f a
      simp only [true_and] at this
      exact eq_sub_of_add_eq this
    simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have t1 : ∑ a, ∑ e, ∑ f, g a e * g f a * uF g e f = (2 * (n : ℂ) ^ 3) • (1 : A) - W := by
    have e1 : ∑ a, ∑ e, ∑ f, g a e * g f a * uF g e f = ∑ e, ∑ f, (∑ a, g a e * g f a) * uF g e f := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [Finset.sum_mul]
    rw [e1]
    simp only [hC, sub_mul, Finset.sum_sub_distrib]
    have e2 : ∑ e, ∑ f, uF g f e * uF g e f = W := by
      rw [Finset.sum_comm]
    rw [e2]
    congr 1
    have e3 : ∀ e, ∑ f, (n : ℂ) • (if e = f then (2 : ℂ) • (1 : A) else 0) * uF g e f =
        ((n : ℂ) * 2) • uF g e e := by
      intro e
      simp [smul_smul, ite_mul]
    simp only [e3]
    rw [← Finset.smul_sum, u_trace hg, smul_smul]
    congr 1
    ring
  have t2 : ∑ a, ∑ e, ∑ f : Fin n, (2 : ℂ) • (g a e * g e a) = (2 * (n : ℂ) ^ 3) • (1 : A) := by
    have h1 : ∑ a, uF g a a = ∑ a, ∑ e, g a e * g e a := rfl
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
    simp only [← Finset.smul_sum]
    rw [← h1, u_trace hg]
    simp only [smul_smul]
    congr 1
    ring
  have t3 : ∑ a, ∑ e, ∑ f, (if e = a then (2 : ℂ) • (g a a * g f f) else 0) = (2 * (n : ℂ)) • (1 : A) := by
    have h1 : ∀ a, ∑ e, ∑ f, (if e = a then (2 : ℂ) • (g a a * g f f) else 0) =
        (2 : ℂ) • ∑ f, g a a * g f f := by
      intro a
      rw [Finset.sum_eq_single a]
      · simp [Finset.smul_sum]
      · intro b _ hb
        simp [hb]
      · simp
    simp only [h1]
    rw [← Finset.smul_sum, c_diag hg, smul_smul]
  have hT : W = ((2 * (n : ℂ) ^ 3) • (1 : A) - W) + (2 * (n : ℂ) ^ 3) • (1 : A) - (2 * (n : ℂ)) • (1 : A) := by
    rw [← t1, ← t2, ← t3, hW]
    simp only [hA, hB, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have : W + W = W + (((2 * (n : ℂ) ^ 3) • (1 : A) - W) + (2 * (n : ℂ) ^ 3) • (1 : A) - (2 * (n : ℂ)) • (1 : A)) := by
    nth_rewrite 2 [hT]
    rfl
  rw [this]
  module

/- English proof (translation)
Establish `hs : ∀ a b : Fin n, sF g a b * sF g b a = (1 / 4 : ℂ) • (uF g a b * uF g b a) - (if a = b then ((n : ℂ) / 2) • uF g a a - ((n : ℂ) / 2) ^ 2 • (1 : A) else 0)`. Introduce `a b`. Unfold `sF`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using `only [if_true, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul]`. Use `module`. Establish `h' : ¬ b = a` using `fun e => h e.symm`. Simplify using `only [h, h', if_false, sub_zero, smul_mul_assoc, mul_smul_comm, smul_smul]`. Use `congr 1`.

Evaluate the numerical expressions. Unfold `Formalism.REAL.Cas`. Simplify using `only [hs, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[u_trace hg]`. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]`.

Establish `h4` using `u_four hg`. Establish `: ∀ W : A, W + W = (4 * (n : ℂ) ^ 3 - 2 * n) • (1 : A) → (1 / 4 : ℂ) • W = ((n : ℂ) ^ 3 / 2 - (n : ℂ) / 4) • (1 : A)`. Introduce `W hW`. Establish `e : W = (2 * (n : ℂ) ^ 3 - n) • (1 : A)`. Apply `half_eq` to reduce the goal to its premises.

Rewrite using `[hW]`. Use `module`. Rewrite using `[e, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this _ h4]`. Use `module`.
-/
theorem s_cas : Formalism.REAL.Cas (sF g) = (((n : ℂ) ^ 3 - n) / 4) • (1 : A) := by
  have hs : ∀ a b : Fin n, sF g a b * sF g b a =
      (1 / 4 : ℂ) • (uF g a b * uF g b a) -
        (if a = b then ((n : ℂ) / 2) • uF g a a - ((n : ℂ) / 2) ^ 2 • (1 : A) else 0) := by
    intro a b
    unfold sF
    by_cases h : a = b
    · subst h
      simp only [if_true, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub, smul_smul]
      module
    · have h' : ¬ b = a := fun e => h e.symm
      simp only [h, h', if_false, sub_zero, smul_mul_assoc, mul_smul_comm, smul_smul]
      congr 1
      norm_num
  unfold Formalism.REAL.Cas
  simp only [hs, Finset.sum_sub_distrib, ← Finset.smul_sum, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [u_trace hg]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]
  have h4 := u_four hg
  have : ∀ W : A, W + W = (4 * (n : ℂ) ^ 3 - 2 * n) • (1 : A) → (1 / 4 : ℂ) • W = ((n : ℂ) ^ 3 / 2 - (n : ℂ) / 4) • (1 : A) := by
    intro W hW
    have e : W = (2 * (n : ℂ) ^ 3 - n) • (1 : A) := by
      apply half_eq
      rw [hW]
      module
    rw [e, smul_smul]
    congr 1
    ring
  rw [this _ h4]
  module

end Cl

section Sq

/- English proof (translation)
Establish `e1 : (∑ i, P i * G i) * (∑ i, P i * G i) = ∑ i, ∑ j, P i * P j * (G i * G j)`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← mul_assoc (G i), ← h j i, mul_assoc, mul_assoc]`. Establish `e2 : (∑ i, P i * G i) * (∑ i, P i * G i) = ∑ i, ∑ j, P j * P i * (G j * G i)`.

Rewrite using `[e1, Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `noncomm_ring`.
-/
theorem sq_sym {I : Type} [Fintype I] {A : Type} [Ring A] (P G : I → A) (h : ∀ i j, P i * G j = G j * P i) :
    (∑ i, P i * G i) * (∑ i, P i * G i) + (∑ i, P i * G i) * (∑ i, P i * G i) =
      ∑ i, ∑ j, P i * P j * (G i * G j + G j * G i) - ∑ i, ∑ j, (P i * P j - P j * P i) * (G i * G j + G j * G i) +
        ∑ i, ∑ j, (P i * P j - P j * P i) * (G i * G j) := by
  have e1 : (∑ i, P i * G i) * (∑ i, P i * G i) = ∑ i, ∑ j, P i * P j * (G i * G j) := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← mul_assoc (G i), ← h j i, mul_assoc, mul_assoc]
  have e2 : (∑ i, P i * G i) * (∑ i, P i * G i) = ∑ i, ∑ j, P j * P i * (G j * G i) := by
    rw [e1, Finset.sum_comm]
  calc _ = (∑ i, ∑ j, P i * P j * (G i * G j)) + ∑ i, ∑ j, P j * P i * (G j * G i) := congrArg₂ (· + ·) e1 e2
    _ = _ := by
      simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      noncomm_ring

variable {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[hc]`. Simplify using the standard rewrite rules.
-/
theorem delta4 (H : Fin n → Fin n → A) (a b : Fin n) :
    ∑ c, ∑ d, H c d * (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) = (2 : ℂ) • H b a := by
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ hc
    simp [hc]
  · simp

/- English proof (translation)
Establish `hD : ∑ a, ∑ b, p a b * g b a = ∑ i : Fin n × Fin n, p i.1 i.2 * g i.2 i.1` using `(Fintype.sum_prod_type (fun i : Fin n × Fin n => p i.1 i.2 * g i.2 i.1)).symm`. Establish `hs` using `sq_sym (fun i : Fin n × Fin n => p i.1 i.2) (fun i => g i.2 i.1) (fun i j => hpg _ _ _ _)`. Rewrite `hs` using `[← hD]`. Simplify using `only [Fintype.sum_prod_type] at hs`. Establish `hAn : ∀ a b c d, g b a * g d c + g d c * g b a = if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0`.

Introduce `a b c d`. Establish `e : (b = c ∧ a = d) ↔ (c = b ∧ d = a)` using `⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩`. Rewrite using `[hg b a d c]`. Simplify using `only [e]`. Apply the tactic sequence `by_cases h1 : c = b <;> by_cases h2 : d = a <;> simp [h1, h2]`.

Simplify using `only [hAn] at hs`. Establish `T1 : ∑ a, ∑ b, ∑ c, ∑ d, p a b * p c d * (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) = ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a)` using `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => delta4 (fun c d => p a b * p c d) a b`. Establish `T2 : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) * (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) = 0`. Establish `e : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) * (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) = ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a - p b a * p a b)` using `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => delta4 (fun c d => p a b * p c d - p c d * p a b) a b`. Rewrite using `[e]`.

Simplify using `only [smul_sub, Finset.sum_sub_distrib]`. Rewrite using `[sub_eq_zero, Finset.sum_comm]`. Use `set U : Fin n → Fin n → A := fun a d => ∑ e, g d e * g e a with hU`. Establish `Q1 : ∑ a, ∑ b, ∑ c, ∑ d, (if b = c then k a d else 0) * (g b a * g d c) = ∑ a, ∑ d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d)`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Establish `e1 : ∀ b, ∑ c, ∑ d, (if b = c then k a d else 0) * (g b a * g d c) = ∑ d, k a d * (g b a * g d b)`. Introduce `b`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`.

Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules. Simplify using `only [e1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Use `congr 1`. Establish `e2 : ∀ b, g b a * g d b = (if a = d then (2 : ℂ) • (1 : A) else 0) - g d b * g b a`. Introduce `b`. Use `hg b a d b` as an intermediate fact.

Simplify using `only [true_and] at this`. Conclude with `eq_sub_of_add_eq this`. Simplify using `only [e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ]`. Both sides reduce to the same expression. Establish `Q2 : ∑ a, ∑ b, ∑ c, ∑ d, (if d = a then k c b else 0) * (g b a * g d c) = ∑ a, ∑ d, k a d * U a d`.

Establish `e1 : ∀ a b c, ∑ d, (if d = a then k c b else 0) * (g b a * g d c) = k c b * (g b a * g a c)`. Introduce `a b c`. Simplify using the standard rewrite rules. Simplify using `only [e1]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hU, ← Finset.mul_sum]`. Establish `T3 : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) * (g b a * g d c) = ∑ a, ∑ d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d)`. Simplify using `only [hp, sub_mul, Finset.sum_sub_distrib]`. Establish `e : ∀ a d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d) = k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d) - k a d * U a d`.

Introduce `a d`. Rewrite using `[mul_sub]`. Simplify using `only [e, Finset.sum_sub_distrib]`. Rewrite using `[← Q1, ← Q2]`. Rewrite `hs` using `[T1, T2, T3]`.

Apply `half_eq` to reduce the goal to its premises. Rewrite using `[hs]`. Use `set W : Fin n → Fin n → A := fun a d => (1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : A) else 0 with hW`. Establish `hc : ∀ a d, (n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d = -(W a d + W a d + (W a d + W a d))`. Introduce `a d`.

Distinguish the cases in `h : a = d`. Substitute `h` using the available equality. Simplify using `only [hW, hU, if_true]`. Use `module`. Establish `h' : ¬ d = a` using `fun e => h e.symm`.

Simplify using `only [hW, hU, h, h', if_false]`. Use `module`. Establish `hZ : ∑ a, ∑ d, k a d * (W a d + W a d + (W a d + W a d)) = ∑ a, ∑ d, k a d * W a d + ∑ a, ∑ d, k a d * W a d + (∑ a, ∑ d, k a d * W a d + ∑ a, ∑ d, k a d * W a d)`. Simplify using `only [mul_add, Finset.sum_add_distrib]`. Establish `hP : ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a) = ∑ a, ∑ b, p a b * p b a + ∑ a, ∑ b, p a b * p b a`.

Simplify using `only [← Finset.smul_sum]`. Conclude with `two_smul ℂ _`. Simplify using `only [hc, mul_neg, Finset.sum_neg_distrib]`. Rewrite using `[hZ, hP, two_mul]`. Normalize the expressions using the abelian group laws.
-/
theorem dirac_sq_ring (p k g : Fin n → Fin n → A)
    (hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : A) else 0)
    (hp : ∀ a b c d, p a b * p c d - p c d * p a b = (if b = c then k a d else 0) - (if d = a then k c b else 0))
    (hpg : ∀ a b c d, p a b * g c d = g c d * p a b) :
    (∑ a, ∑ b, p a b * g b a) * (∑ a, ∑ b, p a b * g b a) =
      ∑ a, ∑ b, p a b * p b a -
        2 * ∑ a, ∑ d, k a d * ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : A) else 0) := by
  have hD : ∑ a, ∑ b, p a b * g b a = ∑ i : Fin n × Fin n, p i.1 i.2 * g i.2 i.1 :=
    (Fintype.sum_prod_type (fun i : Fin n × Fin n => p i.1 i.2 * g i.2 i.1)).symm
  have hs := sq_sym (fun i : Fin n × Fin n => p i.1 i.2) (fun i => g i.2 i.1) (fun i j => hpg _ _ _ _)
  rw [← hD] at hs
  simp only [Fintype.sum_prod_type] at hs
  have hAn : ∀ a b c d, g b a * g d c + g d c * g b a =
      if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0 := by
    intro a b c d
    have e : (b = c ∧ a = d) ↔ (c = b ∧ d = a) :=
      ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
    rw [hg b a d c]
    simp only [e]
    by_cases h1 : c = b <;> by_cases h2 : d = a <;> simp [h1, h2]
  simp only [hAn] at hs
  have T1 : ∑ a, ∑ b, ∑ c, ∑ d, p a b * p c d * (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) =
      ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a) :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => delta4 (fun c d => p a b * p c d) a b
  have T2 : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) *
      (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) = 0 := by
    have e : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) *
        (if c = b then (if d = a then (2 : ℂ) • (1 : A) else 0) else 0) =
        ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a - p b a * p a b) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
        delta4 (fun c d => p a b * p c d - p c d * p a b) a b
    rw [e]
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [sub_eq_zero, Finset.sum_comm]
  set U : Fin n → Fin n → A := fun a d => ∑ e, g d e * g e a with hU
  have Q1 : ∑ a, ∑ b, ∑ c, ∑ d, (if b = c then k a d else 0) * (g b a * g d c) =
      ∑ a, ∑ d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have e1 : ∀ b, ∑ c, ∑ d, (if b = c then k a d else 0) * (g b a * g d c) = ∑ d, k a d * (g b a * g d b) := by
      intro b
      rw [Finset.sum_eq_single b]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    simp only [e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    have e2 : ∀ b, g b a * g d b = (if a = d then (2 : ℂ) • (1 : A) else 0) - g d b * g b a := by
      intro b
      have := hg b a d b
      simp only [true_and] at this
      exact eq_sub_of_add_eq this
    simp only [e2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ]
    rfl
  have Q2 : ∑ a, ∑ b, ∑ c, ∑ d, (if d = a then k c b else 0) * (g b a * g d c) = ∑ a, ∑ d, k a d * U a d := by
    have e1 : ∀ a b c, ∑ d, (if d = a then k c b else 0) * (g b a * g d c) = k c b * (g b a * g a c) := by
      intro a b c
      simp
    simp only [e1]
    calc ∑ a, ∑ b, ∑ c, k c b * (g b a * g a c) = ∑ a, ∑ c, ∑ b, k c b * (g b a * g a c) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, k c b * (g b a * g a c) := Finset.sum_comm
      _ = ∑ c, ∑ b, ∑ a, k c b * (g b a * g a c) := Finset.sum_congr rfl fun c _ => Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
        rw [hU, ← Finset.mul_sum]
  have T3 : ∑ a, ∑ b, ∑ c, ∑ d, (p a b * p c d - p c d * p a b) * (g b a * g d c) =
      ∑ a, ∑ d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d) := by
    simp only [hp, sub_mul, Finset.sum_sub_distrib]
    have e : ∀ a d, k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d) =
        k a d * ((n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d) - k a d * U a d := by
      intro a d
      rw [mul_sub]
    simp only [e, Finset.sum_sub_distrib]
    rw [← Q1, ← Q2]
  rw [T1, T2, T3] at hs
  apply half_eq
  rw [hs]
  set W : Fin n → Fin n → A := fun a d =>
    (1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : A) else 0 with hW
  have hc : ∀ a d, (n : ℂ) • (if a = d then (2 : ℂ) • (1 : A) else 0) - U a d - U a d = -(W a d + W a d + (W a d + W a d)) := by
    intro a d
    by_cases h : a = d
    · subst h
      simp only [hW, hU, if_true]
      module
    · have h' : ¬ d = a := fun e => h e.symm
      simp only [hW, hU, h, h', if_false]
      module
  have hZ : ∑ a, ∑ d, k a d * (W a d + W a d + (W a d + W a d)) =
      ∑ a, ∑ d, k a d * W a d + ∑ a, ∑ d, k a d * W a d + (∑ a, ∑ d, k a d * W a d + ∑ a, ∑ d, k a d * W a d) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have hP : ∑ a, ∑ b, (2 : ℂ) • (p a b * p b a) = ∑ a, ∑ b, p a b * p b a + ∑ a, ∑ b, p a b * p b a := by
    simp only [← Finset.smul_sum]
    exact two_smul ℂ _
  simp only [hc, mul_neg, Finset.sum_neg_distrib]
  rw [hZ, hP, two_mul]
  abel

end Sq

section Misc

/- English proof (translation)
Establish `key : ∀ (m : ℕ) (t : ℝ), ∑ i ∈ range m, (t - (i : ℝ)) ^ 2 = m * t ^ 2 - t * m * (m - 1) + ((m : ℝ) - 1) * m * (2 * m - 1) / 6`. Introduce `m t`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ k ih`.

Rewrite using `[Finset.sum_range_succ, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∑ a, (rhoV n a) ^ 2 = ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) ^ 2`. Rewrite using `[Finset.sum_range]`.

Both sides reduce to the same expression. Rewrite using `[h1, key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_rhoV_sq (n : ℕ) : ∑ a, (rhoV n a) ^ 2 = ((n : ℝ) ^ 3 - n) / 12 := by
  have key : ∀ (m : ℕ) (t : ℝ), ∑ i ∈ range m, (t - (i : ℝ)) ^ 2 =
      m * t ^ 2 - t * m * (m - 1) + ((m : ℝ) - 1) * m * (2 * m - 1) / 6 := by
    intro m t
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  have h1 : ∑ a, (rhoV n a) ^ 2 = ∑ i ∈ range n, (((n : ℝ) - 1) / 2 - (i : ℝ)) ^ 2 := by
    rw [Finset.sum_range]
    rfl
  rw [h1, key]
  ring

/- English proof (translation)
Unfold `GlobalTheory.Dec.gelfVal`. Use `set l : Fin n → ℂ := fun c => χ c + ((n : ℂ) - 1) / 2 with hl`. Use `set B := Formalism.REAL.Amat l with hB`. Establish `hcol : ∀ c, ∑ a, B a c = l c - ((c : ℕ) : ℂ)`. Introduce `c`.

Establish `e : ∀ a, B a c = (if a = c then l c else 0) + (if a < c then (-1 : ℂ) else 0)`. Introduce `a`. Simplify using `only [hB, Formalism.REAL.Amat, Matrix.of_apply]`. Distinguish the cases in `h : a = c`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hc : (univ.filter fun a : Fin n => a < c).card = (c : ℕ)`. Rewrite using `[Finset.filter_gt_eq_Iio, Fin.card_Iio]`. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[← Finset.sum_filter, Finset.sum_const, hc]`. Simplify using `[sub_eq_add_neg]`. Establish `hrow : ∀ c, ∑ b, B c b = l c - ((n : ℂ) - 1 - ((c : ℕ) : ℂ))`. Introduce `c`. Establish `e : ∀ b, B c b = (if c = b then l c else 0) + (if c < b then (-1 : ℂ) else 0)`.

Introduce `b`. Simplify using `only [hB, Formalism.REAL.Amat, Matrix.of_apply]`. Distinguish the cases in `h : c = b`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Establish `hc : (univ.filter fun b : Fin n => c < b).card = n - 1 - (c : ℕ)`. Rewrite using `[Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Establish `hc' : ((n - 1 - (c : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - ((c : ℕ) : ℂ)`. Use `c.isLt` as an intermediate fact.

Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_filter, Finset.sum_const, hc]`.

Simplify using `only [nsmul_eq_mul, hc']`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∑ a, ∑ b, (B ^ 2) a b = ∑ c, (∑ a, B a c) * ∑ b, B c b`. Simplify using `only [pow_two, Matrix.mul_apply]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul_sum]`. Rewrite using `[h1]`. Simplify using `only [hcol, hrow]`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [hl, rhoV]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gelfVal_two_eq (n : ℕ) (χ : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal χ 2 = ∑ a, χ a ^ 2 - ∑ a, ((rhoV n a : ℝ) : ℂ) ^ 2 := by
  unfold GlobalTheory.Dec.gelfVal
  set l : Fin n → ℂ := fun c => χ c + ((n : ℂ) - 1) / 2 with hl
  set B := Formalism.REAL.Amat l with hB
  have hcol : ∀ c, ∑ a, B a c = l c - ((c : ℕ) : ℂ) := by
    intro c
    have e : ∀ a, B a c = (if a = c then l c else 0) + (if a < c then (-1 : ℂ) else 0) := by
      intro a
      simp only [hB, Formalism.REAL.Amat, Matrix.of_apply]
      by_cases h : a = c
      · subst h
        simp
      · simp [h]
    have hc : (univ.filter fun a : Fin n => a < c).card = (c : ℕ) := by
      rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, hc]
    simp [sub_eq_add_neg]
  have hrow : ∀ c, ∑ b, B c b = l c - ((n : ℂ) - 1 - ((c : ℕ) : ℂ)) := by
    intro c
    have e : ∀ b, B c b = (if c = b then l c else 0) + (if c < b then (-1 : ℂ) else 0) := by
      intro b
      simp only [hB, Formalism.REAL.Amat, Matrix.of_apply]
      by_cases h : c = b
      · subst h
        simp
      · simp [h]
    have hc : (univ.filter fun b : Fin n => c < b).card = n - 1 - (c : ℕ) := by
      rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hc' : ((n - 1 - (c : ℕ) : ℕ) : ℂ) = (n : ℂ) - 1 - ((c : ℕ) : ℂ) := by
      have := c.isLt
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Finset.sum_filter, Finset.sum_const, hc]
    simp only [nsmul_eq_mul, hc']
    ring
  have h1 : ∑ a, ∑ b, (B ^ 2) a b = ∑ c, (∑ a, B a c) * ∑ b, B c b := by
    simp only [pow_two, Matrix.mul_apply]
    calc ∑ a, ∑ b, ∑ c, B a c * B c b = ∑ a, ∑ c, ∑ b, B a c * B c b :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ b, B a c * B c b := Finset.sum_comm
      _ = _ := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul_sum]
  rw [h1]
  simp only [hcol, hrow]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hl, rhoV]
  push_cast
  ring

/- English proof (translation)
Simplify using `only [Module.End.mul_apply, lft_apply, rgt_apply, hP, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_neg, Finset.sum_neg_distrib, neg_inj]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hN]`. Simplify using `[Matrix.conjTranspose_apply]`.
-/
theorem skew_term {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : Module.End ℂ V) (M N : Matrix ι ι ℂ) (hP : ∀ x y : V, ⟪P x, y⟫_ℂ = -⟪x, Q y⟫_ℂ) (hN : Mᴴ = N) (x y : ι → V) :
    ∑ i, ⟪(lft ι P * rgt V M) x i, y i⟫_ℂ = -∑ i, ⟪x i, (lft ι Q * rgt V N) y i⟫_ℂ := by
  simp only [Module.End.mul_apply, lft_apply, rgt_apply, hP, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, mul_neg, Finset.sum_neg_distrib, neg_inj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hN]
  simp [Matrix.conjTranspose_apply]

/- English proof (translation)
Establish `hx : ∀ (z : ι → V) (i : ι), dirac P c z i = ∑ a, ∑ b, (lft ι (P a b) * rgt V (c b a)) z i`. Introduce `z i`. Simplify using `[dirac, LinearMap.sum_apply, Finset.sum_apply]`. Simplify using `only [hx, sum_inner, inner_sum]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_comm]`. Simplify using `only [Finset.sum_neg_distrib]`. Use `_ = -∑ i, ∑ a, ∑ b, ⟪x i, (lft ι (P a b) * rgt V (c b a)) y i⟫_ℂ := by`. Rewrite using `[neg_inj]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem dirac_skew {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Fin n → Module.End ℂ V) (c : Fin n → Fin n → Matrix ι ι ℂ)
    (hP : ∀ a b (x y : V), ⟪P a b x, y⟫_ℂ = -⟪x, P b a y⟫_ℂ) (hc : ∀ a b, (c a b)ᴴ = c b a) (x y : ι → V) :
    ∑ i, ⟪dirac P c x i, y i⟫_ℂ = -∑ i, ⟪x i, dirac P c y i⟫_ℂ := by
  have hx : ∀ (z : ι → V) (i : ι), dirac P c z i = ∑ a, ∑ b, (lft ι (P a b) * rgt V (c b a)) z i := by
    intro z i
    simp [dirac, LinearMap.sum_apply, Finset.sum_apply]
  simp only [hx, sum_inner, inner_sum]
  calc ∑ i, ∑ a, ∑ b, ⟪(lft ι (P a b) * rgt V (c b a)) x i, y i⟫_ℂ
      = ∑ a, ∑ i, ∑ b, ⟪(lft ι (P a b) * rgt V (c b a)) x i, y i⟫_ℂ := Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ i, ⟪(lft ι (P a b) * rgt V (c b a)) x i, y i⟫_ℂ :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, -∑ i, ⟪x i, (lft ι (P b a) * rgt V (c a b)) y i⟫_ℂ :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => skew_term _ _ _ _ (hP a b) (hc b a) x y
    _ = -∑ b, ∑ a, ∑ i, ⟪x i, (lft ι (P b a) * rgt V (c a b)) y i⟫_ℂ := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_neg_distrib]
    _ = -∑ i, ∑ a, ∑ b, ⟪x i, (lft ι (P a b) * rgt V (c b a)) y i⟫_ℂ := by
        rw [neg_inj]
        calc ∑ b, ∑ a, ∑ i, ⟪x i, (lft ι (P b a) * rgt V (c a b)) y i⟫_ℂ
            = ∑ b, ∑ i, ∑ a, ⟪x i, (lft ι (P b a) * rgt V (c a b)) y i⟫_ℂ :=
              Finset.sum_congr rfl fun b _ => Finset.sum_comm
          _ = _ := Finset.sum_comm

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[h.1]`. Use `split_ifs`. Rewrite using `[two_smul, one_add_one_eq_two]`. Both sides reduce to the same expression.
-/
theorem cliff_hg {c : Fin n → Fin n → Matrix ι ι ℂ} (h : IsCliff c) (a b d e : Fin n) :
    c a b * c d e + c d e * c a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Matrix ι ι ℂ) else 0 := by
  rw [h.1]
  split_ifs
  · rw [two_smul, one_add_one_eq_two]
  · rfl

/- English proof (translation)
The claim follows from `s_gl (g := c) (cliff_hg h)`.
-/
theorem spinM_glRel (c : Fin n → Fin n → Matrix ι ι ℂ) (h : IsCliff c) : Formalism.REAL.GlRel (spinM c) :=
  s_gl (g := c) (cliff_hg h)

/- English proof (translation)
The claim follows from `s_cas (g := c) (cliff_hg h)`.
-/
theorem spinM_cas (c : Fin n → Fin n → Matrix ι ι ℂ) (h : IsCliff c) :
    Formalism.REAL.Cas (spinM c) = (((n : ℂ) ^ 3 - n) / 4) • (1 : Matrix ι ι ℂ) :=
  s_cas (g := c) (cliff_hg h)

end Misc

section Ring

variable {n : ℕ} {R : Type} [Ring R]

/- English proof (translation)
Unfold `Formalism.REAL.Cas`. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `noncomm_ring`.
-/
theorem cas_p_add_k (E1 E2 : Fin n → Fin n → R) :
    (∑ a, ∑ b, (E1 a b - E2 a b) * (E1 b a - E2 b a)) + Formalism.REAL.Cas (fun a b => E1 a b + E2 a b) =
      2 * Formalism.REAL.Cas E1 + 2 * Formalism.REAL.Cas E2 := by
  unfold Formalism.REAL.Cas
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  noncomm_ring

/- English proof (translation)
Establish `h1 : ∑ a, ∑ b, s a b * k b a = ∑ a, ∑ b, k a b * s b a`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm`. Establish `h2 : (2 : R) * (∑ a, ∑ b, k a b * s b a) = (∑ a, ∑ b, k a b * s b a) + ∑ a, ∑ b, s a b * k b a`. Rewrite using `[h1, two_mul]`.

Rewrite using `[h2]`. Unfold `Formalism.REAL.Cas`. Simplify using `only [add_mul, mul_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem cas_add (k s : Fin n → Fin n → R) (h : ∀ a b c d, k a b * s c d = s c d * k a b) :
    Formalism.REAL.Cas (fun a b => k a b + s a b) =
      Formalism.REAL.Cas k + 2 * (∑ a, ∑ b, k a b * s b a) + Formalism.REAL.Cas s := by
  have h1 : ∑ a, ∑ b, s a b * k b a = ∑ a, ∑ b, k a b * s b a := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => (h a b b a).symm
  have h2 : (2 : R) * (∑ a, ∑ b, k a b * s b a) = (∑ a, ∑ b, k a b * s b a) + ∑ a, ∑ b, s a b * k b a := by
    rw [h1, two_mul]
  rw [h2]
  unfold Formalism.REAL.Cas
  simp only [add_mul, mul_add, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Introduce `a b c d`. Establish `e : (k a b + s a b) * (k c d + s c d) - (k c d + s c d) * (k a b + s a b) = (k a b * k c d - k c d * k a b) + (s a b * s c d - s c d * s a b)`. Establish `h1` using `h a b c d`. Establish `h2` using `h c d a b`. Simplify using `only [add_mul, mul_add]`.

Rewrite using `[h1, h2]`. Normalize the expressions using the abelian group laws. Simplify using `only []`. Rewrite using `[e, hk a b c d, hs a b c d]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel`.
-/
theorem glRel_add (k s : Fin n → Fin n → R) (hk : Formalism.REAL.GlRel k) (hs : Formalism.REAL.GlRel s)
    (h : ∀ a b c d, k a b * s c d = s c d * k a b) : Formalism.REAL.GlRel (fun a b => k a b + s a b) := by
  intro a b c d
  have e : (k a b + s a b) * (k c d + s c d) - (k c d + s c d) * (k a b + s a b) =
      (k a b * k c d - k c d * k a b) + (s a b * s c d - s c d * s a b) := by
    have h1 := h a b c d
    have h2 := h c d a b
    simp only [add_mul, mul_add]
    rw [h1, h2]
    abel
  simp only []
  rw [e, hk a b c d, hs a b c d]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2] <;> abel

/- English proof (translation)
Establish `e : (E1 a b - E2 a b) * (E1 c d - E2 c d) - (E1 c d - E2 c d) * (E1 a b - E2 a b) = (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b)`. Establish `h3` using `h a b c d`. Establish `h4` using `h c d a b`. Simplify using `only [sub_mul, mul_sub]`. Rewrite using `[h3, h4]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, h1 a b c d, h2 a b c d]`. Apply the tactic sequence `by_cases h5 : b = c <;> by_cases h6 : d = a <;> simp [h5, h6] <;> abel`.
-/
theorem bracket_p (E1 E2 : Fin n → Fin n → R) (h1 : Formalism.REAL.GlRel E1) (h2 : Formalism.REAL.GlRel E2)
    (h : ∀ a b c d, E1 a b * E2 c d = E2 c d * E1 a b) (a b c d : Fin n) :
    (E1 a b - E2 a b) * (E1 c d - E2 c d) - (E1 c d - E2 c d) * (E1 a b - E2 a b) =
      (if b = c then E1 a d + E2 a d else 0) - (if d = a then E1 c b + E2 c b else 0) := by
  have e : (E1 a b - E2 a b) * (E1 c d - E2 c d) - (E1 c d - E2 c d) * (E1 a b - E2 a b) =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    have h3 := h a b c d
    have h4 := h c d a b
    simp only [sub_mul, mul_sub]
    rw [h3, h4]
    abel
  rw [e, h1 a b c d, h2 a b c d]
  by_cases h5 : b = c <;> by_cases h6 : d = a <;> simp [h5, h6] <;> abel

/- English proof (translation)
Introduce `a b c d`. Establish `h1` using `congrArg f (h a b c d)`. Simplify using `only [map_sub, map_mul] at h1`. Simplify using `only []`. Rewrite using `[h1]`.

Apply the tactic sequence `by_cases h5 : b = c <;> by_cases h6 : d = a <;> simp [h5, h6]`.
-/
theorem glRel_map {S : Type} [Ring S] (f : R →+* S) {E : Fin n → Fin n → R} (h : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (fun a b => f (E a b)) := by
  intro a b c d
  have h1 := congrArg f (h a b c d)
  simp only [map_sub, map_mul] at h1
  simp only []
  rw [h1]
  by_cases h5 : b = c <;> by_cases h6 : d = a <;> simp [h5, h6]

end Ring

section Gel

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Simplify using `[gelA, epow, Formalism.REAL.Cas]`.
-/
theorem gelA_two (E : Fin n → Fin n → Module.End ℂ V) : gelA E 2 = Formalism.REAL.Cas E := by
  simp [gelA, epow, Formalism.REAL.Cas]

/- English proof (translation)
Rewrite using `[gelA_two]`. Unfold `Formalism.REAL.Cas barF`. Rewrite using `[Finset.sum_comm]`. Simplify using the standard rewrite rules.
-/
theorem gelA_bar_two (E : Fin n → Fin n → Module.End ℂ V) : gelA (barF E) 2 = Formalism.REAL.Cas E := by
  rw [gelA_two]
  unfold Formalism.REAL.Cas barF
  rw [Finset.sum_comm]
  simp

end Gel

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h1 : (univ.filter fun b : Fin n => a < b ∧ (true = true)).card = n - 1 - (a : ℕ)`. Simplify using `only [eq_self_iff_true, and_true]`. Rewrite using `[Finset.filter_lt_eq_Ioi, Fin.card_Ioi]`. Establish `h2 : (univ.filter fun b : Fin n => b < a ∧ (true = true)).card = (a : ℕ)`.

Simplify using `only [eq_self_iff_true, and_true]`. Rewrite using `[Finset.filter_gt_eq_Iio, Fin.card_Iio]`. Unfold `Formalism.REAL.rhoC rhoV`. Rewrite using `[h1, h2]`. Establish `ha` using `a.isLt`.

Establish `: ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ)`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem rhoC_true (n : ℕ) : Formalism.REAL.rhoC (fun _ : Fin n => true) = rhoV n := by
  funext a
  have h1 : (univ.filter fun b : Fin n => a < b ∧ (true = true)).card = n - 1 - (a : ℕ) := by
    simp only [eq_self_iff_true, and_true]
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  have h2 : (univ.filter fun b : Fin n => b < a ∧ (true = true)).card = (a : ℕ) := by
    simp only [eq_self_iff_true, and_true]
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  unfold Formalism.REAL.rhoC rhoV
  rw [h1, h2]
  have ha := a.isLt
  have : ((n - 1 - (a : ℕ) : ℕ) : ℝ) = (n : ℝ) - 1 - (a : ℕ) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [this]
  ring

/- English proof (translation)
Use `push_cast`. Rewrite using `[Finset.sum_div]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Unfold `infOf m0`. Apply the tactic sequence `cases s <;> simp <;> ring`.
-/
theorem infOf_sq {n : ℕ} (lam : Fin n → ℤ) (s : Bool) :
    ∑ a, infOf lam s a ^ 2 = (((∑ a, (m0 lam a) ^ 2) / 4 : ℝ) : ℂ) := by
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold infOf m0
  cases s <;> simp <;> ring

/- English proof (translation)
Introduce `n lam V _ _ E1 E2 σ A h ι _ _ c hc τ x hx hK`. Take `⟨hc1, hc2⟩` from `hc`. Establish `hcl : IsCliff c` using `⟨hc1, hc2⟩`. Establish `hp` using `h.pair`. Use `set L := lft (V := V) ι with hL`.

Use `set Rr := rgt (ι := ι) V with hRr`. Use `set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef`. Use `set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef`. Use `set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef`. Use `set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef`.

Use `set D := dirac (pF E1 E2) c with hD`. Establish `hDe : D = ∑ a, ∑ b, p a b * g b a` using `rfl`. Establish `hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b` using `fun a b c' d => lft_mul_rgt _ _`. Establish `hglK : Formalism.REAL.GlRel (kF E1 E2)` using `glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm`. Establish `hGk : Formalism.REAL.GlRel k` using `glRel_map L.toRingHom hglK`.

Establish `hGs : Formalism.REAL.GlRel s` using `glRel_map Rr.toRingHom (spinM_glRel c hcl)`. Establish `hYe : yF (kF E1 E2) c = fun a b => k a b + s a b`. Use function extensionality and compare the values at `a b`. Conclude with `yF_eq _ _ a b`. Establish `hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c)`.

Rewrite using `[hYe]`. Conclude with `glRel_add k s hGk hGs hks`. Establish `hCY` using `Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK`. Establish `hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c)`. Simplify using `[Formalism.REAL.CasK, Formalism.REAL.Cas]`.

Rewrite `hCY` using `[hCK, rhoC_true]`. Establish `hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0`. Introduce `a b d e`. Establish `h1` using `congrArg Rr (cliff_hg hcl a b d e)`. Simplify using `only [map_add, map_mul] at h1`.

Rewrite using `[show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]`. Use `split_ifs`. Rewrite using `[map_smul, map_one]`. Conclude with `map_zero Rr`. Establish `hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b = (if b = c' then k a d else 0) - (if d = a then k c' b else 0)`.

Introduce `a b c' d`. Establish `h1` using `congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)`. Simplify using `only [map_sub, map_mul] at h1`. Establish `h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) - L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b)` using `rfl`. Rewrite using `[h2]`.

Simplify using `only [map_sub]`. Rewrite using `[h1]`. Apply the tactic sequence `by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]`. Establish `hsq` using `dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)`. Establish `hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) = s d a`.

Introduce `d a`. Establish `: s d a = Rr (spinM c d a)` using `rfl`. Rewrite using `[this]`. Unfold `spinM`. Apply the tactic sequence `by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]`.

Simplify using `only [hsE] at hsq`. Rewrite `hsq` using `[← hDe]`. Establish `hCasY` using `cas_add k s hks`. Rewrite `hCasY` using `[← hYe]`. Establish `hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k = L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2))`.

Establish `h1` using `congrArg L (cas_p_add_k E1 E2)`. Simplify using `only [two_mul] at h1`. Rewrite using `[← h1]`. Simplify using `[Formalism.REAL.Cas, map_add, map_sum, map_mul, hpdef, hkdef, pF, kF]`. Establish `hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V))`.

Establish `h1` using `congrArg Rr (spinM_cas c hcl)`. Simplify using `only [map_smul, map_one] at h1`. Rewrite using `[← h1]`. Simplify using `[Formalism.REAL.Cas, map_sum, map_mul, hsdef]`. Establish `hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) = L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) + (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V))`.

Rewrite using `[← hCasP, ← hCasS, hsq, hCasY]`. Normalize the expressions using the abelian group laws. Use `set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR`. Use `set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS`. Establish `hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ)`.

Introduce `b`. Rewrite using `[gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v`.

Introduce `v`. Rewrite using `[← gelA_two, h.ch1 2 v, hv]`. Establish `hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v`. Introduce `v`. Rewrite using `[← gelA_bar_two, h.ch2 2 v, hv]`.

Establish `hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ)`. Rewrite using `[hR, sum_rhoV_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT`.

Establish `hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x`. Establish `h1` using `congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot`. Simplify using `only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1`. Rewrite `h1` using `[hCY]`. Establish `h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x = ((4 * (S - R) : ℝ) : ℂ) • x`.

Use function extensionality and compare the values at `i`. Simplify using `only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]`. Use `push_cast`. Use `module`. Rewrite `h1` using `[h2, hn]`.

Rewrite using `[eq_sub_of_add_eq h1]`. Use `push_cast`. Use `module`. Establish `hsk` using `dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)`. Establish `hN : 0 < ∑ i, ‖x i‖ ^ 2`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`. Conclude with `Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by`. Establish `: x i ≠ 0` using `hi`. Use the proof step `positivity⟩`. Establish `hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2` using `Finset.sum_nonneg fun _ _ => by positivity`.

Establish `hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)`. Establish `e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Both sides reduce to the same expression. Establish `e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ = (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ)`. Establish `: dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x` using `hDD`. Rewrite using `[this]`. Use `push_cast`.

Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by`. Rewrite using `[Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[← e1, hsk, e2]`. Establish `hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2)`. Conclude with `hEq` after adjusting the coercions. Establish `hle : 4 * (S - R) + 3 * R - T ≤ 0`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Use `mul_pos hcon hN` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R`. Rewrite using `[hT, hR]`.

Simplify using `only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]`. Rewrite `hle` using `[hT']`. Establish `: ∑ a, (m0 lam a) ^ 2 = 4 * S`. Rewrite using `[hS]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem dirac_ineq : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V),
    IsCoreMod (infOf lam) E1 E2 σ A → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  intro n lam V _ _ E1 E2 σ A h ι _ _ c hc τ x hx hK
  obtain ⟨hc1, hc2⟩ := hc
  have hcl : IsCliff c := ⟨hc1, hc2⟩
  have hp := h.pair

  set L := lft (V := V) ι with hL
  set Rr := rgt (ι := ι) V with hRr
  set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef
  set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef
  set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef
  set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef
  set D := dirac (pF E1 E2) c with hD
  have hDe : D = ∑ a, ∑ b, p a b * g b a := rfl
  have hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b := fun a b c' d => lft_mul_rgt _ _
  have hglK : Formalism.REAL.GlRel (kF E1 E2) := glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm
  have hGk : Formalism.REAL.GlRel k := glRel_map L.toRingHom hglK
  have hGs : Formalism.REAL.GlRel s := glRel_map Rr.toRingHom (spinM_glRel c hcl)
  have hYe : yF (kF E1 E2) c = fun a b => k a b + s a b := by
    funext a b
    exact yF_eq _ _ a b
  have hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c) := by
    rw [hYe]
    exact glRel_add k s hGk hGs hks
  have hCY := Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK
  have hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c) := by
    simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
  rw [hCK, rhoC_true] at hCY

  have hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0 := by
    intro a b d e
    have h1 := congrArg Rr (cliff_hg hcl a b d e)
    simp only [map_add, map_mul] at h1
    rw [show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]
    split_ifs
    · rw [map_smul, map_one]
    · exact map_zero Rr
  have hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b =
      (if b = c' then k a d else 0) - (if d = a then k c' b else 0) := by
    intro a b c' d
    have h1 := congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)
    simp only [map_sub, map_mul] at h1
    have h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) -
        L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b) := rfl
    rw [h2]
    simp only [map_sub]
    rw [h1]
    by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]
  have hsq := dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)
  have hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) =
      s d a := by
    intro d a
    have : s d a = Rr (spinM c d a) := rfl
    rw [this]
    unfold spinM
    by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]
  simp only [hsE] at hsq
  rw [← hDe] at hsq
  have hCasY := cas_add k s hks
  rw [← hYe] at hCasY
  have hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) := by
    have h1 := congrArg L (cas_p_add_k E1 E2)
    simp only [two_mul] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_add, map_sum, map_mul, hpdef, hkdef, pF, kF]
  have hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    have h1 := congrArg Rr (spinM_cas c hcl)
    simp only [map_smul, map_one] at h1
    rw [← h1]
    simp [Formalism.REAL.Cas, map_sum, map_mul, hsdef]
  have hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) +
        (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    rw [← hCasP, ← hCasS, hsq, hCasY]
    abel

  set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR
  set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS
  have hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ) := by
    intro b
    rw [gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]
    push_cast
    rfl
  have hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_two, h.ch1 2 v, hv]
  have hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_bar_two, h.ch2 2 v, hv]
  have hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ) := by
    rw [hR, sum_rhoV_sq]
    push_cast
    ring
  set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT
  have hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := by
    have h1 := congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [hCY] at h1
    have h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x =
        ((4 * (S - R) : ℝ) : ℂ) • x := by
      funext i
      simp only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]
      push_cast
      module
    rw [h2, hn] at h1
    rw [eq_sub_of_add_eq h1]
    push_cast
    module

  have hsk := dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)
  have hN : 0 < ∑ i, ‖x i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by
      have : x i ≠ 0 := hi
      positivity⟩
  have hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by
        rw [inner_self_eq_norm_sq_to_K]
        rfl
    have e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ =
        (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      have : dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := hDD
      rw [this]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
    rw [← e1, hsk, e2]
  have hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2) := by
    exact_mod_cast hEq
  have hle : 4 * (S - R) + 3 * R - T ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hcon hN
    linarith
  have hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R := by
    rw [hT, hR]
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]
  rw [hT'] at hle
  have : ∑ a, (m0 lam a) ^ 2 = 4 * S := by
    rw [hS]
    ring
  rw [this]
  linarith

end GlobalTheory.CompanionTheory.DiracK
