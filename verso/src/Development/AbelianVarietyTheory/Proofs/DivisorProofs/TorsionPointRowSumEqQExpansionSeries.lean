import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootOfUnityExpZModAdditiveCharacterProperties

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exp_two_pi_I_div_pow_eq_mul (N : ℕ) (hN : (N : ℂ) ≠ 0) (d : ℕ) (τ c : ℂ) (j : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * ((d * τ + c) / N)) ^ j
      = Complex.exp (2 * Real.pi * Complex.I * (j * c) / N)
        * Complex.exp (2 * Real.pi * Complex.I * τ / N) ^ (d * j) := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private lemma wpFam_ch_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N ((j : ZMod N) * b)
      = Complex.exp (2 * Real.pi * Complex.I * (j * (b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 ((j * b.val : ℕ) : ℤ)
  have hc : (((j * b.val : ℕ) : ℤ) : ZMod N) = (j : ZMod N) * b := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
private lemma wpFam_ch_neg_natCast_mul (N : ℕ) [NeZero N] (j : ℕ) (b : ZMod N) :
    _root_.GlobalTheory.WpFam.ch N (-((j : ZMod N) * b))
      = Complex.exp (2 * Real.pi * Complex.I * (j * -(b.val : ℂ)) / N) := by
  have h := (_root_.GlobalTheory.WpFam.AddCharZMod.main N).1 (-((j * b.val : ℕ) : ℤ))
  have hc : ((-((j * b.val : ℕ) : ℤ) : ℤ) : ZMod N) = -((j : ZMod N) * b) := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [hc] at h
  rw [h]
  congr 1
  first | (push_cast; ring) | push_cast

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem _root_.GlobalTheory.WpFam.torsion_row_series : ∀ (N : ℕ) [NeZero N] (e : ℕ) (τ : ℍ) (b : ZMod N) (d : ℕ+), 1 ≤ e → (∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) ∧ ∑' m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1) = (-(2 * (Real.pi : ℂ) * Complex.I)) ^ (e + 1) / (e.factorial : ℂ) * ((-1) ^ (e + 1) * ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b)) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ))) := by
  intro N _ e τ b d he
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have him : ∀ c : ℂ, c.im = 0 → 0 < ((((d : ℕ) : ℂ) * τ + c) / N).im := by
    intro c hc
    rw [Complex.div_natCast_im]
    have h1 : (((d : ℕ) : ℂ) * (τ : ℂ) + c).im = ((d : ℕ) : ℝ) * τ.im := by
      simp [Complex.mul_im, hc]
    rw [h1]
    exact div_pos (mul_pos (by exact_mod_cast d.pos) τ.im_pos) hN
  constructor
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N, him _ (Complex.natCast_im _)⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (((j : ℕ) : ZMod N) * b)
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_natCast_mul]
        ring
    rw [h, hS]
    ring
  · have h := EisensteinSeries.qExpansion_identity_pnat he
      ⟨(((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N, him _
        (by rw [Complex.neg_im, Complex.natCast_im, neg_zero])⟩
    simp only [UpperHalfPlane.coe_mk] at h
    have hterm : ∀ m : ℤ, 1 / ((-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m) ^ (e + 1)
        = (-1) ^ (e + 1) * (1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)) := by
      intro m
      rw [show (-((d : ℕ) : ℂ) * τ + (b.val : ℂ)) / N + m
          = -((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) by push_cast; ring]
      rw [neg_pow, one_div, one_div, mul_inv, ← inv_pow, inv_neg, inv_one]
    have hre : ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + ((-m : ℤ) : ℂ)) ^ (e + 1)
        = ∑' m : ℤ, 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1) :=
      (Equiv.neg ℤ).tsum_eq
        (fun m : ℤ => 1 / ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N + (m : ℂ)) ^ (e + 1))
    have hS : (∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * Complex.exp (2 * Real.pi * Complex.I
        * ((((d : ℕ) : ℂ) * τ + -(b.val : ℂ)) / N)) ^ (j : ℕ))
        = ∑' j : ℕ+, ((j : ℕ) : ℂ) ^ e * _root_.GlobalTheory.WpFam.ch N (-(((j : ℕ) : ZMod N) * b))
          * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ ((d : ℕ) * (j : ℕ)) :=
      tsum_congr fun j => by
        rw [exp_two_pi_I_div_pow_eq_mul N hNc, wpFam_ch_neg_natCast_mul]
        ring
    rw [tsum_congr hterm, tsum_mul_left, hre, h, hS]
    ring

end GlobalTheory.WpFam
