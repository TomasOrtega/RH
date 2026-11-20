import Mathlib

namespace GlobalTheory
namespace GenericCharBlock

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem mul_rankOne (Q : Matrix ι ι K) (q a b : K) (hQ : Q * Q = q • Q) :
    (1 + a • Q) * (1 + b • Q) = 1 + (a + b + a * b * q) • Q := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hQ, smul_smul, add_smul, smul_add]
  module

noncomputable def rankOneUnit (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : GL ι K where
  val := 1 + μ • Q
  inv := 1 + (-μ / (1 + μ * q)) • Q
  val_inv := by
    rw [mul_rankOne Q q _ _ hQ]
    have : μ + -μ / (1 + μ * q) + μ * (-μ / (1 + μ * q)) * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]
  inv_val := by
    rw [mul_rankOne Q q _ _ hQ]
    have : -μ / (1 + μ * q) + μ + -μ / (1 + μ * q) * μ * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rankOneUnit_val (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : (rankOneUnit Q q μ hQ hμ).val = 1 + μ • Q := rfl

noncomputable def unip (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) : GL ι K :=
  rankOneUnit Q 0 y (by rw [h, zero_smul]) (by simp)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unip_val (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) :
    (unip Q h y).val = 1 + y • Q := rfl

noncomputable def diagUnit (f : ι → K) (hf : ∀ a, f a ≠ 0) : GL ι K where
  val := diagonal f
  inv := diagonal fun a => (f a)⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact mul_inv_cancel₀ (hf a)
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact inv_mul_cancel₀ (hf a)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem diagUnit_val (f : ι → K) (hf : ∀ a, f a ≠ 0) : (diagUnit f hf).val = diagonal f := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem conj_one_add (B Bi X : Matrix ι ι K) (h : B * Bi = 1) (y : K) :
    B * (1 + y • X) * Bi = 1 + y • (B * X * Bi) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Chain the equalities or inequalities of the calculation.
-/
theorem conj_mul_conj (B Bi X Y : Matrix ι ι K) (h : Bi * B = 1) :
    (B * X * Bi) * (B * Y * Bi) = B * (X * Y) * Bi := by
  calc (B * X * Bi) * (B * Y * Bi) = B * X * (Bi * B) * Y * Bi := by simp only [Matrix.mul_assoc]
    _ = B * (X * Y) * Bi := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem single_eq_smul (i j : ι) (x : K) : single i j x = x • single i j (1 : K) := by
  rw [smul_single, smul_eq_mul, mul_one]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem chi_trivial_of_scaled {A : Type} [CommGroup A] (H : Subgroup (GL ι K)) (χ : H →* A)
    (P : Matrix ι ι K) (hP : P * P = 0)
    (hmem : ∀ y : K, ∃ g : GL ι K, g ∈ H ∧ g.val = 1 + y • P)
    (s : GL ι K) (hs : s ∈ H) (l : K) (hl : l ≠ 1) (hsc : s.val * P = l • (P * s.val))
    (g : GL ι K) (hg : g ∈ H) (y : K) (hgy : g.val = 1 + y • P) : χ ⟨g, hg⟩ = 1 := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.mpr hl
  obtain ⟨g1, hg1, hv1⟩ := hmem (y / (l - 1))
  have hinv : s.val * (s⁻¹ : GL ι K).val = 1 := s.mul_inv
  have key : s * g1 * s⁻¹ = g1 * g := by
    ext1
    simp only [Units.val_mul]
    rw [hv1, hgy]
    have e1 : s.val * (1 + (y / (l - 1)) • P) * (s⁻¹ : GL ι K).val
        = 1 + (y / (l - 1) * l) • P := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinv, Matrix.mul_smul, hsc,
        Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one, smul_smul]
    rw [e1, mul_rankOne P 0 _ _ (by rw [hP, zero_smul])]
    congr 2
    field_simp
    ring
  have e : (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹ : H) = ⟨g1, hg1⟩ * ⟨g, hg⟩ := Subtype.ext key
  have h1 : χ ⟨g1, hg1⟩ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := by
    calc χ ⟨g1, hg1⟩ = χ ⟨s, hs⟩ * χ ⟨g1, hg1⟩ * (χ ⟨s, hs⟩)⁻¹ := by
          rw [mul_comm (χ ⟨s, hs⟩), mul_inv_cancel_right]
      _ = χ (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = χ (⟨g1, hg1⟩ * ⟨g, hg⟩) := by rw [e]
      _ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := map_mul _ _ _
  exact (mul_eq_left.mp h1.symm)

end GenericCharBlock
end GlobalTheory
