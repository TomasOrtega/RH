import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent

noncomputable section

namespace GlobalTheory.ClassMin

open QuadraticMap Module
open scoped Pointwise

section Class

variable {X : Type*} [AddCommGroup X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem mk_eq_mk_iff (N : ℤ) (a b : X) :
    (Submodule.Quotient.mk b : QuotSMulTop N X) = Submodule.Quotient.mk a ↔ ∃ w, b = a + N • w := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨w, _, h⟩ => ⟨w, by rw [h]; abel⟩, fun ⟨w, h⟩ => ⟨w, trivial, by rw [h]; abel⟩⟩

def classMin (Q : QuadraticMap ℤ X ℝ) (N : ℤ) (z : QuotSMulTop N X) : ℝ :=
  sInf ((fun x => Q x / N) '' {x | Submodule.Quotient.mk x = z})

variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Clear the denominators using the available nonvanishing facts.
-/
theorem shifted_zsmul (hN : N ≠ 0) (ν : X →+ ℝ) (μ : X) :
    Q (N • μ) / N + ν (N • μ) = N * (Q μ + ν μ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [QuadraticMap.map_smul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  field_simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem shifted_zsmul_nonneg (hN : 0 < N) {ν : X →+ ℝ} (h : ∀ μ, 0 ≤ Q μ + ν μ) (μ : X) :
    0 ≤ Q (N • μ) / N + ν (N • μ) := by
  rw [shifted_zsmul hN.ne']
  exact mul_nonneg (by exact_mod_cast hN.le) (h μ)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem shifted_lt_add_zsmul {c : ℝ} (hc : 0 ≤ c) (hN : 1 + 2 * c < N) {ν : X →+ ℝ} {e μ : X}
    (hμ : 0 < Q μ) (hF : 0 ≤ Q μ / N + ν μ) (h : |polar Q e μ| ≤ c * polar Q μ μ) :
    Q e / N + ν e < Q (e + N • μ) / N + ν (e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : Q (e + N • μ) / N + ν (e + N • μ) = Q e / N + ν e +
      (polar Q e μ + (N - 1) * Q μ + N * (Q μ / N + ν μ)) := by
    rw [map_add_zsmul, map_add, map_zsmul, zsmul_eq_mul]
    field_simp
    ring
  rw [polar_self, two_smul, abs_le] at h
  have h1 := mul_pos (sub_pos.2 hN) hμ
  have h2 := mul_nonneg hN0.le hF
  rw [e1]
  nlinarith [h.1]

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem exists_basis_neg {ι : Type*} (e : Basis ι ℤ X) {ν : X →+ ℝ} (hν : ν ≠ 0) :
    ∃ i, ν (e i) < 0 ∨ ν (-e i) < 0 := by
  by_contra h
  push Not at h
  refine hν (AddMonoidHom.toIntLinearMap_injective (e.ext fun i => ?_))
  have h2 := (h i).2
  rw [map_neg] at h2
  simpa using le_antisymm (by linarith) (h i).1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem realExtension_eq_realExt (Q : QuadraticMap ℤ X ℝ) : realExtension Q = realExt Q :=
  eq_realExt Q _ (realExtension_one_tmul Q)

end Class

section Main

variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ} {N : ℤ} {d : ℕ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Reduce the argument to an intermediate assertion. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_shifted_lt (hd : finrank ℤ X = d) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * d * (2 : ℝ) ^ ((d : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  have hP := posDef_of_posDef_realExt hQ
  have hc : (0 : ℝ) ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  rw [mul_assoc] at hN
  have hN1 : (1 : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have : (1 : ℤ) < N := by exact_mod_cast hN1
    omega
  have hN0 : (0 : ℝ) < N := by linarith
  suffices H : ∃ α : X, (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N by
    obtain ⟨α, h1, h2⟩ := H
    refine ⟨α, ?_, h1, h2⟩
    rintro w rfl
    have h3 := h2 (-w)
    rw [smul_neg, add_neg_cancel, map_zero, zero_div] at h3
    exact h3.not_ge (shifted_zsmul_nonneg (by omega) h w)
  obtain ⟨a, ha⟩ := exists_global_min (realExtension_eq_realExt Q ▸ hQ) ν hN0
  by_cases hX : ∃ u, a = N • u
  · obtain ⟨u, rfl⟩ := hX
    have hF : ∀ x, 0 ≤ Q x / N + ν x := fun x => (shifted_zsmul_nonneg (by omega) h u).trans (ha x)
    obtain ⟨e, he, -⟩ := exists_reduced_basis_pairing_coord hd Q hQ
    obtain ⟨v, hv, hvp⟩ : ∃ v, ν v < 0 ∧
        ∀ μ, |polar Q v μ| ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) * polar Q μ μ := by
      obtain ⟨i, hi | hi⟩ := exists_basis_neg e hν
      · exact ⟨_, hi, he i⟩
      · exact ⟨_, hi, fun μ => by rw [polar_neg_left, abs_neg]; exact he i μ⟩
    refine ⟨v, fun w hw => shifted_lt_add_zsmul hc hN (hP w hw) (hF w) (hvp w), fun w => ?_⟩
    refine (add_lt_of_neg_right _ hv).trans_le (div_le_div_of_nonneg_right ?_ hN0.le)
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (lt_add_smul_of_abs_polar_le Q hc (by linarith) (hP w hw) (hvp w)).1.le
  · refine ⟨a, fun w => lt_of_global_min hP ν hN2 ha, fun w => ?_⟩
    have h0 := ha 0
    rw [map_zero, map_zero, zero_div, add_zero] at h0
    refine h0.trans_lt (div_pos (hP _ fun hw => hX ⟨-w, ?_⟩) hN0)
    rw [smul_neg, eq_neg_iff_add_eq_zero, hw]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_shifted_lt_of_le {g : ℕ} (hg : finrank ℤ X ≤ g) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * g * (2 : ℝ) ^ ((g : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  refine exists_shifted_lt rfl hQ (lt_of_le_of_lt ?_ hN) hν h
  have := pairing_const_mono hg
  rw [mul_assoc, mul_assoc]
  linarith

end Main

section Matrix

open ReciprocityTheory.ReducedBases (SameClass IsMinInClass IsUniqueMinInClass)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
example : ∃ (A : Matrix (Fin 1) (Fin 1) ℝ) (ν : (Fin 1 → ℤ) →+ ℝ), A.PosDef ∧ ν ≠ 0 ∧
    (∀ μ, 0 ≤ ReciprocityTheory.ReducedBases.Q A μ + ν μ) ∧
    1 + 2 * (1 : ℕ) * (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) < (4 : ℤ) := by
  refine ⟨Matrix.diagonal fun _ => 2,
    (Int.castAddHom ℝ).comp (Pi.evalAddMonoidHom (fun _ => ℤ) 0),
    Matrix.PosDef.diagonal fun _ => two_pos, fun h => ?_, fun μ => ?_, ?_⟩
  · simpa using DFunLike.congr_fun h 1
  · have h1 : 0 ≤ μ 0 ^ 2 + μ 0 := by nlinarith [Int.le_self_sq (-μ 0)]
    have h2 : (0 : ℝ) ≤ (μ 0 : ℝ) ^ 2 + μ 0 := by exact_mod_cast h1
    simp [ReciprocityTheory.ReducedBases.Q, ReciprocityTheory.ReducedBases.polar, ReciprocityTheory.ReducedBases.toReal, dotProduct, Matrix.mulVec]
    linarith
  · have h1 := rpow_half_sq 1
    have h2 : (2 : ℝ) ^ (((1 : ℕ) : ℝ) / 2) < 3 / 2 :=
      lt_of_pow_lt_pow_left₀ 2 (by norm_num) (by rw [h1]; norm_num)
    push_cast at h2 ⊢
    linarith

end Matrix

end GlobalTheory.ClassMin

end
