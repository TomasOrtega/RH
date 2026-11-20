import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.PlaneSU

open Matrix

section PlaneFacts

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem planeFacts_hE_conj (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix (Fin M) (Fin M) E)
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin M → E) : σ (hE σ J x y) = hE σ J y x := by
  unfold hE Formalism.UG.hform
  simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem planeFacts_cTJ_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k : Fin 2) (j : Fin M) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) k j = ∑ i, σ (![e₁, e₂] k i) * J i j := by
  simp [Matrix.mul_apply, Formalism.UG.cT, planeA]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem planeFacts_gram_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (k l : Fin 2) :
    (Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J * planeA e₁ e₂) k l = hE σ J (![e₁, e₂] k) (![e₁, e₂] l) := by
  rw [Matrix.mul_apply]
  simp_rw [planeFacts_cTJ_apply]
  simp only [planeA, Matrix.of_apply, hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion repeatedly using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem planeFacts_mulVec_apply (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E)
    (v : Fin M → E) (k : Fin 2) :
    ((Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J) *ᵥ v) k = hE σ J (![e₁, e₂] k) v := by
  simp only [Matrix.mulVec, dotProduct]
  simp_rw [planeFacts_cTJ_apply]
  simp only [hE, Formalism.UG.hform, Finset.sum_mul, AlgHom.coe_toRingHom]
  rw [Finset.sum_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem planeB_facts : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ ∧ σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ ∧ planeB σ J e₁ e₂ * planeA e₁ e₂ = 1 ∧ Formalism.UG.cT (σ : E →+* E) (planeA e₁ e₂) * J = planeH σ J e₁ e₂ * planeB σ J e₁ e₂ ∧ J * planeA e₁ e₂ = Formalism.UG.cT (σ : E →+* E) (planeB σ J e₁ e₂) * planeH σ J e₁ e₂ ∧ ∀ v : Fin M → E, (planeB σ J e₁ e₂).mulVec v = 0 ↔ (hE σ J e₁ v = 0 ∧ hE σ J e₂ v = 0) := by
  intro F E _ _ _ σ hσ M J hJ e₁ e₂ h12 h1 h2
  have hc := planeFacts_hE_conj σ hσ J hJ.1
  have h21 : hE σ J e₂ e₁ = 0 := by rw [← hc, h12, map_zero]
  have s1 : σ (hE σ J e₁ e₁) = hE σ J e₁ e₁ := hc _ _
  have s2 : σ (hE σ J e₂ e₂) = hE σ J e₂ e₂ := hc _ _
  set a₁ := hE σ J e₁ e₁ with ha₁
  set a₂ := hE σ J e₂ e₂ with ha₂
  set A := planeA e₁ e₂ with hA
  have gram : Formalism.UG.cT (σ : E →+* E) A * J * A = planeH σ J e₁ e₂ := by
    ext k l
    rw [planeFacts_gram_apply]
    fin_cases k <;> fin_cases l <;> simp [planeH, h12, h21, ha₁, ha₂]
  have dd : Matrix.diagonal ![a₁⁻¹, a₂⁻¹] * Matrix.diagonal ![a₁, a₂] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have dd' : Matrix.diagonal ![a₁, a₂] * Matrix.diagonal ![a₁⁻¹, a₂⁻¹] = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext k; fin_cases k <;> simp [h1, h2]
  have cTJ : Formalism.UG.cT (σ : E →+* E) J = J := by
    ext i j; simp [Formalism.UG.cT, hJ.1]
  have cTcT : Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := by
    ext i j; simp [Formalism.UG.cT, hσ]
  have cTd : Formalism.UG.cT (σ : E →+* E) (Matrix.diagonal ![a₁⁻¹, a₂⁻¹]) = Matrix.diagonal ![a₁⁻¹, a₂⁻¹] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Formalism.UG.cT, map_inv₀, s1, s2]
  refine ⟨s1, s2, ?_, ?_, ?_, ?_⟩
  · unfold planeB
    rw [← ha₁, ← ha₂, ← hA]
    have gram' : Formalism.UG.cT (σ : E →+* E) A * (J * A) = planeH σ J e₁ e₂ := by rw [← Matrix.mul_assoc, gram]
    simp only [Matrix.mul_assoc]
    rw [gram']
    unfold planeH
    rw [← ha₁, ← ha₂, dd]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, ← Matrix.mul_assoc, ← Matrix.mul_assoc, dd', Matrix.one_mul]
  · unfold planeB planeH
    rw [← ha₁, ← ha₂, ← hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cTJ, cTcT, cTd, Matrix.mul_assoc, Matrix.mul_assoc A, dd, Matrix.mul_one]
  · intro v
    have hv : ∀ k, (planeB σ J e₁ e₂ *ᵥ v) k = ![a₁⁻¹, a₂⁻¹] k * hE σ J (![e₁, e₂] k) v := by
      intro k
      unfold planeB
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal, planeFacts_mulVec_apply]
    constructor
    · intro h
      have k0 := hv 0
      have k1 := hv 1
      rw [h] at k0 k1
      simp only [Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at k0 k1
      exact ⟨(mul_eq_zero.mp k0.symm).resolve_left (inv_ne_zero h1),
        (mul_eq_zero.mp k1.symm).resolve_left (inv_ne_zero h2)⟩
    · rintro ⟨z1, z2⟩
      funext k
      rw [hv]
      fin_cases k <;> simp [z1, z2]

end PlaneFacts

end GlobalTheory.PlaneSU
