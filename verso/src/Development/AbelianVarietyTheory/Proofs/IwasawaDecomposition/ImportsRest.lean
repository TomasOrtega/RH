import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.SignatureFactor

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem Jpq_mul_self (p q : ℕ) : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_factor : ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → p + q = M ∧ (∃ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G) ∧ ∀ A : Matrix (Fin p ⊕ Fin q) (Fin M) ℂ, Aᴴ * Formalism.UG.Jpq p q * A = G → ∃ B : Matrix (Fin M) (Fin p ⊕ Fin q) ℂ, A * B = 1 ∧ B * A = 1 := by
  intro M p q G h
  obtain ⟨e, P, hP⟩ := h
  have hP' : P.valᴴ * (reindex e e G) * P.val = Formalism.UG.Jpq p q := hP
  set Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Units.val (P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) with hQ
  have hPQ : P.val * Q = 1 := by
    rw [hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hG' : Qᴴ * Formalism.UG.Jpq p q * Q = reindex e e G := by
    rw [← hP']
    calc Qᴴ * (P.valᴴ * (reindex e e G) * P.val) * Q
        = (P.val * Q)ᴴ * (reindex e e G) * (P.val * Q) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [hPQ]; simp
  have hdet : G.det ≠ 0 := by
    intro h0
    have h1 : (Formalism.UG.Jpq p q).det = 0 := by
      rw [← hP', Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, h0]; simp
    have h2 := congrArg Matrix.det (Jpq_mul_self p q)
    rw [Matrix.det_mul, h1] at h2
    simp at h2
  refine ⟨?_, ⟨Q.submatrix id e, ?_⟩, ?_⟩
  · simpa using (Fintype.card_congr e).symm
  · ext i j
    have := congrFun (congrFun hG' (e i)) (e j)
    simpa [Matrix.mul_apply] using this
  · intro A hA
    have hBA : (G⁻¹ * (Aᴴ * Formalism.UG.Jpq p q)) * A = 1 := by
      rw [Matrix.mul_assoc, hA]
      exact Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)
    exact ⟨_, (Matrix.mul_eq_one_comm_of_equiv e).mp hBA, hBA⟩

end GlobalTheory.Mem.SignatureFactor
