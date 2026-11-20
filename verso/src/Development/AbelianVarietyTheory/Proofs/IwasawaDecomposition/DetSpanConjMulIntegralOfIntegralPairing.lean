import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThClass
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
open NumberField IsDedekindDomain Formalism.L2.Pj

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Treat this case separately. Treat this case separately.

Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem detSpan_conj_mul_mem_range (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (M M' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) :
    ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M',
      IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  have hc : ∀ a : 𝓞 E, IsCMField.complexConj E (a : E) ∈ (algebraMap (𝓞 E) E).range := fun a =>
    ⟨IsCMField.ringOfIntegersComplexConj E a, IsCMField.coe_ringOfIntegersComplexConj E a⟩
  intro x hx y hy
  unfold GlobalTheory.BetaEx.detSpan at hx hy
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M x).1 hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w, hw, rfl⟩ := (GlobalTheory.BetaEx.mem_detSet M' y).1 hy
      choose A hA using fun i k => h (v i) (hv i) (w k) (hw k)
      refine ⟨(Matrix.of A).det, ?_⟩
      have e1 : IsCMField.complexConj E v.det
          = ((IsCMField.complexConj E : E →+* E).mapMatrix v).det := by
        rw [← RingHom.map_det]; rfl
      rw [RingHom.map_det, e1, ← Matrix.det_transpose w, ← Matrix.det_mul]
      congr 1
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
        Matrix.transpose_apply, hA]
      rfl
    | zero => simpa using Subring.zero_mem _
    | add a b _ _ ha hb => rw [mul_add]; exact Subring.add_mem _ ha hb
    | smul a b _ hb =>
      rw [Algebra.smul_def, mul_left_comm]
      exact Subring.mul_mem _ ⟨a, rfl⟩ hb
  | zero => simpa using Subring.zero_mem _
  | add a b _ _ ha hb => rw [map_add, add_mul]; exact Subring.add_mem _ ha hb
  | smul a b _ hb =>
    rw [Algebra.smul_def, map_mul, mul_assoc]
    exact Subring.mul_mem _ (hc a) hb

end GlobalTheory
