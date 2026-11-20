import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.GLift

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Simplify to obtain the desired conclusion from the available facts.

Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Assume the hypotheses and unpack their components.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem glO_isOpen_isCompact : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F] (n : ℕ), IsOpen (glO n F) ∧ IsCompact (glO n F) := by
  intro F _ _ _ n
  let B : Set (Matrix (Fin n) (Fin n) F) :=
    Set.pi Set.univ (fun _ : Fin n => Set.pi Set.univ (fun _ : Fin n => Metric.closedBall (0 : F) 1))
  have hB : ∀ A : Matrix (Fin n) (Fin n) F, A ∈ B ↔ ∀ i j, ‖A i j‖ ≤ 1 := by
    intro A
    constructor
    · intro h i j
      have := h i (Set.mem_univ _) j (Set.mem_univ _)
      simpa using this
    · intro h i _ j _
      simpa using h i j
  have hBo : IsOpen B :=
    isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => IsUltrametricDist.isOpen_closedBall _ one_ne_zero
  have hBc : IsCompact B :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  let S : Set (Matrix (Fin n) (Fin n) F × (Matrix (Fin n) (Fin n) F)ᵐᵒᵖ) :=
    B ×ˢ (MulOpposite.unop ⁻¹' B)
  have hS : glO n F = Units.embedProduct _ ⁻¹' S := by
    ext g
    simp only [glO, Set.mem_setOf_eq, Set.mem_preimage, S, Set.mem_prod, hB, Units.embedProduct_apply,
      MulOpposite.unop_op]
    constructor
    · intro h; exact ⟨fun i j => (h i j).1, fun i j => (h i j).2⟩
    · intro h i j; exact ⟨h.1 i j, h.2 i j⟩
  have hSo : IsOpen S := hBo.prod (hBo.preimage MulOpposite.continuous_unop)
  have hSc : IsCompact S := by
    refine hBc.prod ?_
    have : MulOpposite.unop ⁻¹' B = MulOpposite.op '' B := by
      ext x
      constructor
      · intro h; exact ⟨_, h, MulOpposite.op_unop x⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [this]; exact hBc.image MulOpposite.continuous_op
  rw [hS]
  exact ⟨hSo.preimage Units.continuous_embedProduct,
    Units.isClosedEmbedding_embedProduct.isCompact_preimage hSc⟩

end GlobalTheory.JR.GLift
