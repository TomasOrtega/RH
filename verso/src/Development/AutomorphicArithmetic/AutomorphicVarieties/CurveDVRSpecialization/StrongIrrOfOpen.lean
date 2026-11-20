import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open Matrix

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Pr.strongIrrOfOpen :
    UpperTheory.V.Pr.StrongIrrOfOpen := by
  intro G κ _ _ _ _ n r hlin hirr W S hS hiff
  have hset : (S : Set G) = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator,
      {g | φ (UpperTheory.V.Pr.gm r g *ᵥ v) = 0} := by
    ext g
    simp only [SetLike.mem_coe, hiff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (h v hv)
  have hclosed : IsClosed (S : Set G) := by
    rw [hset]
    refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
    let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
      { toFun := fun M => φ (M *ᵥ v)
        map_add' := by
          intro A B
          simp [Matrix.add_mulVec]
        map_smul' := by
          intro c A
          simp [Matrix.smul_mulVec] }
    exact hlin f
  have hopen : IsOpen (S : Set G) := S.isOpen_of_isClosed_of_finiteIndex hclosed
  apply hirr S hopen W
  intro g hg v hv
  exact (hiff g).mp hg v hv
