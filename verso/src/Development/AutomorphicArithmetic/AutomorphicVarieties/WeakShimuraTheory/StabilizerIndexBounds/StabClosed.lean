import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.isClosed_setOf_matrix_stabilizes_submodule :
    ∀ (G κ : Type) [TopologicalSpace G] [Field κ] (n : ℕ) (a : G → Matrix (Fin n) (Fin n) κ), Pr.LinClosed a →
      ∀ W : Submodule κ (Fin n → κ), IsClosed {g | ∀ v ∈ W, a g *ᵥ v ∈ W} := by
  intro G κ _ _ n a ha W
  have hset : {g | ∀ v ∈ W, a g *ᵥ v ∈ W} =
      ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator, {g | φ (a g *ᵥ v) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h v hv φ hφ
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ
    · intro h v hv
      exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (fun φ hφ => h v hv φ hφ)
  rw [hset]
  refine isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_
  let f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ :=
    { toFun := fun M => φ (M *ᵥ v)
      map_add' := by
        intro M N
        simp [Matrix.add_mulVec]
      map_smul' := by
        intro c M
        simp only [Matrix.smul_mulVec, map_smul, smul_eq_mul, RingHom.id_apply] }
  exact ha f
