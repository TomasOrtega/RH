import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open IsLocalRing Polynomial Matrix UpperTheory.V

/- English proof (translation)
Introduce `G κ _ _ n a ha W`. Establish `hset : {g | ∀ v ∈ W, a g *ᵥ v ∈ W} = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator, {g | φ (a g *ᵥ v) = 0}`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion.

Introduce `h v hv φ hφ`. Conclude with `(Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ`. Introduce `h v hv`. Conclude with `(Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (fun φ hφ => h v hv φ hφ)`. Rewrite using `[hset]`.

Use `isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_` and prove the remaining obligations. Set `f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ` to `{ toFun := fun M => φ (M *ᵥ v) map_add' := by`. Introduce `M N`. Simplify using `[Matrix.add_mulVec]`. Use the proof step `map_smul' := by`.

Introduce `c M`. Simplify using `only [Matrix.smul_mulVec, map_smul, smul_eq_mul, RingHom.id_apply] }`. Conclude with `ha f`.
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
