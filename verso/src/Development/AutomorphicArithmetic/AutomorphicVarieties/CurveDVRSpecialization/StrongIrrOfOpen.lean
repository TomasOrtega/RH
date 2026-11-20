import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne

open Matrix

/- English proof (translation)
Introduce `G κ _ _ _ _ n r hlin hirr W S hS hiff`. Establish `hset : (S : Set G) = ⋂ v ∈ W, ⋂ φ ∈ W.dualAnnihilator, {g | φ (UpperTheory.V.Pr.gm r g *ᵥ v) = 0}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, hiff, Set.mem_iInter, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `h v hv φ hφ`. Conclude with `(Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mpr (h v hv) φ hφ`. Introduce `h v hv`. Conclude with `(Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp (h v hv)`. Establish `hclosed : IsClosed (S : Set G)`.

Rewrite using `[hset]`. Use `isClosed_biInter fun v _ => isClosed_biInter fun φ _ => ?_` and prove the remaining obligations. Set `f : Matrix (Fin n) (Fin n) κ →ₗ[κ] κ` to `{ toFun := fun M => φ (M *ᵥ v) map_add' := by`. Introduce `A B`. Simplify using `[Matrix.add_mulVec]`.

Use the proof step `map_smul' := by`. Introduce `c A`. Simplify using `[Matrix.smul_mulVec] }`. Conclude with `hlin f`. Establish `hopen : IsOpen (S : Set G)` using `S.isOpen_of_isClosed_of_finiteIndex hclosed`.

Apply `hirr S hopen W` to reduce the goal to its premises. Introduce `g hg v hv`. Conclude with `(hiff g).mp hg v hv`.
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
