import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelLocal

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
private theorem length_addMonoidHom_le_of_card_eq {R A B C X : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
    (f : A →ₗ[R] X) (j : B →ₗ[R] X) (hj : Function.Injective j) (g : B →ₗ[R] C)
    (h : ∀ x, g x = 0 → j x ∈ LinearMap.range f) :
    Module.length R B ≤ Module.length R A + Module.length R C := by
  have hex : Function.Exact (LinearMap.ker g).subtype g.rangeRestrict := by
    intro x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      have := congrArg Subtype.val hx
      simpa [LinearMap.mem_ker] using this
    · rintro ⟨y, rfl⟩
      apply Subtype.ext
      simpa using y.2
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict hex]
  gcongr
  · let φ : LinearMap.ker g →ₗ[R] LinearMap.range f :=
      (j.comp (LinearMap.ker g).subtype).codRestrict (LinearMap.range f) (fun x => h x x.2)
    have hφ : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply hj
      exact congrArg Subtype.val hab
    calc Module.length R (LinearMap.ker g) ≤ Module.length R (LinearMap.range f) :=
          Module.length_le_of_injective φ hφ
      _ ≤ Module.length R A := Module.length_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
  · exact Module.length_le_of_injective (LinearMap.range g).subtype (Submodule.subtype_injective _)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Base.selDown :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R (selEig ρ U' h𝒟 U 1) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) + Module.length R (resCoker ρ h) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U _ h 𝒟 h𝒟 ι _ D hD hcov
  have hinv : ∀ x : selEig ρ U' h𝒟 U 1,
      ((x : LocSel ρ U' 𝒟) : H1U ρ U') ∈ invariantsUnderSubgroupH1 ρ U U' := by
    intro x
    rw [Representation.mem_invariants]
    intro u
    have := (mem_eig.mp x.2) u
    simpa [selRep, Representation.subrepresentation] using congrArg Subtype.val this
  let j : selEig ρ U' h𝒟 U 1 →ₗ[R] H1U ρ U' :=
    (LocSel ρ U' 𝒟).subtype.comp (selEig ρ U' h𝒟 U 1).subtype
  let g : selEig ρ U' h𝒟 U 1 →ₗ[R] resCoker ρ h :=
    (Submodule.mkQ _).comp (LinearMap.codRestrict (invariantsUnderSubgroupH1 ρ U U') j hinv)
  let A := Submodule.comap (resU ρ h) (LocSel ρ U' 𝒟)
  have hj : Function.Injective j := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact hab
  have hker : ∀ x, g x = 0 → j x ∈ LinearMap.range ((resU ρ h).comp A.subtype) := by
    intro x hx
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨y, ?_⟩, hy⟩
    show resU ρ h y ∈ LocSel ρ U' 𝒟
    rw [hy]
    exact (x : LocSel ρ U' 𝒟).2
  refine le_trans (length_addMonoidHom_le_of_card_eq ((resU ρ h).comp A.subtype) j hj g hker) ?_
  gcongr
  exact selLocal R G M ρ U' U h 𝒟 ι D hD hcov
