import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.ClPullApply

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Introduce `K Ω _ _ _ _ _`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K`. Use `haveI : Normal K Ω := IsAlgClosure.normal K Ω`. Use `set L := GroundTheory.Global.hilbertClassField K Ω`. Establish `hL : IsOpen ((AlgEquiv.restrictNormalHom (F` using `K) (K₁ := Ω) L).ker : Set (G K Ω)) := by`.

Rewrite using `[IntermediateField.restrictNormalHom_ker]`. Conclude with `IntermediateField.fixingSubgroup_isOpen L`. Establish `hker : (AlgEquiv.restrictNormalHom (F` using `K) (K₁ := Ω) L).ker ≤ (artCl K Ω).ker := by`. Introduce `x hx`. Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`.

Use `show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L x) = 1`. Rewrite using `[hx, map_one]`. Establish `hopen : IsOpen ((artCl K Ω).ker : Set (G K Ω))` using `Subgroup.isOpen_mono hker hL`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `y`.

Take `⟨σ, hσ⟩` from `AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω y)`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use `show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L σ) = y`. Rewrite using `[hσ, MulEquiv.symm_apply_apply]`. Rewrite using `[IsLocallyConstant.iff_isOpen_fiber]`.

Introduce `y`. Distinguish the cases in `hy : ∃ g, artCl K Ω g = y`. Take `⟨g, rfl⟩` from `hy`. Establish `: (artCl K Ω) ⁻¹' {artCl K Ω g} = (fun x => g⁻¹ * x) ⁻¹' ((artCl K Ω).ker : Set (G K Ω))`. Use extensionality with `x`.

Rewrite using `[Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]`. Rewrite using `[this]`. Conclude with `hopen.preimage (continuous_mul_left g⁻¹)`. Use `push_neg at hy`. Establish `: (artCl K Ω) ⁻¹' {y} = ∅`.

Use extensionality with `x`. Simplify using `[hy x]`. Rewrite using `[this]`. Conclude with `isOpen_empty`.
-/
theorem UpperTheory.V.Kum.artSurj :
    ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], Function.Surjective (artCl K Ω) ∧ IsLocallyConstant (artCl K Ω) := by
  intro K Ω _ _ _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  set L := GroundTheory.Global.hilbertClassField K Ω
  have hL : IsOpen ((AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker : Set (G K Ω)) := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isOpen L
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L).ker ≤ (artCl K Ω).ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L x) = 1
    rw [hx, map_one]
  have hopen : IsOpen ((artCl K Ω).ker : Set (G K Ω)) := Subgroup.isOpen_mono hker hL
  refine ⟨?_, ?_⟩
  · intro y
    obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := L) Ω
      (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω y)
    refine ⟨σ, ?_⟩
    show (GroundTheory.Global.hilbertClassFieldArtinEquiv K Ω).symm (AlgEquiv.restrictNormalHom L σ) = y
    rw [hσ, MulEquiv.symm_apply_apply]
  · rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ g, artCl K Ω g = y
    · obtain ⟨g, rfl⟩ := hy
      have : (artCl K Ω) ⁻¹' {artCl K Ω g} = (fun x => g⁻¹ * x) ⁻¹' ((artCl K Ω).ker : Set (G K Ω)) := by
        ext x
        rw [Set.mem_preimage, Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, eq_comm]
      rw [this]
      exact hopen.preimage (continuous_mul_left g⁻¹)
    · push_neg at hy
      have : (artCl K Ω) ⁻¹' {y} = ∅ := by
        ext x
        simp [hy x]
      rw [this]
      exact isOpen_empty
