import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CqStmt

open NumberField UpperTheory.V.Af.Bc

/- English proof (translation)
Use extensionality with `σ`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, rfl⟩ y hy`. Take `⟨k, rfl⟩` from `AlgHom.mem_fieldRange.mp hy`.

Conclude with `τ.commutes k`. Introduce `h`. Use `⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Both sides reduce to the same expression.
-/
private theorem range_res_eq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] :
    (res F Ω K).range = (IsScalarTower.toAlgHom F K Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff, MonoidHom.mem_range]
  constructor
  · rintro ⟨τ, rfl⟩ y hy
    obtain ⟨k, rfl⟩ := AlgHom.mem_fieldRange.mp hy
    exact τ.commutes k
  · intro h
    refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) fun k => h _ (AlgHom.mem_fieldRange.mpr ⟨k, rfl⟩), ?_⟩
    ext y
    rfl

/- English proof (translation)
Establish `hK` using `InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange`. Establish `hK'` using `InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange`. Rewrite `h` using `[range_res_eq, range_res_eq]`. Establish `he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange`. Rewrite using `[← hK, ← hK', h]`.

Establish `he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range`. Rewrite using `[← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]`. Conclude with `⟨(AlgEquiv.ofInjectiveField _).trans ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩`.
-/
private theorem equiv_of_range {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω] (K K' : Type) [Field K] [Algebra F K]
    [Algebra K Ω] [IsScalarTower F K Ω] [Field K'] [Algebra F K'] [Algebra K' Ω] [IsScalarTower F K' Ω]
    (h : (res F Ω K).range = (res F Ω K').range) : Nonempty (K ≃ₐ[F] K') := by
  have hK := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K Ω).fieldRange
  have hK' := InfiniteGalois.fixedField_fixingSubgroup (IsScalarTower.toAlgHom F K' Ω).fieldRange
  rw [range_res_eq, range_res_eq] at h
  have he : (IsScalarTower.toAlgHom F K Ω).fieldRange = (IsScalarTower.toAlgHom F K' Ω).fieldRange := by
    rw [← hK, ← hK', h]
  have he' : (IsScalarTower.toAlgHom F K Ω).range = (IsScalarTower.toAlgHom F K' Ω).range := by
    rw [← AlgHom.fieldRange_toSubalgebra, ← AlgHom.fieldRange_toSubalgebra, he]
  exact ⟨(AlgEquiv.ofInjectiveField _).trans
    ((Subalgebra.equivOfEq _ _ he').trans (AlgEquiv.ofInjectiveField _).symm)⟩

/- English proof (translation)
Introduce `K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq`. Take `⟨e⟩` from `equiv_of_range K K' heq`. Rewrite `hcop` using `[← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff]`. Use `NumberField.abs_discr_gt_two (K := K) (by omega)` as an intermediate fact. Apply the tactic sequence `rcases hcop with h | h <;> rw [h] at this <;> norm_num at this`.
-/
theorem UpperTheory.V.Br.signNe :
    UpperTheory.V.Br.SignNe := by
  intro K K' Ω _ _ _ _ _ _ _ _ _ _ _ hK hcop heq
  obtain ⟨e⟩ := equiv_of_range K K' heq
  rw [← NumberField.discr_eq_discr_of_algEquiv (K := K) e, isCoprime_self, Int.isUnit_iff] at hcop
  have := NumberField.abs_discr_gt_two (K := K) (by omega)
  rcases hcop with h | h <;> rw [h] at this <;> norm_num at this
