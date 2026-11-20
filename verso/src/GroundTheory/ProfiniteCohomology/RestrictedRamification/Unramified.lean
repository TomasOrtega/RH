import Mathlib
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Ramification

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain

open scoped Pointwise

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

omit [NumberField F] in

/- English proof (translation)
The claim follows from `Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap (IntermediateField.inclusion_injective h)`.
-/
theorem finiteDimensional_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M] :
    FiniteDimensional F E :=
  Module.Finite.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

/- English proof (translation)
Establish `: FiniteDimensional F E` using `finiteDimensional_of_le h`. Set `_ : Algebra E M` to `(IntermediateField.inclusion h).toAlgebra`. Establish `: IsScalarTower F E M` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `NumberField.of_module_finite F M` as an intermediate fact. Use `NumberField.of_module_finite F E` as an intermediate fact.

Introduce `P hP hPv`. Take `⟨⟨Q, hQ, hQP⟩⟩` from `(inferInstance : Nonempty (P.primesOver (𝓞 M)))`. Establish `: Q.LiesOver v.asIdeal` using `Ideal.LiesOver.trans Q P v.asIdeal`. Establish `hu` using `((isUnramifiedAt_tower_iff (F := F) (L := E) Q).1 (hM Q hQ this)).1`. Establish `e : P = Q.under (𝓞 E)` using `Ideal.over_def Q P`.

Substitute `e` using the available equality. Conclude with `hu`.
-/
theorem isUnramifiedIn_of_le {E M : IntermediateField F Ω} (h : E ≤ M) [FiniteDimensional F M]
    (v : HeightOneSpectrum (𝓞 F)) (hM : Algebra.IsUnramifiedIn (𝓞 M) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  intro P hP hPv
  obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
  have : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
  have hu := ((isUnramifiedAt_tower_iff (F := F) (L := E) Q).1 (hM Q hQ this)).1
  have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
  subst e
  exact hu

/- English proof (translation)
Establish `: FiniteDimensional F E` using `finiteDimensional_of_le h`. Set `_ : Algebra E M` to `(IntermediateField.inclusion h).toAlgebra`. Establish `: IsScalarTower F E M` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `NumberField.of_module_finite F M` as an intermediate fact. Use `NumberField.of_module_finite F E` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Introduce `hE Q hQ hQv σ hσ x hx`. Establish `: (Q.under (𝓞 E)).LiesOver v.asIdeal` using `⟨by rw [Ideal.under_under]; exact hQv.over⟩`. Establish `hu` using `hE (Q.under (𝓞 E)) inferInstance this`. Conclude with `(isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩`.

Introduce `hI P hP hPv`. Take `⟨⟨Q, hQ, hQP⟩⟩` from `(inferInstance : Nonempty (P.primesOver (𝓞 M)))`. Establish `hQv : Q.LiesOver v.asIdeal` using `Ideal.LiesOver.trans Q P v.asIdeal`. Establish `hu` using `(isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2 (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)`. Establish `e : P = Q.under (𝓞 E)` using `Ideal.over_def Q P`.

Substitute `e` using the available equality. Conclude with `hu`.
-/
theorem isUnramifiedIn_iff_inertia {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        ∀ σ ∈ Q.inertia Gal(M/F), ∀ x (hx : x ∈ E), σ ⟨x, h hx⟩ = ⟨x, h hx⟩ := by
  have : FiniteDimensional F E := finiteDimensional_of_le h
  let _ : Algebra E M := (IntermediateField.inclusion h).toAlgebra
  have : IsScalarTower F E M := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := NumberField.of_module_finite F M
  have := NumberField.of_module_finite F E
  constructor
  · intro hE Q hQ hQv σ hσ x hx
    have : (Q.under (𝓞 E)).LiesOver v.asIdeal := ⟨by rw [Ideal.under_under]; exact hQv.over⟩
    have hu := hE (Q.under (𝓞 E)) inferInstance this
    exact (isUnramifiedAt_under_iff_inertia Q).1 hu σ hσ ⟨x, hx⟩
  · intro hI P hP hPv
    obtain ⟨⟨Q, hQ, hQP⟩⟩ := (inferInstance : Nonempty (P.primesOver (𝓞 M)))
    have hQv : Q.LiesOver v.asIdeal := Ideal.LiesOver.trans Q P v.asIdeal
    have hu := (isUnramifiedAt_under_iff_inertia (F := F) (E := E) Q).2
      (fun σ hσ y => hI Q hQ hQv σ hσ y.1 y.2)
    have e : P = Q.under (𝓞 E) := Ideal.over_def Q P
    subst e
    exact hu

omit [NumberField F] in

/- English proof (translation)
Rewrite using `[IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩`. Introduce and unpack `⟨hx, hfix⟩`.

Conclude with `⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩`.
-/
theorem mem_map_fixedField_iff {M : IntermediateField F Ω} (H : Subgroup Gal(M/F)) (x : Ω) :
    x ∈ (IntermediateField.fixedField H).map M.val ↔ ∃ hx : x ∈ M, ∀ σ ∈ H, σ ⟨x, hx⟩ = ⟨x, hx⟩ := by
  rw [IntermediateField.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, fun σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ⟩
  · rintro ⟨hx, hfix⟩
    exact ⟨⟨x, hx⟩, (IntermediateField.mem_fixedField_iff H _).2 hfix, rfl⟩

/- English proof (translation)
Rewrite using `[isUnramifiedIn_iff_inertia h]`. Use `forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `hI x hx`. Conclude with `(mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩`.

Introduce `hle σ hσ x hx`. Take `⟨_, hfix⟩` from `(mem_map_fixedField_iff _ x).1 (hle hx)`. Conclude with `hfix σ hσ`.
-/
theorem isUnramifiedIn_iff_le_fixedField {E M : IntermediateField F Ω} (h : E ≤ M)
    [FiniteDimensional F M] [IsGalois F M] (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal ↔
      ∀ Q : Ideal (𝓞 M), Q.IsPrime → Q.LiesOver v.asIdeal →
        E ≤ (IntermediateField.fixedField (Q.inertia Gal(M/F))).map M.val := by
  rw [isUnramifiedIn_iff_inertia h]
  refine forall_congr' fun Q => forall_congr' fun _ => forall_congr' fun _ => ?_
  constructor
  · intro hI x hx
    exact (mem_map_fixedField_iff _ x).2 ⟨h hx, fun σ hσ => hI σ hσ x hx⟩
  · intro hle σ hσ x hx
    obtain ⟨_, hfix⟩ := (mem_map_fixedField_iff _ x).1 (hle hx)
    exact hfix σ hσ

variable [IsGalois F Ω]

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_finiteGalois_le (E₁ ⊔ E₂)`. Rewrite using `[isUnramifiedIn_iff_le_fixedField hM]`. Rewrite `h₁` using `[isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)]`. Rewrite `h₂` using `[isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)]`. Conclude with `fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)`.
-/
theorem isUnramifiedIn_sup {E₁ E₂ : IntermediateField F Ω} [FiniteDimensional F E₁]
    [FiniteDimensional F E₂] (v : HeightOneSpectrum (𝓞 F))
    (h₁ : Algebra.IsUnramifiedIn (𝓞 E₁) v.asIdeal) (h₂ : Algebra.IsUnramifiedIn (𝓞 E₂) v.asIdeal) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E₁ ⊔ E₂)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (E₁ ⊔ E₂)
  rw [isUnramifiedIn_iff_le_fixedField hM]
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_left.trans hM)] at h₁
  rw [isUnramifiedIn_iff_le_fixedField (le_sup_right.trans hM)] at h₂
  exact fun Q hQ hQv => sup_le (h₁ Q hQ hQv) (h₂ Q hQ hQv)

/- English proof (translation)
Introduce `v hv` and use `isUnramifiedIn_sup v (h₁ v hv) (h₂ v hv)`.
-/
theorem IsUnramifiedOutside.sup {S : Set (HeightOneSpectrum (𝓞 F))} {E₁ E₂ : IntermediateField F Ω}
    [FiniteDimensional F E₁] [FiniteDimensional F E₂] (h₁ : IsUnramifiedOutside S E₁)
    (h₂ : IsUnramifiedOutside S E₂) : IsUnramifiedOutside S (E₁ ⊔ E₂) :=
  fun v hv => isUnramifiedIn_sup v (h₁ v hv) (h₂ v hv)

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_finiteGalois_le (⊥ : IntermediateField F Ω)`. Rewrite using `[isUnramifiedIn_iff_inertia hM]`. Introduce `Q _ _ σ _ x hx`. Take `⟨a, rfl⟩` from `IntermediateField.mem_bot.1 hx`. Conclude with `σ.commutes a`.
-/
theorem isUnramifiedIn_bot (v : HeightOneSpectrum (𝓞 F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(⊥ : IntermediateField F Ω)) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le (⊥ : IntermediateField F Ω)
  rw [isUnramifiedIn_iff_inertia hM]
  intro Q _ _ σ _ x hx
  obtain ⟨a, rfl⟩ := IntermediateField.mem_bot.1 hx
  exact σ.commutes a

/- English proof (translation)
Introduce `v _` and use `isUnramifiedIn_bot v`.
-/
theorem isUnramifiedOutside_bot (S : Set (HeightOneSpectrum (𝓞 F))) :
    IsUnramifiedOutside S (⊥ : IntermediateField F Ω) :=
  fun v _ => isUnramifiedIn_bot v

/- English proof (translation)
Take `⟨M, hM⟩` from `exists_finiteGalois_le E`. Use `set M' : IntermediateField F Ω := M.toIntermediateField with hM'`. Use `set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ`. Establish `hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y` using `fun y hy => AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩`. Establish `hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M'`.

Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `(IntermediateField.mem_map _).1 hx`. Use `(ρ ⟨y, hM hy⟩).2` as an intermediate fact. Rewrite `this` using `[hρapp]`. Then use the resulting hypothesis. Rewrite `hE` using `[isUnramifiedIn_iff_inertia hM]`.

Rewrite using `[isUnramifiedIn_iff_inertia hτM]`. Introduce `Q hQ hQv σ hσ x hx`. Take `⟨y, hy, rfl⟩` from `(IntermediateField.mem_map _).1 hx`. Establish `hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F)`. Rewrite using `[Ideal.inertia, AddSubgroup.mem_inertia]`.

Introduce `z`. Rewrite using `[Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv, smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]`. Conclude with `(AddSubgroup.mem_inertia.1 hσ) (ρ • z)`. Use `NumberField.of_module_finite F M'` as an intermediate fact. Establish `: IsGaloisGroup Gal(M'/F) (𝓞 F) (𝓞 M')` using `IsGaloisGroup.of_isFractionRing _ _ _ F M'`.

Establish `hfix` using `hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy`. Establish `hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩` using `Subtype.ext (hρapp y (hM hy))`. Rewrite using `[← hρy]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]`.

Use `_ = ρ ⟨y, hM hy⟩ := by rw [hfix]`.
-/
theorem isUnramifiedIn_map {E : IntermediateField F Ω} [FiniteDimensional F E]
    (v : HeightOneSpectrum (𝓞 F)) (hE : Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal) (τ : Gal(Ω/F)) :
    Algebra.IsUnramifiedIn (𝓞 ↥(E.map (τ : Ω →ₐ[F] Ω))) v.asIdeal := by
  obtain ⟨M, hM⟩ := exists_finiteGalois_le E
  set M' : IntermediateField F Ω := M.toIntermediateField with hM'
  set ρ : Gal(M'/F) := τ.restrictNormal M' with hρ
  have hρapp : ∀ y (hy : y ∈ M'), ((ρ ⟨y, hy⟩ : M') : Ω) = τ y := fun y hy =>
    AlgEquiv.restrictNormal_commutes τ M' ⟨y, hy⟩
  have hτM : E.map (τ : Ω →ₐ[F] Ω) ≤ M' := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
    have := (ρ ⟨y, hM hy⟩).2
    rwa [hρapp] at this
  rw [isUnramifiedIn_iff_inertia hM] at hE
  rw [isUnramifiedIn_iff_inertia hτM]
  intro Q hQ hQv σ hσ x hx
  obtain ⟨y, hy, rfl⟩ := (IntermediateField.mem_map _).1 hx
  have hconj : ρ⁻¹ * σ * ρ ∈ (ρ⁻¹ • Q).inertia Gal(M'/F) := by
    rw [Ideal.inertia, AddSubgroup.mem_inertia]
    intro z
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, inv_inv,
      smul_sub, ← mul_smul, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul, mul_smul]
    exact (AddSubgroup.mem_inertia.1 hσ) (ρ • z)
  have := NumberField.of_module_finite F M'
  have : IsGaloisGroup Gal(M'/F) (𝓞 F) (𝓞 M') := IsGaloisGroup.of_isFractionRing _ _ _ F M'
  have hfix := hE (ρ⁻¹ • Q) inferInstance inferInstance _ hconj y hy
  have hρy : ρ ⟨y, hM hy⟩ = ⟨(τ : Ω →ₐ[F] Ω) y, hτM hx⟩ := Subtype.ext (hρapp y (hM hy))
  rw [← hρy]
  calc σ (ρ ⟨y, hM hy⟩) = ρ ((ρ⁻¹ * σ * ρ) ⟨y, hM hy⟩) := by
        simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    _ = ρ ⟨y, hM hy⟩ := by rw [hfix]

/- English proof (translation)
Introduce `v hv` and use `isUnramifiedIn_map v (hE v hv) τ`.
-/
theorem IsUnramifiedOutside.map {S : Set (HeightOneSpectrum (𝓞 F))} {E : IntermediateField F Ω}
    [FiniteDimensional F E] (hE : IsUnramifiedOutside S E) (τ : Gal(Ω/F)) :
    IsUnramifiedOutside S (E.map (τ : Ω →ₐ[F] Ω)) :=
  fun v hv => isUnramifiedIn_map v (hE v hv) τ

end GroundTheory.ProfCoh
