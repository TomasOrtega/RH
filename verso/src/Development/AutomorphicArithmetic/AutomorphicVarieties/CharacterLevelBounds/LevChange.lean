import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem level_iff (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N]
    [hc : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ)] (H : Subgroup (ZMod N)ˣ) :
    HasLevel E N H ↔ ∃ j : E →ₐ[ℚ] CyclotomicField N ℚ, ∀ τ : CyclotomicField N ℚ ≃ₐ[ℚ] CyclotomicField N ℚ,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ) τ ∈ H := by
  constructor
  · rintro ⟨j, ζ, hζ, h⟩
    exact ⟨j, fun τ => h τ _ (IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one)⟩
  · rintro ⟨j, h⟩
    have hζ := IsCyclotomicExtension.zeta_spec N ℚ (CyclotomicField N ℚ)
    refine ⟨j, _, hζ, fun τ u hu => ?_⟩
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N _ τ hζ.pow_eq_one,
      (hζ.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζ.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ← Units.ext_iff] at hu
    rw [← hu]
    exact h τ

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem change (E F K : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Field K] [NumberField K]
    (M N : ℕ) [NeZero M] [NeZero N] [IsCyclotomicExtension {M} ℚ F] [IsCyclotomicExtension {N} ℚ K]
    (h : M ∣ N) (H : Subgroup (ZMod M)ˣ) :
    (∃ j : E →ₐ[ℚ] F, ∀ τ : F ≃ₐ[ℚ] F,
      (∀ x : E, τ (j x) = j x) ↔ IsCyclotomicExtension.Rat.galEquivZMod M F τ ∈ H) ↔
    (∃ j : E →ₐ[ℚ] K, ∀ τ : K ≃ₐ[ℚ] K,
      (∀ x : E, τ (j x) = j x) ↔
        IsCyclotomicExtension.Rat.galEquivZMod N K τ ∈ H.comap (ZMod.unitsMap h)) := by
  haveI : IsGalois ℚ F := IsCyclotomicExtension.isGalois {M} ℚ F
  haveI : IsGalois ℚ K := IsCyclotomicExtension.isGalois {N} ℚ K
  obtain ⟨c, hc⟩ := id h
  have hη : IsPrimitiveRoot (IsCyclotomicExtension.zeta N ℚ K ^ c) M :=
    (IsCyclotomicExtension.zeta_spec N ℚ K).pow (NeZero.pos N) (hc.trans (mul_comm _ _))
  let i : F →ₐ[ℚ] K := ((IsCyclotomicExtension.zeta_spec M ℚ F).embeddingsEquivPrimitiveRoots K
    (Polynomial.cyclotomic.irreducible_rat (NeZero.pos M))).symm ⟨_, (mem_primitiveRoots (NeZero.pos M)).2 hη⟩
  letI : Algebra F K := i.toRingHom.toAlgebra
  haveI : IsGalois F K := IsGalois.tower_top_of_isGalois ℚ F K
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have hinj := (algebraMap F K).injective
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨i.comp j, fun τ => ?_⟩
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h τ, ← hj]
    refine forall_congr' fun x => ?_
    rw [← hinj.eq_iff, AlgEquiv.restrictNormal_commutes]
    rfl
  · rintro ⟨j, hj⟩
    have hr : ∀ x : E, ∃ y : F, algebraMap F K y = j x := by
      intro x
      have : j x ∈ Set.range (algebraMap F K) := by
        rw [IsGalois.mem_range_algebraMap_iff_fixed]
        intro σ
        refine (hj (σ.restrictScalars ℚ)).2 ?_ x
        have h1 : (σ.restrictScalars ℚ).restrictNormal F = 1 := by
          ext y
          apply hinj
          rw [AlgEquiv.restrictNormal_commutes]
          exact σ.commutes y
        rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h, h1, map_one]
        exact H.one_mem
      exact this
    choose f hf using hr
    let j0 : E →+* F :=
      { toFun := f
        map_one' := hinj (by simp [hf])
        map_mul' := fun x y => hinj (by simp [hf])
        map_zero' := hinj (by simp [hf])
        map_add' := fun x y => hinj (by simp [hf]) }
    refine ⟨j0.toRatAlgHom, fun τ => ?_⟩
    have h2 := hj (τ.liftNormal K)
    rw [Subgroup.mem_comap, ← IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply N K F h,
      AlgEquiv.restrict_liftNormal] at h2
    rw [← h2]
    refine forall_congr' fun x => ?_
    rw [← hf x, ← hinj.eq_iff, ← τ.liftNormal_commutes K]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Chr.levChange :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ) [NeZero N], (Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → ∃ H : Subgroup (ZMod N)ˣ, HasLevel E N H) ∧
          ∀ (M : ℕ) [NeZero M] (h : M ∣ N) (H : Subgroup (ZMod M)ˣ), HasLevel E M H ↔ HasLevel E N (H.comap (ZMod.unitsMap h)) := by
  intro E _ _ N _
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) := CyclotomicField.isCyclotomicExtension N ℚ
  constructor
  · rintro ⟨j⟩
    refine ⟨j.fieldRange.fixingSubgroup.map
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom, (level_iff E N _).2 ⟨j, fun τ => ?_⟩⟩
    refine Iff.trans ?_ (Subgroup.mem_map_iff_mem (f := (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).toMonoidHom)
      (IsCyclotomicExtension.Rat.galEquivZMod N (CyclotomicField N ℚ)).injective).symm
    rw [IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      exact h x
    · intro h x
      exact h _ ⟨x, rfl⟩
  · intro M _ h H
    haveI : IsCyclotomicExtension {M} ℚ (CyclotomicField M ℚ) := CyclotomicField.isCyclotomicExtension M ℚ
    rw [level_iff, level_iff]
    exact change E _ _ M N h H
