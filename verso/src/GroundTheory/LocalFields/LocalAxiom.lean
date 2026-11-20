import Mathlib
import GroundTheory.LocalFields.LocalAxiomDictionary
import GroundTheory.LocalFields.HerbrandLocal
import GroundTheory.LocalFields.MaximalUnramified
import GroundTheory.LocalFields.SeparableClosure
import GroundTheory.LocalFields.SeparableClosureValuation

namespace GroundTheory.LocalField

open Abstract ValuativeRel

section Valuation

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

noncomputable def ordUnitsHom : Kˣ →* Multiplicative ℤ̂ where
  toFun x := Multiplicative.ofAdd ((ord (x : K) : ℤ) : ℤ̂)
  map_one' := by
    rw [Units.val_one, ord_one, Int.cast_zero, ofAdd_zero]
  map_mul' x y := by
    rw [Units.val_mul, ord_mul x.ne_zero y.ne_zero, Int.cast_add, ofAdd_add]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toAdd_ordUnitsHom (x : Kˣ) :
    (ordUnitsHom K x).toAdd = ((ord (x : K) : ℤ) : ℤ̂) :=
  rfl

variable {K} in

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_ordUnitsHom_eq (n : ℤ) :
    ∃ x : Kˣ, ordUnitsHom K x = Multiplicative.ofAdd (n : ℤ̂) := by
  obtain ⟨x, hx, h⟩ := exists_ord_eq K n
  refine ⟨Units.mk0 x hx, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_ordUnitsHom, Units.val_mk0, h, toAdd_ofAdd]

end Valuation

section Data

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localValuation : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) →* Multiplicative ℤ̂ :=
  (ordUnitsHom K).comp baseUnitsEquiv.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localValuation_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    localValuation K Ω a = ordUnitsHom K (baseUnitsEquiv a) :=
  rfl

variable {K Ω}

/- English proof (translation)
Substitute using the available equality. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem range_localValuation_comp_norm_of_eq (H : Subgroup (Ω ≃ₐ[K] Ω))
    [(H.subgroupOf ⊤).FiniteIndex] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hL : L.fixingSubgroup = H) :
    ((localValuation K Ω).comp (norm Ωˣ ⊤ H)).range =
      (localValuation K Ω).range.map (powMonoidHom (inertiaDegree (unramifiedDegree K Ω) H)) := by
  subst hL
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have hsc : IsSepClosed Ω := IsSepClosure.sep_closed K
  rw [inertiaDegree_unramifiedDegree_fixingSubgroup]
  have key : ∀ u : Lˣ, ordUnitsHom K (normUnits K L u) =
      Multiplicative.ofAdd (((residueDegree K L : ℤ) * ord (u : L) : ℤ) : ℤ̂) := fun u => by
    apply Multiplicative.toAdd.injective
    rw [toAdd_ordUnitsHom, coe_normUnits, ord_norm, toAdd_ofAdd]
  ext z
  simp only [MonoidHom.mem_range, Subgroup.mem_map, MonoidHom.comp_apply, powMonoidHom_apply]
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) (ord ((fixedModuleUnitsEquiv L a : Lˣ) : L))
    refine ⟨_, ⟨baseUnitsEquiv.symm x, rfl⟩, ?_⟩
    rw [localValuation_apply, localValuation_apply, MulEquiv.apply_symm_apply, hx,
      baseUnitsEquiv_norm, key]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    obtain ⟨y, hy, hy'⟩ := exists_ord_eq L (ord ((baseUnitsEquiv b : Kˣ) : K))
    refine ⟨(fixedModuleUnitsEquiv L).symm (Units.mk0 y hy), ?_⟩
    rw [localValuation_apply, localValuation_apply, baseUnitsEquiv_norm, MulEquiv.apply_symm_apply,
      key, Units.val_mk0, hy']
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_ordUnitsHom, toAdd_ofAdd, Int.cast_mul,
      Int.cast_natCast, nsmul_eq_mul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem intCast_mem_range_localValuation (n : ℤ) :
    Multiplicative.ofAdd (n : ℤ̂) ∈ (localValuation K Ω).range := by
  obtain ⟨x, hx⟩ := exists_ordUnitsHom_eq (K := K) n
  exact ⟨baseUnitsEquiv.symm x, by rw [localValuation_apply, MulEquiv.apply_symm_apply, hx]⟩

variable (K Ω)

noncomputable def localClassFieldData : ClassFieldData (Ω ≃ₐ[K] Ω) Ωˣ where
  deg := unramifiedDegree K Ω
  continuous_deg := unramifiedDegree_spec.1
  surjective_deg := unramifiedDegree_spec.2.1
  val := localValuation K Ω
  intCast_mem_range_val := intCast_mem_range_localValuation
  exists_eq_intCast_add_nsmul n _ a := by
    refine ⟨ord ((baseUnitsEquiv a : Kˣ) : K), 1, ?_⟩
    rw [map_one, toAdd_one, smul_zero, add_zero]
    rfl
  range_val_comp_norm U :=
    range_localValuation_comp_norm_of_eq (U : Subgroup (Ω ≃ₐ[K] Ω))
      (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
      (fixingSubgroup_fixedField_openSubgroup U)

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localClassFieldData_deg : (localClassFieldData K Ω).deg = unramifiedDegree K Ω :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localClassFieldData_val : (localClassFieldData K Ω).val = localValuation K Ω :=
  rfl

end Data

section Axiom

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem natCard_tate_of_isCyclic (K' L' : Subgroup (Ω ≃ₐ[K] Ω)) [(L'.subgroupOf K').Normal]
    [(L'.subgroupOf K').FiniteIndex] (E F : IntermediateField K Ω) [FiniteDimensional K E]
    [FiniteDimensional K F] (hEF : E ≤ F) (hK : E.fixingSubgroup = K') (hL : F.fixingSubgroup = L')
    (hcyc : IsCyclic (K' ⧸ L'.subgroupOf K')) :
    Nat.card (tateZero Ωˣ K' L') = L'.relIndex K' ∧ Nat.card (tateNegOne Ωˣ K' L') = 1 := by
  let := algebraicValuativeRel K Ω
  let := algebraicTopology K Ω
  have := algebraicValuativeRel_valuativeExtension K Ω
  have := algebraicTopology_isValuativeTopology K Ω
  have : Algebra.IsAlgebraic E Ω := Algebra.IsAlgebraic.tower_top (K := K) E
  have := normal_extendScalars K' L' hEF hK hL
  have := finiteDimensional_extendScalars hEF
  have : IsGalois E (IntermediateField.extendScalars hEF) :=
    isGalois_iff.2 ⟨inferInstance, inferInstance⟩
  let T := galoisTateModel K' L' hEF hK hL
  have : IsCyclic (IntermediateField.extendScalars hEF ≃ₐ[E] IntermediateField.extendScalars hEF) :=
    isCyclic_of_surjective T.quotientEquiv.toMonoidHom T.quotientEquiv.surjective
  refine ⟨?_, ?_⟩
  · rw [T.natCard_tateZero, natCard_tateZero_units, T.relIndex_eq_natCard,
      IsGalois.card_aut_eq_finrank]
  · rw [T.natCard_tateNegOne, natCard_tateNegOne_units]

variable (K Ω) in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem classFieldAxiom_units : ClassFieldAxiom (Ω ≃ₐ[K] Ω) Ωˣ := by
  intro U V hVU _ hcyc
  exact natCard_tate_of_isCyclic (U : Subgroup (Ω ≃ₐ[K] Ω)) (V : Subgroup (Ω ≃ₐ[K] Ω))
    (IntermediateField.fixedField (U : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField (V : Subgroup (Ω ≃ₐ[K] Ω)))
    (IntermediateField.fixedField_antitone hVU) (fixingSubgroup_fixedField_openSubgroup U)
    (fixingSubgroup_fixedField_openSubgroup V) hcyc

end Axiom

section Theory

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

noncomputable def localClassFieldTheory : ClassFieldTheory (Ω ≃ₐ[K] Ω) Ωˣ where
  toClassFieldData := localClassFieldData K Ω
  isDiscreteModule := isDiscreteModule_units
  classFieldAxiom := classFieldAxiom_units K Ω

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem localClassFieldTheory_deg : (localClassFieldTheory K Ω).deg = unramifiedDegree K Ω :=
  rfl

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localClassFieldTheory_val : (localClassFieldTheory K Ω).val = localValuation K Ω :=
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localClassFieldTheory_val_apply (a : fixedModule Ωˣ (⊤ : Subgroup (Ω ≃ₐ[K] Ω))) :
    ((localClassFieldTheory K Ω).val a).toAdd = ((ord ((baseUnitsEquiv a : Kˣ) : K) : ℤ) : ℤ̂) :=
  rfl

end Theory

end GroundTheory.LocalField
