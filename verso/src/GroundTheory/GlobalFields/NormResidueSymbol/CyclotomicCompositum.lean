import Mathlib
import GroundTheory.GlobalFields.NormResidueSymbol.CyclotomicBase
import GroundTheory.GlobalFields.IdeleClassGroup.InvariantsGalois

namespace GroundTheory.Global

open NumberField IntermediateField IdeleGroup

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

namespace CyclotomicSymbol

open FiniteSubfield

def compositum (K F : FiniteSubfield) : FiniteSubfield :=
  ⟨K.1 ⊔ F.1, inferInstance⟩

variable (K F : FiniteSubfield)

instance fact_le_compositum_left : Fact (K ≤ compositum K F) :=
  ⟨show K.1 ≤ K.1 ⊔ F.1 from le_sup_left⟩

instance fact_le_compositum_right : Fact (F ≤ compositum K F) :=
  ⟨show F.1 ≤ K.1 ⊔ F.1 from le_sup_right⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fixingSubgroup_compositum :
    (compositum K F).1.fixingSubgroup = K.1.fixingSubgroup ⊓ F.1.fixingSubgroup :=
  fixingSubgroup_sup

variable [IsGalois ℚ F.1]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem fixingSubgroup_normal : F.1.fixingSubgroup.Normal := by
  have : IsGalois ℚ ℚ̄ := IsAlgClosure.isGalois ℚ ℚ̄
  have h : @IsGalois ℚ _ F.1 _ (IntermediateField.algebra' F.1) := by
    convert (inferInstance : IsGalois ℚ F.1)
    exact Subsingleton.elim _ _
  rw [InfiniteGalois.normal_iff_isGalois]
  exact h

instance normal_subgroupOf_compositum :
    ((compositum K F).1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal := by
  rw [fixingSubgroup_compositum, Subgroup.inf_subgroupOf_left]
  have := fixingSubgroup_normal F
  exact Subgroup.Normal.subgroupOf this _

instance isGalois_compositum : IsGalois K.1 (compositum K F).1 :=
  isGalois_of_normal

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem mem_fixingSubgroup_iff_restrictNormal_eq_one (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    g ∈ F.1.fixingSubgroup ↔ g.restrictNormal F.1 = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg
    ext y
    exact (AlgEquiv.restrictNormal_commutes g F.1 y).trans (hg y y.2)
  · intro hg y hy
    have h1 := AlgEquiv.restrictNormal_commutes g F.1 ⟨y, hy⟩
    rw [hg] at h1
    exact h1.symm

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem commutator_mem_fixingSubgroup (a b : ℚ̄ ≃ₐ[ℚ] ℚ̄) :
    (a * b)⁻¹ * (b * a) ∈ F.1.fixingSubgroup := by
  rw [mem_fixingSubgroup_iff_restrictNormal_eq_one]
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 ((a * b)⁻¹ * (b * a)) = 1
  rw [map_mul, map_inv, map_mul, map_mul,
    mul_comm' (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1 b), inv_mul_cancel]

variable [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)]

instance isMulCommutative_compositum :
    IsMulCommutative ((compositum K F).1 ≃ₐ[K.1] (compositum K F).1) := by
  refine ⟨⟨fun a b ↦ ?_⟩⟩
  obtain ⟨g, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) a
  obtain ⟨h, rfl⟩ := restrictHom_surjective (F := K) (E := compositum K F) b
  rw [← map_mul, ← map_mul, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  exact ⟨Subtype.property _, commutator_mem_fixingSubgroup F _ _⟩

omit [IsMulCommutative (F.1 ≃ₐ[ℚ] F.1)] in

/- English proof (translation)
By extensionality, compare the relevant components. Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem restrictNormal_restrictHom (g : K.1.fixingSubgroup) :
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ).restrictNormal F.1 =
      (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
  ext y
  have h1 := AlgEquiv.restrictNormal_commutes
    ((restrictHom (E := compositum K F) g).restrictScalars ℚ) F.1 y
  have h2 := AlgEquiv.restrictNormal_commutes (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) F.1 y
  exact (congrArg Subtype.val h1).trans h2.symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ideleSymbol_ideleNorm (x : IdeleGroup K.1) :
    ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) =
      ((ideleSymbol K.1 (compositum K F).1 x).restrictScalars ℚ).restrictNormal F.1 :=
  (restrictNormal_restrictScalars_ideleSymbol x).symm

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_restrictNormal_eq_ideleSymbol (x : IdeleGroup K.1) :
    ∃ g ∈ K.1.fixingSubgroup,
      g.restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) := by
  obtain ⟨g, hg⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  refine ⟨g, g.2, ?_⟩
  rw [ideleSymbol_ideleNorm, ← hg, restrictNormal_restrictHom]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_ideleSymbol_eq_restrictNormal {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g ∈ K.1.fixingSubgroup) :
    ∃ x : IdeleGroup K.1, ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x) = g.restrictNormal F.1 := by
  obtain ⟨x, hx⟩ := ideleSymbol_surjective (K := K.1) (L := (compositum K F).1)
    (restrictHom (E := compositum K F) ⟨g, hg⟩)
  refine ⟨x, ?_⟩
  rw [ideleSymbol_ideleNorm, hx, restrictNormal_restrictHom]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem restrictHom_eq_ideleSymbol (g : K.1.fixingSubgroup) (x : IdeleGroup K.1)
    (h : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = ideleSymbol ℚ F.1 (ideleNorm ℚ K.1 x)) :
    restrictHom (E := compositum K F) g = ideleSymbol K.1 (compositum K F).1 x := by
  obtain ⟨g', hg'⟩ := restrictHom_surjective (F := K) (E := compositum K F)
    (ideleSymbol K.1 (compositum K F).1 x)
  have h' : (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 := by
    rw [h, ideleSymbol_ideleNorm, ← hg', restrictNormal_restrictHom]
  rw [← hg', eq_comm, MonoidHom.eq_iff, ker_restrictHom, Subgroup.mem_subgroupOf,
    fixingSubgroup_compositum]
  refine ⟨(g⁻¹ * g' : K.1.fixingSubgroup).2, (mem_fixingSubgroup_iff_restrictNormal_eq_one F _).2 ?_⟩
  change AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚ̄) F.1
    ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄)) = 1
  rw [map_mul, map_inv]
  change ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1)⁻¹ * (g' : ℚ̄ ≃ₐ[ℚ] ℚ̄).restrictNormal F.1 = 1
  rw [h', inv_mul_cancel]

end CyclotomicSymbol

end

end GroundTheory.Global
