import Mathlib
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnitsGalois
import GroundTheory.LocalFields.CompleteTrivial
import GroundTheory.LocalFields.HilbertCyclic

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel IsLocalRing

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.
-/
theorem coe_tateNorm_integerUnits [IsGalois K L] (u : 𝒪[L]ˣ) :
    (((tateNorm (L ≃ₐ[K] L) 𝒪[L]ˣ u : 𝒪[L]ˣ) : 𝒪[L]) : L) =
      algebraMap K L (Algebra.norm K ((u : 𝒪[L]) : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms, tateNorm_apply, Units.coe_prod]
  push_cast
  rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem exists_eq_of_forall_smul_eq [IsGalois K L] {x : 𝒪[L]ˣ}
    (hx : ∀ σ : L ≃ₐ[K] L, σ • x = x) :
    ∃ w : 𝒪[K]ˣ, algebraMap K L ((w : 𝒪[K]) : K) = ((x : 𝒪[L]) : L) := by
  have hfix : ((x : 𝒪[L]) : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed _).2 fun σ ↦ by
      have := congrArg (fun u : 𝒪[L]ˣ ↦ ((u : 𝒪[L]) : L)) (hx σ)
      simpa using this
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 hfix
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact (Units.ne_zero x) (by exact_mod_cast hc.symm)
  have h1 : c ∈ 𝒪[K] := (algebraMap_mem_integer_iff K L c).1 (hc ▸ (x : 𝒪[L]).2)
  have h2 : c⁻¹ ∈ 𝒪[K] := by
    refine (algebraMap_mem_integer_iff K L c⁻¹).1 ?_
    have e : algebraMap K L c⁻¹ = (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) := by
      rw [map_inv₀, hc, eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast (Units.ne_zero x))]
      exact_mod_cast congrArg (fun u : 𝒪[L] ↦ (u : L)) x.inv_mul
    rw [e]
    exact (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L])).2
  refine ⟨⟨⟨c, h1⟩, ⟨c⁻¹, h2⟩, ?_, ?_⟩, hc⟩
  · ext
    simp [hc0]
  · ext
    simp [hc0]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities.
-/
theorem subsingleton_tateZero_integerUnits [IsGalois K L] [IsUnramified K L] :
    Subsingleton (TateZero (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateZero_iff]
  intro x hx
  obtain ⟨w, hw⟩ := exists_eq_of_forall_smul_eq hx
  obtain ⟨v, rfl⟩ := normIntegerUnits_surjective (K := K) (L := L) w
  refine ⟨v, Units.ext (Subtype.ext ?_)⟩
  rw [coe_tateNorm_integerUnits, ← hw, ← coe_norm_integer, coe_normIntegerUnits_eq]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem subsingleton_tateNegOne_integerUnits [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)]
    [IsUnramified K L] :
    Subsingleton (TateNegOne (L ≃ₐ[K] L) 𝒪[L]ˣ) := by
  rw [subsingleton_tateNegOne_iff]
  intro x hx
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := L ≃ₐ[K] L)
  have hxL : tateNorm (L ≃ₐ[K] L) Lˣ (unitsIncl L x) = 1 := by
    rw [tateNorm_apply]
    simp_rw [← unitsIncl_smul]
    rw [← map_prod, ← tateNorm_apply, hx, map_one]
  obtain ⟨y, hy⟩ := exists_smul_div_eq_of_tateNorm_eq_one hg hxL
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖL := irreducible_algebraMap_of_isUnramified (L := L) hϖ
  obtain ⟨⟨m, v⟩, rfl⟩ := (unitsOfIntProd_bijective hϖL).2 y
  have hπ : g • uniformizerUnit hϖL = uniformizerUnit hϖL := by
    ext
    change g ((uniformizerUnit hϖL : Lˣ) : L) = _
    rw [coe_uniformizerUnit, coe_algebraMap_integer, AlgEquiv.commutes]
  have hx' : x = g • v / v := by
    apply unitsIncl_injective (K := L)
    rw [← hy, unitsOfIntProd_eq, _root_.map_div, unitsIncl_smul, smul_mul', smul_zpow', hπ,
      mul_div_mul_left_eq_div]
  rw [hx']
  exact Subgroup.subset_closure ⟨g, v, rfl⟩

end GroundTheory.LocalField
