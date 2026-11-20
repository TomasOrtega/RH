import Mathlib

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

section Algebraic

variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

instance valuation_hasExtension : (valuation K).HasExtension (valuation L) where
  val_isEquiv_comap a b := by
    rw [Valuation.comap_apply, Valuation.comap_apply, ← Valuation.vle_iff_le,
      ← Valuation.vle_iff_le, ValuativeExtension.vle_iff_vle]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_algebraMap_integer (x : 𝒪[K]) :
    ((algebraMap 𝒪[K] 𝒪[L] x : 𝒪[L]) : L) = algebraMap K L (x : K) :=
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem algebraMap_integer_injective : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) :=
  Valuation.HasExtension.algebraMap_injective

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem algebraMap_mem_integer_iff (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  simp only [Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x

/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsScalarTower 𝒪[K] K L := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example : Algebra 𝓀[K] 𝓀[L] := inferInstance
/- English proof (translation)
A detailed English derivation is pending.
-/
example : FaithfulSMul 𝒪[K] 𝒪[L] := inferInstance

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem continuous_algebraMap : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  intro γ _
  obtain ⟨δ, hδ0, hδ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨a, rfl⟩ := valuation_surjective δ
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hδ0
  have hb : valuation L (algebraMap K L a) < 1 := by
    exact (Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hb γ
  refine ⟨Units.mk0 (valuation K (a ^ n)) (by simp [ha0]), trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢
  calc valuation L (algebraMap K L x) < valuation L (algebraMap K L (a ^ n)) := by
        rw [← (valuation L).vlt_iff_lt, ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt]
        exact hx
    _ = valuation L (algebraMap K L a) ^ n := by simp
    _ < γ := hn

instance continuousSMul : ContinuousSMul K L :=
  continuousSMul_of_algebraMap K L (continuous_algebraMap K L)

end Topological

end GroundTheory.LocalField
