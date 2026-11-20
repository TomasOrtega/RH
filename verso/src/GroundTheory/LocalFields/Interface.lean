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
The claim follows from `Valuation.HasExtension.algebraMap_injective`.
-/
theorem algebraMap_integer_injective : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) :=
  Valuation.HasExtension.algebraMap_injective

/- English proof (translation)
Simplify using `only [Valuation.mem_integer_iff]`. Conclude with `Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x`.
-/
theorem algebraMap_mem_integer_iff (x : K) : algebraMap K L x ∈ 𝒪[L] ↔ x ∈ 𝒪[K] := by
  simp only [Valuation.mem_integer_iff]
  exact Valuation.HasExtension.val_map_le_one_iff (valuation K) (valuation L) x

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : IsScalarTower 𝒪[K] 𝒪[L] L := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : IsScalarTower 𝒪[K] K L := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : IsLocalHom (algebraMap 𝒪[K] 𝒪[L]) := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : Algebra 𝓀[K] 𝓀[L] := inferInstance
/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : FaithfulSMul 𝒪[K] 𝒪[L] := inferInstance

end Algebraic

section Topological

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

/- English proof (translation)
Use `continuous_of_continuousAt_zero (algebraMap K L) ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero L)]`. Introduce `γ _`. Take `⟨δ, hδ0, hδ1⟩` from `IsNontrivial.exists_lt_one (R := K)`. Take `⟨a, rfl⟩` from `valuation_surjective δ`.

Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hδ0`. Establish `hb : valuation L (algebraMap K L a) < 1`. Conclude with `(Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) a).mpr hδ1`.

Take `⟨n, hn⟩` from `exists_pow_lt₀ hb γ`. Use `⟨Units.mk0 (valuation K (a ^ n)) (by simp [ha0]), trivial, fun x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hx ⊢`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← (valuation L).vlt_iff_lt, ValuativeExtension.vlt_iff_vlt, (valuation K).vlt_iff_lt]`.

Conclude with `hx`. Use `_ = valuation L (algebraMap K L a) ^ n := by simp`. Use `_ < γ := hn`.
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
