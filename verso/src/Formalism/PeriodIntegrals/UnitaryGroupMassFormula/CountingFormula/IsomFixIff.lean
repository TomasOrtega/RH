import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrthogonalLatticeMapExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowsMassOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GluingMassHolds

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3

namespace GluedLatticeMass

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [Module (𝓞 K) V1] [IsScalarTower (𝓞 K) K V1]

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.
-/
theorem z_ne_zero {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz0

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem orthK_span (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) :
    Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z}) = wPerp h1 z := by
  ext x
  simp only [Formalism.L2.SG.Pf.Cnt.orthK, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro H
    exact H z (Submodule.mem_span_singleton_self z)
  · intro hx u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have hx' : h1 z x = 0 := hx
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx', smul_zero]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem glueSet_iff {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) (Λ : Submodule (𝓞 K) V1) :
    Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) ↔
      IsGlueLat h1 z Λ := by
  have hz : z ≠ 0 := z_ne_zero hz0
  unfold Formalism.L2.SG.Pf.Cnt.GlueSet IsGlueLat
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hl, hu, he⟩
    have hzmem : z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) := by
      rw [he]
      exact Submodule.mem_span_singleton_self z
    refine ⟨hl, hu, hzmem.1, fun c hc => ?_⟩
    have hcz : c • z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K) :=
      ⟨hc, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)⟩
    rw [he] at hcz
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hcz
    refine ⟨o, ?_⟩
    rw [← algebraMap_smul K o z] at ho
    exact (smul_left_injective K hz ho)
  · rintro ⟨hl, hu, hzΛ, hp⟩
    refine ⟨hl, hu, ?_⟩
    ext y
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨hyΛ, hyU⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hyU
      obtain ⟨o, ho⟩ := hp c hyΛ
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ o (Submodule.mem_span_singleton_self z)
    · intro hy
      obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hy
      refine ⟨Λ.smul_mem o hzΛ, ?_⟩
      rw [← algebraMap_smul K o z]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem isomFix_iff (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (g : V1 ≃ₗ[K] V1) :
    g ∈ Formalism.L2.SG.Pf.Cnt.isomFix h1 (Submodule.span K {z}) ↔ g ∈ hz h1 z := by
  constructor
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, hfix z (Submodule.mem_span_singleton_self z)⟩
  · rintro ⟨hg, hfz⟩
    refine ⟨hg, fun u hu => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [map_smul, hfz]

/- English proof (translation)
By extensionality, compare the relevant components. A detailed English derivation is pending.
-/
theorem stabFix_eq (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (Λ : Submodule (𝓞 K) V1) :
    Formalism.L2.SG.Pf.Cnt.stabFix h1 (Submodule.span K {z}) Λ = stabZ h1 z Λ := by
  ext g
  exact and_congr (isomFix_iff h1 z g) Iff.rfl

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
