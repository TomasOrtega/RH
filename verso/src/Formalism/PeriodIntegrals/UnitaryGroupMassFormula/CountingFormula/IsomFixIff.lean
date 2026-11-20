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
Introduce and unpack `rfl`. Simplify using `at hz0`.
-/
theorem z_ne_zero {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} (hz0 : h1 z z ≠ 0) : z ≠ 0 := by
  rintro rfl
  simp at hz0

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Formalism.L2.SG.Pf.Cnt.orthK, Submodule.mem_iInf, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Conclude with `H z (Submodule.mem_span_singleton_self z)`.

Introduce `hx u hu`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hu`. Establish `hx' : h1 z x = 0` using `hx`. Rewrite using `[LinearMap.map_smulₛₗ, LinearMap.smul_apply, hx', smul_zero]`.
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
Establish `hz : z ≠ 0` using `z_ne_zero hz0`. Unfold `Formalism.L2.SG.Pf.Cnt.GlueSet IsGlueLat`. Simplify using `only [Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hl, hu, he⟩`.

Establish `hzmem : z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K)`. Rewrite using `[he]`. Conclude with `Submodule.mem_span_singleton_self z`. Use `⟨hl, hu, hzmem.1, fun c hc => ?_⟩` and prove the remaining obligations. Establish `hcz : c • z ∈ Λ ⊓ (Submodule.span K {z}).restrictScalars (𝓞 K)` using `⟨hc, Submodule.smul_mem _ c (Submodule.mem_span_singleton_self z)⟩`.

Rewrite `hcz` using `[he]`. Take `⟨o, ho⟩` from `Submodule.mem_span_singleton.1 hcz`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite `ho` using `[← algebraMap_smul K o z]`. Conclude with `(smul_left_injective K hz ho)`.

Introduce and unpack `⟨hl, hu, hzΛ, hp⟩`. Use `⟨hl, hu, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hyΛ, hyU⟩`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hyU`. Take `⟨o, ho⟩` from `hp c hyΛ`. Rewrite using `[← ho, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ o (Submodule.mem_span_singleton_self z)`.

Introduce `hy`. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 hy`. Use `⟨Λ.smul_mem o hzΛ, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K o z]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)`.
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
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hg, hfix⟩`. Conclude with `⟨hg, hfix z (Submodule.mem_span_singleton_self z)⟩`. Introduce and unpack `⟨hg, hfz⟩`. Use `⟨hg, fun u hu => ?_⟩` and prove the remaining obligations.

Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hu`. Rewrite using `[map_smul, hfz]`.
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
Use extensionality with `g`. Conclude with `and_congr (isomFix_iff h1 z g) Iff.rfl`.
-/
theorem stabFix_eq (h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K) (z : V1) (Λ : Submodule (𝓞 K) V1) :
    Formalism.L2.SG.Pf.Cnt.stabFix h1 (Submodule.span K {z}) Λ = stabZ h1 z Λ := by
  ext g
  exact and_congr (isomFix_iff h1 z g) Iff.rfl

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
