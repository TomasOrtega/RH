import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualField
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDualCase

set_option linter.style.haveILetI false

noncomputable section
open ValuativeRel Module

namespace PI.LocDualGen.EpG

/- English proof (translation)
Use `haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hr]; norm_num)`. Establish `hOC : ∀ z : L, z ∈ O ↔ z ∈ integralClosure 𝒪[K] L` using `fun z => (hO z).trans Iff.rfl`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[K]`. Establish `hm : 𝓂[K] = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Establish `hcoe : ∀ c : integralClosure 𝒪[K] L, ((c * algebraMap 𝒪[K] (integralClosure 𝒪[K] L) ϖ : integralClosure 𝒪[K] L) : L) = (c : L) * algebraMap K L (ϖ : K)`.

Introduce `c`. Rewrite using `[Subalgebra.coe_mul, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[K] K L]`. Both sides reduce to the same expression. Establish `hmem : ∀ z : integralClosure 𝒪[K] L, z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] ↔ (z : L) ∈ Submodule.span O {algebraMap K L (ϖ : K)}`. Introduce `z`.

Rewrite using `[hm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', Submodule.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Use `⟨⟨c, (hOC c).2 c.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, hcoe]`.

Both sides reduce to the same expression. Introduce and unpack `⟨a, ha⟩`. Use `⟨⟨a, (hOC a).1 a.2⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hcoe, ← ha]`. Both sides reduce to the same expression.

Establish `hU' : ∀ z : integralClosure 𝒪[K] L, z * z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] → z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K]`. Introduce `z hz`. Rewrite `hz`, the goal using `[hmem]`. Conclude with `hU ϖ hϖ z ((hOC z).2 z.2) hz`. Establish `key` using `PI.LocDualGen.EpF.selfDual_field K L hU' x`.

Simplify `key` using `only [hOC]`.
-/
theorem field_version (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [CharZero K]
    (L : Type) [Field L] [Algebra K L] (hr : finrank K L = 2)
    (O : Subring L) (hO : ∀ x : L, x ∈ O ↔ IsIntegral 𝒪[K] x)
    (hU : ∀ ϖ : 𝒪[K], Irreducible ϖ → ∀ x ∈ O,
      x * x ∈ Submodule.span O {algebraMap K L (ϖ : K)} →
        x ∈ Submodule.span O {algebraMap K L (ϖ : K)})
    (x : L) : (∀ y ∈ O, Algebra.trace K L (x * y) ∈ 𝒪[K]) ↔ x ∈ O := by
  haveI : FiniteDimensional K L := Module.finite_of_finrank_pos (by rw [hr]; norm_num)
  have hOC : ∀ z : L, z ∈ O ↔ z ∈ integralClosure 𝒪[K] L := fun z => (hO z).trans Iff.rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hm : 𝓂[K] = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
  have hcoe : ∀ c : integralClosure 𝒪[K] L,
      ((c * algebraMap 𝒪[K] (integralClosure 𝒪[K] L) ϖ : integralClosure 𝒪[K] L) : L) =
        (c : L) * algebraMap K L (ϖ : K) := by
    intro c
    rw [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply 𝒪[K] K L]
    rfl
  have hmem : ∀ z : integralClosure 𝒪[K] L,
      z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] ↔
        (z : L) ∈ Submodule.span O {algebraMap K L (ϖ : K)} := by
    intro z
    rw [hm, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton', Submodule.mem_span_singleton]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨⟨c, (hOC c).2 c.2⟩, ?_⟩
      rw [← hc, hcoe]
      rfl
    · rintro ⟨a, ha⟩
      refine ⟨⟨a, (hOC a).1 a.2⟩, Subtype.ext ?_⟩
      rw [hcoe, ← ha]
      rfl
  have hU' : ∀ z : integralClosure 𝒪[K] L,
      z * z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] →
        z ∈ Ideal.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) 𝓂[K] := by
    intro z hz
    rw [hmem] at hz ⊢
    exact hU ϖ hϖ z ((hOC z).2 z.2) hz
  have key := PI.LocDualGen.EpF.selfDual_field K L hU' x
  simpa only [hOC] using key

/- English proof (translation)
Introduce `K _ _ _ L _ _ hK hC _ hr hred O hO hU x`. Use `haveI := hK`. Use `haveI := hC`. Break down `PI.LocDualGen.EpC.dichotomy hr hred with hF | ⟨e, he, h0, h1⟩` into its components or cases. Use `letI : Field L := hF.toField`.

Conclude with `field_version K L hr O hO hU x`. Establish `key` using `PI.LocDualGen.EpS.selfDual_split hr e he h0 h1 x`. Simplify `key` using `only [hO]`.
-/
theorem quadraticSelfDual : PI.LocDualGen.W.EpSelfDual := by
  intro K _ _ _ L _ _ hK hC _ hr hred O hO hU x
  haveI := hK
  haveI := hC
  rcases PI.LocDualGen.EpC.dichotomy hr hred with hF | ⟨e, he, h0, h1⟩
  · letI : Field L := hF.toField
    exact field_version K L hr O hO hU x
  · have key := PI.LocDualGen.EpS.selfDual_split hr e he h0 h1 x
    simpa only [hO] using key

end PI.LocDualGen.EpG
