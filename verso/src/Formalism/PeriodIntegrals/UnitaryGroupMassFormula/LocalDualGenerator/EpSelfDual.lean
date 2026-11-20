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
Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Equip the data with the indicated structure. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
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
