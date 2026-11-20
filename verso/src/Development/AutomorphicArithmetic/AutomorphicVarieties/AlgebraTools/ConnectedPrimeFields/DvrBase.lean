import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

/- English proof (translation)
Introduce `O _ _ _ _`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Use `haveI : Nontrivial (QuotSMulTop ϖ O) := by open Pointwise in`. Use `Submodule.Quotient.nontrivial_iff.mpr ?_` and prove the remaining obligations. Introduce `h`.

Establish `h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O)` using `by rw [h]; exact Submodule.mem_top`. Take `⟨x, -, hx⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1`. Conclude with `hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))`. Use `⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩` and prove the remaining obligations. Rewrite using `[IsDiscreteValuationRing.ringKrullDim_eq_one]`.

Both sides reduce to the same expression. Introduce `r hr`. Simplify using `only [List.mem_singleton] at hr`. Substitute `hr` using the available equality. Conclude with `(IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit`.

Rewrite using `[RingTheory.Sequence.isRegular_cons_iff]`. Use `⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩` and prove the remaining obligations. Conclude with `RingTheory.Sequence.IsRegular.nil _ _`.
-/
theorem UpperTheory.V.AlgebraTools.Conn.dvrBase :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O], IsBase O := by
  intro O _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Nontrivial (QuotSMulTop ϖ O) := by
    open Pointwise in
    refine Submodule.Quotient.nontrivial_iff.mpr ?_
    intro h
    have h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O) := by rw [h]; exact Submodule.mem_top
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩
    exact RingTheory.Sequence.IsRegular.nil _ _
