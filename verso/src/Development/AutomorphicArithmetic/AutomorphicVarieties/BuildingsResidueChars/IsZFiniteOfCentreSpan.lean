import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Development.AutomorphicArithmetic.DivisorFrames.ExistsQdetEqPowAddSumCoeffMemSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalSpanAdjoinOrbitOfCommuting
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CenterUActionMemAdjoinCapOp

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce `K _ _ n φ hφ`. Take `⟨ι, hι, ⟨D⟩⟩` from `UpperTheory.exists_idempotent_decomposition_mixedSpace K`. Establish `key` using `fun τ => UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span (Module.End ℂ (archSmooth K n)) n (gen D (lam K n) τ)`. Use `choose c hc hq using key`. Set `s : Set (Module.End ℂ (archSmooth K n))` to `Set.range (fun p : ι × Fin n => c p.1 p.2)`.

Establish `hcZ : ∀ τ k, c τ k ∈ Zc K n`. Introduce `τ k`. Establish `h1 : Submodule.span ℂ (Set.range (Formalism.REAL.qdet (gen D (lam K n) τ))) ≤ Subalgebra.toSubmodule (Zc K n)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨u, rfl⟩`.

Conclude with `UpperTheory.qdet_generates_universalEnveloping_centre K n ι D τ u`. Conclude with `h1 (hc τ k)`. Establish `hsZ : ∀ x ∈ s, x ∈ Zc K n`. Introduce and unpack `x ⟨⟨τ, k⟩, rfl⟩`. Conclude with `hcZ τ k`.

Establish `hAlg : ∀ T ∈ Zc K n, AlgMod (Submodule.span ℂ {φ}) ⊥ T`. Introduce `T hT`. Apply `UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ (uAction '' (isExpLieAlgebra K n).centerU)` to reduce the goal to its premises. Introduce and unpack `x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩`. Conclude with `Zc_comm (uAction_mem_Zc hz) (uAction_mem_Zc hw)`.

Introduce and unpack `x ⟨z, hz, rfl⟩`. Conclude with `hφ z hz`. Conclude with `hT`. Establish `hfd` using `UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting _ φ s (Set.finite_range _) (fun a ha b hb => Zc_comm (hsZ a ha) (hsZ b hb)) (fun T hT => hAlg T (hsZ T hT))`. Establish `hle : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤ Algebra.adjoin ℂ s`.

Rewrite using `[Algebra.adjoin_le_iff]`. Introduce and unpack `x ⟨τ, u, rfl⟩`. Use `show Formalism.REAL.qdet (gen D (lam K n) τ) u ∈ Algebra.adjoin ℂ s`. Rewrite using `[hq τ u]`. Use `Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.sum_mem _ fun k hk => Subalgebra.smul_mem _ ?_ _)` and prove the remaining obligations.

Conclude with `Algebra.subset_adjoin ⟨(τ, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩`. Establish `hsub : Submodule.span ℂ ((fun z => (uAction z) φ) '' ((isExpLieAlgebra K n).centerU : Set _)) ≤ Submodule.span ℂ ((fun T : Module.End ℂ (archSmooth K n) => T φ) '' (Algebra.adjoin ℂ s : Set _))`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `⟨uAction z, hle (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz), rfl⟩`.

Conclude with `Submodule.finiteDimensional_of_le hsub`.
-/
theorem UpperTheory.isZFinite_of_centre_span :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : archSmooth K n), Centre (Submodule.span ℂ {φ}) → IsZFinite φ := by
  intro K _ _ n φ hφ
  obtain ⟨ι, hι, ⟨D⟩⟩ := UpperTheory.exists_idempotent_decomposition_mixedSpace K
  have key := fun τ => UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span (Module.End ℂ (archSmooth K n)) n (gen D (lam K n) τ)
  choose c hc hq using key
  let s : Set (Module.End ℂ (archSmooth K n)) := Set.range (fun p : ι × Fin n => c p.1 p.2)
  have hcZ : ∀ τ k, c τ k ∈ Zc K n := by
    intro τ k
    have h1 : Submodule.span ℂ (Set.range (Formalism.REAL.qdet (gen D (lam K n) τ))) ≤
        Subalgebra.toSubmodule (Zc K n) := by
      rw [Submodule.span_le]
      rintro x ⟨u, rfl⟩
      exact UpperTheory.qdet_generates_universalEnveloping_centre K n ι D τ u
    exact h1 (hc τ k)
  have hsZ : ∀ x ∈ s, x ∈ Zc K n := by
    rintro x ⟨⟨τ, k⟩, rfl⟩
    exact hcZ τ k
  have hAlg : ∀ T ∈ Zc K n, AlgMod (Submodule.span ℂ {φ}) ⊥ T := by
    intro T hT
    apply UpperTheory.algMod_bot_of_mem_adjoin_commuting _ _ (uAction '' (isExpLieAlgebra K n).centerU)
    · rintro x ⟨z, hz, rfl⟩ y ⟨w, hw, rfl⟩
      exact Zc_comm (uAction_mem_Zc hz) (uAction_mem_Zc hw)
    · rintro x ⟨z, hz, rfl⟩
      exact hφ z hz
    · exact hT
  have hfd := UpperTheory.finiteDimensional_span_adjoin_orbit_of_commuting _ φ s (Set.finite_range _)
    (fun a ha b hb => Zc_comm (hsZ a ha) (hsZ b hb)) (fun T hT => hAlg T (hsZ T hT))
  have hle : Algebra.adjoin ℂ {x | ∃ τ u, x = capOp D n τ u} ≤ Algebra.adjoin ℂ s := by
    rw [Algebra.adjoin_le_iff]
    rintro x ⟨τ, u, rfl⟩
    show Formalism.REAL.qdet (gen D (lam K n) τ) u ∈ Algebra.adjoin ℂ s
    rw [hq τ u]
    refine Subalgebra.add_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.sum_mem _ fun k hk => Subalgebra.smul_mem _ ?_ _)
    exact Algebra.subset_adjoin ⟨(τ, ⟨k, Finset.mem_range.mp hk⟩), rfl⟩
  have hsub : Submodule.span ℂ ((fun z => (uAction z) φ) '' ((isExpLieAlgebra K n).centerU : Set _)) ≤
      Submodule.span ℂ ((fun T : Module.End ℂ (archSmooth K n) => T φ) '' (Algebra.adjoin ℂ s : Set _)) := by
    apply Submodule.span_mono
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨uAction z, hle (UpperTheory.centerU_action_mem_adjoin_capOp K n ι D z hz), rfl⟩
  exact Submodule.finiteDimensional_of_le hsub
