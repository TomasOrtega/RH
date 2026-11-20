import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CvCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.LatCount
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
/- English proof (translation)
Introduce `E _ _ _ a ha μ _ _ ψ hψc hψs F g`. Take `⟨B, hB0, hB⟩` from `cvCount (GA E a) (latticeGL E a) μ ψ hψc hψs`. Establish `hKc : IsCompact (tsupport ψ)` using `hψs.isCompact`. Take `⟨C, N, hC⟩` from `latCount E a ha ((tsupport ψ)⁻¹ * tsupport ψ) (hKc.inv.mul hKc) g`. Use `⟨B * ‖F‖ * C, N, fun y => ?_⟩` and prove the remaining obligations.

Take `⟨M, hM, hcard⟩` from `hC y`. Establish `key : ∀ h : GA E a, {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.encard ≤ (M : ℕ∞)`. Introduce `h`. Distinguish the cases in `hne : {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.Nonempty`. Take `⟨γ₀, hγ₀⟩` from `hne`.

Use `le_trans (Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_) hcard` and prove the remaining obligations. Introduce `γ hγ`. Simplify using `only [Set.mem_setOf_eq] at hγ hγ₀ ⊢`. Establish `h₁` using `subset_tsupport ψ hγ`. Establish `h₂` using `subset_tsupport ψ hγ₀`.

Establish `e : (g * infGL E a y)⁻¹ * ↑(γ * γ₀⁻¹) * (g * infGL E a y) = ((↑γ * h)⁻¹ * (g * infGL E a y))⁻¹ * ((↑γ₀ * h)⁻¹ * (g * infGL E a y))`. Use `push_cast`. Use `group`. Rewrite using `[e]`. Conclude with `Set.mul_mem_mul (Set.inv_mem_inv.mpr h₁) h₂`.

Introduce `γ _ δ _ hγδ`. Simplify using `using hγδ`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Rewrite using `[hne]`. Simplify using the standard rewrite rules.

Establish `hx` using `hB (g * infGL E a y) M key F`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Cj.H.cvGrow :
    UpperTheory.V.Cj.H.CvGrow := by
  intro E _ _ _ a ha μ _ _ ψ hψc hψs F g
  obtain ⟨B, hB0, hB⟩ := cvCount (GA E a) (latticeGL E a) μ ψ hψc hψs
  have hKc : IsCompact (tsupport ψ) := hψs.isCompact
  obtain ⟨C, N, hC⟩ := latCount E a ha ((tsupport ψ)⁻¹ * tsupport ψ) (hKc.inv.mul hKc) g
  refine ⟨B * ‖F‖ * C, N, fun y => ?_⟩
  obtain ⟨M, hM, hcard⟩ := hC y
  have key : ∀ h : GA E a,
      {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.encard ≤ (M : ℕ∞) := by
    intro h
    by_cases hne : {γ : latticeGL E a | ψ ((↑γ * h)⁻¹ * (g * infGL E a y)) ≠ 0}.Nonempty
    · obtain ⟨γ₀, hγ₀⟩ := hne
      refine le_trans (Set.encard_le_encard_of_injOn (f := fun γ => γ * γ₀⁻¹) ?_ ?_) hcard
      · intro γ hγ
        simp only [Set.mem_setOf_eq] at hγ hγ₀ ⊢
        have h₁ := subset_tsupport ψ hγ
        have h₂ := subset_tsupport ψ hγ₀
        have e : (g * infGL E a y)⁻¹ * ↑(γ * γ₀⁻¹) * (g * infGL E a y)
            = ((↑γ * h)⁻¹ * (g * infGL E a y))⁻¹ * ((↑γ₀ * h)⁻¹ * (g * infGL E a y)) := by
          push_cast
          group
        rw [e]
        exact Set.mul_mem_mul (Set.inv_mem_inv.mpr h₁) h₂
      · intro γ _ δ _ hγδ
        simpa using hγδ
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hx := hB (g * infGL E a y) M key F
  calc ‖cv ψ F (g * infGL E a y)‖ ≤ B * M * ‖F‖ := hx
    _ = B * ‖F‖ * M := by ring
    _ ≤ B * ‖F‖ * (C * height y ^ N) :=
        mul_le_mul_of_nonneg_left hM (mul_nonneg hB0 (norm_nonneg _))
    _ = B * ‖F‖ * C * height y ^ N := by ring
