import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemLpLiftL2DiscreteQuotientOnCompact

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

open scoped Pointwise in
/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ _`. Use `⟨fun F => ?_, fun C hC => ?_⟩` and prove the remaining obligations. Rewrite using `[MeasureTheory.locallyIntegrable_iff]`. Introduce `K hK`. Conclude with `(GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2`.

Establish `hfin` using `GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)`. Use `⟨hfin.toFinset.card, fun g => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty`. Take `⟨γ0, hγ0⟩` from `hne`. Combine the equalities or inequalities in the displayed calculation.

Apply `Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)` to reduce the goal to its premises. Introduce `γ hγ`. Use `⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`. Introduce `a _ b _ h`.

Simplify using `using h`. Use `_ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card`. Rewrite using `[Set.not_nonempty_iff_eq_empty.1 hne]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.V.Cj.H.locInt :
    UpperTheory.V.Cj.H.LocInt := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _
  refine ⟨fun F => ?_, fun C hC => ?_⟩
  · rw [MeasureTheory.locallyIntegrable_iff]
    intro K hK
    exact (GlobalTheory.AutomorphicL2Local.memLp_restrict_compact G Γ μ F K hK).2
  · have hfin := GlobalTheory.AutomorphicL2Unitary.finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    refine ⟨hfin.toFinset.card, fun g => ?_⟩
    by_cases hne : {γ : Γ | ↑γ * g ∈ C}.Nonempty
    · obtain ⟨γ0, hγ0⟩ := hne
      calc {γ : Γ | ↑γ * g ∈ C}.encard ≤ {δ : Γ | ↑δ ∈ C * C⁻¹}.encard := by
            apply Set.encard_le_encard_of_injOn (f := fun γ => γ * γ0⁻¹)
            · intro γ hγ
              refine ⟨↑γ * g, hγ, (↑γ0 * g)⁻¹, Set.inv_mem_inv.2 hγ0, ?_⟩
              simp [mul_assoc]
            · intro a _ b _ h
              simpa using h
        _ = hfin.toFinset.card := hfin.encard_eq_coe_toFinset_card
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]
      simp
