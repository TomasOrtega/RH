import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.
-/
theorem allLeaves_mono {E : Type} [Field E] [NumberField E] [IsCMField E]
    {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (hPQ : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact fun h => hPQ _ _ h
  | node t₁ t₂ i₁ i₂ => exact fun h => ⟨i₁ h.1, i₂ h.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem factorStep_holds : FactorStep := by
  intro h4 E _ _ _ N W hW
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, fun K _ =>
      ⟨fun _ => ∅, fun M => ⟨Set.finite_empty, by simp⟩, ?_⟩⟩
    intro U _ _ _ _ _ _ hU
    obtain ⟨ψ, hψ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    refine ⟨.leaf ⊤ 0, LinearMap.id, trivial, Or.inl ⟨rfl, rfl, rfl⟩, Or.inl rfl,
      fun _ _ _ => rfl, fun χ _ => ?_, ψ, hψ, hne⟩
    exact ⟨(mulChi 0 (Model.absC E 0)).symm χ, trivial, by simp⟩
  · obtain ⟨Ω, hΩ, h⟩ := h4 E N W hW
    refine ⟨Ω, hΩ, fun K hK => ?_⟩
    obtain ⟨Θ, hΘ, h'⟩ := h K hK
    refine ⟨Θ, hΘ, ?_⟩
    intro U hs ha hg hn hc hi hU
    obtain ⟨t, T, hG, hL, he, hm, hne⟩ := h' U hN hs ha hg hn hc hi hU
    exact ⟨t, T, red_of_leaves hL, hG, allLeaves_mono (fun M V h => Or.inr h.2) hL, he, hm, hne⟩

end GlobalTheory.CompanionTheory.EGlue

end
