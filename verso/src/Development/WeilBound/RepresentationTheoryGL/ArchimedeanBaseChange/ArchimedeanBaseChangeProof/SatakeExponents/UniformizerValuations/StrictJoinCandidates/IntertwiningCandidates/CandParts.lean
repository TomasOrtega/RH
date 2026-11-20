import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `| _, .leaf V z => by simp [Tr.AllLeaves, Tr.leafList] | _, .node t₁ t₂ => by rw [Tr.AllLeaves, Tr.leafList, allLeaves_iff Q t₁, allLeaves_iff Q t₂] simp only [List.mem_append] constructor · rintro ⟨h₁, h₂⟩ x (hx | hx) · exact h₁ x hx · exact h₂ x hx · intro h exact ⟨fun x hx => h …`.
-/
theorem allLeaves_iff (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.AllLeaves Q ↔ ∀ x ∈ t.leafList, Q x.1 x.2
  | _, .leaf V z => by simp [Tr.AllLeaves, Tr.leafList]
  | _, .node t₁ t₂ => by
    rw [Tr.AllLeaves, Tr.leafList, allLeaves_iff Q t₁, allLeaves_iff Q t₂]
    simp only [List.mem_append]
    constructor
    · rintro ⟨h₁, h₂⟩ x (hx | hx)
      · exact h₁ x hx
      · exact h₂ x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), fun x hx => h x (Or.inr hx)⟩

/- English proof (translation)
Introduce `j`. Establish `hmem : (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ t.leafList.filter fun x => 0 < x.1`. Rewrite using `[← ht]`. Conclude with `List.mem_ofFn.2 ⟨j, rfl⟩`. Rewrite `hmem` using `[List.mem_filter]`.

Take `⟨hx, hpos⟩` from `hmem`. Establish `h` using `(allLeaves_iff _ t).1 hl _ hx`. Break down `h with h0 | hQ` into its components or cases. Simplify using `only [decide_eq_true_eq] at hpos`. Conclude with `absurd h0 (Nat.pos_iff_ne_zero.1 hpos)`.

Conclude with `hQ`.
-/
theorem parts_of_leaves {N : ℕ} (t : Tr E N) (P : Pre E N) (Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop)
    (ht : TreeParts t P) (hl : t.AllLeaves fun M V => M = 0 ∨ Q M V) : ∀ j, Q (P.N j) (P.V j) := by
  intro j
  have hmem : (⟨P.N j, P.V j⟩ : Σ M : ℕ, Submodule ℂ (Sm E M)) ∈ t.leafList.filter fun x => 0 < x.1 := by
    rw [← ht]
    exact List.mem_ofFn.2 ⟨j, rfl⟩
  rw [List.mem_filter] at hmem
  obtain ⟨hx, hpos⟩ := hmem
  have h := (allLeaves_iff _ t).1 hl _ hx
  rcases h with h0 | hQ
  · simp only [decide_eq_true_eq] at hpos
    exact absurd h0 (Nat.pos_iff_ne_zero.1 hpos)
  · exact hQ

end PositivityTheory.Rg.BcB.F.FX.Bo.CandidateLeafDecomposition

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F

/- English proof (translation)
Introduce `hR E _ _ _ n π S F₀ d i s₁ s₂ Pa Pb D hC`. Conclude with `⟨CandidateLeafDecomposition.parts_of_leaves s₁ Pa _ hC.ctx.t₁ hC.leaves₁, CandidateLeafDecomposition.parts_of_leaves s₂ Pb _ hC.ctx.t₂ hC.leaves₂⟩`.
-/
theorem CandParts_holds : CandParts := by
  intro hR E _ _ _ n π S F₀ d i s₁ s₂ Pa Pb D hC
  exact ⟨CandidateLeafDecomposition.parts_of_leaves s₁ Pa _ hC.ctx.t₁ hC.leaves₁,
    CandidateLeafDecomposition.parts_of_leaves s₂ Pb _ hC.ctx.t₂ hC.leaves₂⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
