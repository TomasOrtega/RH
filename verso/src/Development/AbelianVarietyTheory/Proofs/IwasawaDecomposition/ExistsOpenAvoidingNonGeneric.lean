import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace GlobalTheory

/- English proof (translation)
Introduce `X _ P G hG U z hzU hgen`. Take `⟨U', hU', hzU', hU'U⟩` from `(Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU`. Establish `: IsNoetherianRing Γ(X, U')` using `IsLocallyNoetherian.component_noetherian ⟨U', hU'⟩`. Use `haveI hN : NoetherianSpace (U' : Set X) := noetherianSpace_of_isAffineOpen U' hU'`. Establish `hC : IsClosed {x : (U' : Set X) | (x : X) ∉ G}` using `(hG.preimage continuous_subtype_val).isClosed_compl`.

Take `⟨S, hS, hSc, hSi, hSeq⟩` from `NoetherianSpace.exists_finite_set_isClosed_irreducible hC`. Set `F : Set (Set (U' : Set X))` to `{T | T ∈ S ∧ z ∉ closure (Subtype.val '' T)}`. Establish `hF : F.Finite` using `hS.subset (fun T hT => hT.1)`. Set `K : Set X` to `⋃ T ∈ F, closure (Subtype.val '' T)`. Establish `hK : IsClosed K` using `hF.isClosed_biUnion (fun _ _ => isClosed_closure)`.

Use `⟨⟨(U' : Set X) ∩ Kᶜ, U'.isOpen.inter hK.isOpen_compl⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun x hx => hU'U hx.1`. Use `⟨hzU', ?_⟩` and prove the remaining obligations. Simplify using `only [K, Set.mem_compl_iff, Set.mem_iUnion, not_exists]`. Conclude with `fun T hT => hT.2`.

Introduce and unpack `q ⟨hqU', hqK⟩ hPq`. Distinguish the cases in `hqG : q ∈ G`. Conclude with `Or.inl hqG`. Use `right`. Establish `hqC : (⟨q, hqU'⟩ : (U' : Set X)) ∈ ⋃₀ S` using `by rw [← hSeq]; exact hqG`.

Take `⟨T, hTS, hqT⟩` from `hqC`. Establish `hzT : z ∈ closure (Subtype.val '' T)`. Assume the negation of the conclusion as `hz`. Conclude with `hqK (Set.mem_biUnion (x := T) ⟨hTS, hz⟩ (subset_closure ⟨_, hqT, rfl⟩))`. Establish `hirr : IsIrreducible (Subtype.val '' T)` using `(hSi T hTS).image _ continuous_subtype_val.continuousOn`.

Take `⟨c, hc⟩` from `QuasiSober.sober hirr.closure isClosed_closure`. Establish `hcU' : c ∈ (U' : Set X)` using `(hc.mem_open_set_iff U'.isOpen).mpr ⟨q, subset_closure ⟨_, hqT, rfl⟩, hqU'⟩`. Establish `hcG : c ∉ G`. Establish `hsub : closure (Subtype.val '' T) ⊆ Gᶜ` using `closure_minimal (by rintro _ ⟨x, hx, rfl⟩; have := hSeq ▸ (Set.subset_sUnion_of_mem hTS hx); exact this) hG.isClosed_compl`. Conclude with `hsub hc.mem`.

Establish `hcq : c ⤳ q` using `hc.specializes (subset_closure ⟨_, hqT, rfl⟩)`. Distinguish the cases in `hne : c = q`. Substitute `hne` using the available equality. Conclude with `hc.specializes hzT`. Conclude with `absurd (hgen q (hU'U hqU') hPq c hcq hne) hcG`.
-/
theorem shrink_nbhd_generise_centre : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (P : X → Prop) (G : Set X),
    IsOpen G → ∀ (U : X.Opens) (z : X), z ∈ U → (∀ q ∈ U, P q → ∀ η : X, η ⤳ q → η ≠ q → η ∈ G) →
      ∃ V : X.Opens, V ≤ U ∧ z ∈ V ∧ ∀ q ∈ V, P q → q ∈ G ∨ q ⤳ z := by
  intro X _ P G hG U z hzU hgen
  obtain ⟨U', hU', hzU', hU'U⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have : IsNoetherianRing Γ(X, U') := IsLocallyNoetherian.component_noetherian ⟨U', hU'⟩
  haveI hN : NoetherianSpace (U' : Set X) := noetherianSpace_of_isAffineOpen U' hU'

  have hC : IsClosed {x : (U' : Set X) | (x : X) ∉ G} := (hG.preimage continuous_subtype_val).isClosed_compl
  obtain ⟨S, hS, hSc, hSi, hSeq⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  let F : Set (Set (U' : Set X)) := {T | T ∈ S ∧ z ∉ closure (Subtype.val '' T)}
  have hF : F.Finite := hS.subset (fun T hT => hT.1)
  let K : Set X := ⋃ T ∈ F, closure (Subtype.val '' T)
  have hK : IsClosed K := hF.isClosed_biUnion (fun _ _ => isClosed_closure)
  refine ⟨⟨(U' : Set X) ∩ Kᶜ, U'.isOpen.inter hK.isOpen_compl⟩, ?_, ?_, ?_⟩
  · exact fun x hx => hU'U hx.1
  · refine ⟨hzU', ?_⟩
    simp only [K, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    exact fun T hT => hT.2
  · rintro q ⟨hqU', hqK⟩ hPq
    by_cases hqG : q ∈ G
    · exact Or.inl hqG
    right
    have hqC : (⟨q, hqU'⟩ : (U' : Set X)) ∈ ⋃₀ S := by rw [← hSeq]; exact hqG
    obtain ⟨T, hTS, hqT⟩ := hqC
    have hzT : z ∈ closure (Subtype.val '' T) := by
      by_contra hz
      exact hqK (Set.mem_biUnion (x := T) ⟨hTS, hz⟩ (subset_closure ⟨_, hqT, rfl⟩))
    have hirr : IsIrreducible (Subtype.val '' T) := (hSi T hTS).image _ continuous_subtype_val.continuousOn
    obtain ⟨c, hc⟩ := QuasiSober.sober hirr.closure isClosed_closure

    have hcU' : c ∈ (U' : Set X) := (hc.mem_open_set_iff U'.isOpen).mpr
      ⟨q, subset_closure ⟨_, hqT, rfl⟩, hqU'⟩
    have hcG : c ∉ G := by
      have hsub : closure (Subtype.val '' T) ⊆ Gᶜ := closure_minimal
        (by rintro _ ⟨x, hx, rfl⟩; have := hSeq ▸ (Set.subset_sUnion_of_mem hTS hx); exact this) hG.isClosed_compl
      exact hsub hc.mem
    have hcq : c ⤳ q := hc.specializes (subset_closure ⟨_, hqT, rfl⟩)
    by_cases hne : c = q
    · subst hne
      exact hc.specializes hzT
    · exact absurd (hgen q (hU'U hqU') hPq c hcq hne) hcG

end GlobalTheory
