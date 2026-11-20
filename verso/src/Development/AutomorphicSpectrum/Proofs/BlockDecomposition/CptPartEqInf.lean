import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.CptGen

/- English proof (translation)
Introduce `G _ _ _ _ T C hC h`. Apply `le_antisymm` to reduce the goal to its premises. Use `(Subgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce `x hx`. Conclude with `⟨hx.1, h x hx.1 hx.2⟩`.

Introduce `x hx`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩` and prove the remaining obligations. Conclude with `closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed`.
-/
theorem cptPart_eq_inf : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] (T C : Subgroup G), IsCompact (C : Set G) → (∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set G)) → t ∈ C) → cptPart T = T ⊓ C := by
  intro G _ _ _ _ T C hC h
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    exact ⟨hx.1, h x hx.1 hx.2⟩
  · intro x hx
    apply Subgroup.subset_closure
    refine ⟨hx.1, hC.of_isClosed_subset isClosed_closure ?_⟩
    exact closure_minimal (fun y hy => (Subgroup.zpowers_le.2 hx.2) hy) hC.isClosed

end GlobalTheory.CompanionTheory.CptGen
