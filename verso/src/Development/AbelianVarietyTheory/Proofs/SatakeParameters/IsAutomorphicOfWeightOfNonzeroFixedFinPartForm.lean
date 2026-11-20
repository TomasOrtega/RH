import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

open GlobalTheory.DefU

namespace GlobalTheory.Cong

/- English proof (translation)
Introduce `E _ _ _ n π W K f hf hf0 hK`. Use `⟨π.isAut, fun τ => ?_, ?_⟩` and prove the remaining obligations. Establish `h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ))` using `hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Establish `h'` using `h`.

Rewrite `h'` using `[← Wt.at_embedding W (InfinitePlace.mk τ), e]`. Conclude with `h'`. Establish `h2` using `h.conjugate`. Rewrite `h2` using `[← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ]`. Conclude with `h2`.

Establish `hne : f.1 ≠ 0` using `fun h => hf0 (Subtype.ext h)`. Choose the witnesses or unpack the hypotheses as in `⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hne (LinearMap.ext hc)`.

Use `⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`. Rewrite using `[RU_apply]`. Conclude with `hK x hx v g`.
-/
theorem ofType_of_finPart_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n)
    (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) →
    OfType (fun τ => W.at τ) K π.V := by
  intro E _ _ _ n π W K f hf hf0 hK
  refine ⟨π.isAut, fun τ => ?_, ?_⟩
  · have h : (AU.mk π).HasWt (InfinitePlace.mk τ).embedding (W (InfinitePlace.mk τ)) :=
      hasWeightAt_of_finPart π W hf hf0 (InfinitePlace.mk τ)
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · have h' := h
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), e] at h'
      exact h'
    · have h2 := h.conjugate
      rw [← Wt.at_embedding W (InfinitePlace.mk τ), ← Wt.at_conjugate, e, ComplexEmbedding.involutive_conjugate E τ] at h2
      exact h2
  · have hne : f.1 ≠ 0 := fun h => hf0 (Subtype.ext h)
    obtain ⟨v, hv⟩ : ∃ v, f.1 v ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hne (LinearMap.ext hc)
    refine ⟨f.1 v, AutSub.mem_finPart.1 hf v, hv, fun x hx => ?_⟩
    funext g
    rw [RU_apply]
    exact hK x hx v g

/- English proof (translation)
The claim follows from `ofType_of_finPart_fixed`.
-/
example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AutSub E n) (W : Wt E n) (K : Subgroup (UA E n)) (f : algForms W), f ∈ π.finPart W → f ≠ 0 → (∀ k ∈ K, ∀ v g, f.1 v (g * k) = f.1 v g) → OfType (fun τ => W.at τ) K π.V := ofType_of_finPart_fixed

end GlobalTheory.Cong

end
