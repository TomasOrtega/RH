import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `R _ F`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `E n hn`. Establish `hz : ∀ α : Cochain ((chains R).obj E) (res R F) n, α = 0`. Introduce `α`.

Apply `(GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α 0` to reduce the goal to its premises. Introduce `p s h U x`. Establish `hs : s < 0` using `by omega`. Use `haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs)`. Conclude with `Subsingleton.elim _ _`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `a.mk_surjective`. Take `⟨b, rfl⟩` from `b.mk_surjective`. Establish `: a = b` using `Cocycle.ext (by rw [hz a.1, hz b.1])`. Rewrite using `[this]`.

Set `f : ∀ X : Scheme.{0}, Sec F X →+ H R (sch.obj X) F 0` to `fun X => AddMonoidHom.mk' (secClass F (X := X)) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.1`. Use `⟨fun X => AddEquiv.ofBijective (f X) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.1, ?_, ?_⟩` and prove the remaining obligations. Introduce `Y X g s`. Conclude with `(GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.2.1 g s`. Introduce `X s`.

Take `⟨α, hα⟩` from `(secClass F s).mk_surjective`. Conclude with `⟨α, hα, ((GlobalTheory.T.degreeZeroSectionClass_properties R F X).1 s α).2 hα⟩`.
-/
theorem etale_cohomology_vanishing_negative_degree_zero : A9 := by
  intro R _ F
  refine ⟨?_, ?_⟩
  · intro E n hn
    have hz : ∀ α : Cochain ((chains R).obj E) (res R F) n, α = 0 := by
      intro α
      apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R).2.2.1 α 0
      intro p s h U x
      have hs : s < 0 := by omega
      haveI := ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_sections_exactness R F U).2.2.2 s hs)
      exact Subsingleton.elim _ _
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := a.mk_surjective
    obtain ⟨b, rfl⟩ := b.mk_surjective
    have : a = b := Cocycle.ext (by rw [hz a.1, hz b.1])
    rw [this]
  · let f : ∀ X : Scheme.{0}, Sec F X →+ H R (sch.obj X) F 0 := fun X =>
      AddMonoidHom.mk' (secClass F (X := X)) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.1
    refine ⟨fun X => AddEquiv.ofBijective (f X) (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.1, ?_, ?_⟩
    · intro Y X g s
      exact (GlobalTheory.T.degreeZeroSectionClass_properties R F X).2.2.2.1 g s
    · intro X s
      obtain ⟨α, hα⟩ := (secClass F s).mk_surjective
      exact ⟨α, hα, ((GlobalTheory.T.degreeZeroSectionClass_properties R F X).1 s α).2 hα⟩

end GlobalTheory.EtC
