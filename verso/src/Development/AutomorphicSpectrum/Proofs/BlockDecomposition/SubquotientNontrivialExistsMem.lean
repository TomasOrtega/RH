import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.SubQuotNe

/- English proof (translation)
Introduce `M W X _ _ _ _ _ ρ σ S T hE hX`. Take `⟨e⟩` from `hE`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hle : S.toSubmodule ≤ T.toSubmodule` using `fun s hs => h s hs`.

Use `haveI : Subsingleton (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) := Submodule.Quotient.subsingleton_iff.mpr (Submodule.comap_subtype_eq_top.mpr hle)`. Conclude with `not_subsingleton X e.toLinearEquiv.symm.injective.subsingleton`.
-/
theorem exists_mem_not_mem_of_subQuot_equiv :
    ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X]
      (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ),
      Nonempty ((subQuot S T).Equiv σ) → Nontrivial X →
        ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  intro M W X _ _ _ _ _ ρ σ S T hE hX
  obtain ⟨e⟩ := hE
  by_contra h
  push_neg at h
  have hle : S.toSubmodule ≤ T.toSubmodule := fun s hs => h s hs
  haveI : Subsingleton (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
    Submodule.Quotient.subsingleton_iff.mpr (Submodule.comap_subtype_eq_top.mpr hle)
  exact not_subsingleton X e.toLinearEquiv.symm.injective.subsingleton

end GlobalTheory.CompanionTheory.SubQuotNe
