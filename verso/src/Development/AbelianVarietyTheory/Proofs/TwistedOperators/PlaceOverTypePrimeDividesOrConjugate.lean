import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderEqOrSmulUnderEq

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLaw

/- English proof (translation)
Introduce `D P k PP h`. Break down `GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩` into its components or cases. Conclude with `Or.inl h1`. Use `Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩` and prove the remaining obligations. Rewrite `hc` using `[h2, Formalism.L2.Col.conjIdeal_eq]`.

Conclude with `hc`.
-/
theorem div_or_isConjPl_div : ∀ (D : D7) (P : Formalism.L2.Host.PiBar D.host) (k : Fin 2) (PP : Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → P.Div k PP ∨ ∃ PP', P.Div k PP' ∧ IsConjPl PP' PP := by
  intro D P k PP h
  rcases GlobalTheory.ConjOverQuad.div_or_conj_div D P k PP h with h1 | ⟨w, h1, h2⟩
  · exact Or.inl h1
  · refine Or.inr ⟨w, h1, fun c hc => ⟨Formalism.L2.Col.cO D.host.E c, ?_, rfl⟩⟩
    rw [h2, Formalism.L2.Col.conjIdeal_eq] at hc
    exact hc

end GlobalTheory.StepLaw
