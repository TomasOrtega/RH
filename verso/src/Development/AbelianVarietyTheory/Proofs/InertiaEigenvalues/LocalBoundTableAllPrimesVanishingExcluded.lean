import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `D L P X C tf h`. Take `⟨h3, hq, hd, -, -, hsl⟩` from `h.small`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `i _ hl`. Take `⟨hlt, -, hexc⟩` from `hl`.

Establish `hexc' : D.nd.l i ∉ X.exc` using `hexc`. Establish `h2 : D.nd.l i ∉ D.host.small` using `fun he => by linarith [hsl _ he]`. Establish `h3' : D.nd.l i ≠ 3`. Introduce and unpack `he`. Rewrite `hlt` using `[he]`.

Move the coercions through the operations in `at hlt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq' : D.nd.l i ≠ D.host.q`. Introduce and unpack `he`. Rewrite `hlt` using `[he]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hd' : D.nd.l i ≠ D.host.d`. Introduce and unpack `he`. Rewrite `hlt` using `[he]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i)` using `fun hr => hr.2.2 ⟨hlt, hexc'⟩`. Use `⟨fun lam _ => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [tab, h2, h3', hR, if_false]`. Simplify using `only [tab, h2, hR, if_false]`. Apply the tactic sequence `rw [if_neg (by rintro (he | he) <;> contradiction)]`.

Conclude with `h.exc.1`. Conclude with `h.exc.2`.
-/
theorem largePrimeLengthVanishing_and_exceptionalBounded_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ)
    (tf : TwistedPlaces.Tab L), Concl L P X C → TwistedPlaces.LargePrimeLengthVanishing L (tab L X tf C) ∧ TwistedPlaces.ExceptionalPrimesBounded L (tab L X tf C) := by
  intro D L P X C tf h
  obtain ⟨h3, hq, hd, -, -, hsl⟩ := h.small
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hlt, -, hexc⟩ := hl
    have hexc' : D.nd.l i ∉ X.exc := hexc
    have h2 : D.nd.l i ∉ D.host.small := fun he => by linarith [hsl _ he]
    have h3' : D.nd.l i ≠ 3 := by
      rintro he; rw [he] at hlt; push_cast at hlt; linarith
    have hq' : D.nd.l i ≠ D.host.q := by
      rintro he; rw [he] at hlt; linarith
    have hd' : D.nd.l i ≠ D.host.d := by
      rintro he; rw [he] at hlt; linarith
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun hr => hr.2.2 ⟨hlt, hexc'⟩
    refine ⟨fun lam _ => ?_, ?_⟩
    · simp only [tab, h2, h3', hR, if_false]
    · simp only [tab, h2, hR, if_false]
      rw [if_neg (by rintro (he | he) <;> contradiction)]
  · exact h.exc.1
  · exact h.exc.2

end GlobalTheory.NLink
