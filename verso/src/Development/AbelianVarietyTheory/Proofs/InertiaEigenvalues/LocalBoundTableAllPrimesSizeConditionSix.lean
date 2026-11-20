import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `D L P X C tf hC`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `i hi π hπ`. Establish `hk` using `((hC.kill i hi).1 π hπ).2`. Use `show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _`.

Unfold `TwistedPlaces.epsL at hk ⊢`. Establish `: (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j _ l _ show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2`.

Unfold `TwistedPlaces.epsL`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adm6_tab : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.adm6 L (tab L X tf C) := by
  intro D L P X C tf hC
  refine ⟨?_, ?_⟩
  · intro i hi π hπ
    have hk := ((hC.kill i hi).1 π hπ).2
    show (Br.sPi D.loc D.nbr i (X.ρ i) π : ℝ) + TwistedPlaces.epsL (D.nd.l i) ≤ _
    unfold TwistedPlaces.epsL at hk ⊢
    have : (2 : ℝ) / (D.nd.l i : ℝ) ^ 2 = 1 / (D.nd.l i : ℝ) ^ 2 + 1 / (D.nd.l i : ℝ) ^ 2 := by ring
    rw [this]
    linarith
  · intro j _ l _
    show TwistedPlaces.epsL l + TwistedPlaces.epsL l ≤ 2 / (l : ℝ) ^ 2
    unfold TwistedPlaces.epsL
    apply le_of_eq
    ring

end GlobalTheory.NLink
