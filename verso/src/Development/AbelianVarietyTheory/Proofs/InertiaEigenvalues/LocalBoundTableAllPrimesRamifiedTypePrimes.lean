import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `D L P X C tf hC`. Use `⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩` and prove the remaining obligations. Introduce `i _ hl`. Take `⟨hq, hd, hq8, hd16, -⟩` from `D.host.hyp`. Establish `h3q` using `D.host.q_ne_three`.

Establish `h2 : D.nd.l i ∉ D.host.small` using `UpperTheory.Small.not_mem_of_qd D.host hl`. Apply the tactic sequence `have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega`. Establish `hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i)` using `fun h => h.2.1 hl`. Establish `hlen : (tab L X tf C).len i = fun _ => 0`. Use function extensionality and compare the values at `lam`.

Simplify using `only [tab, h2, h3, hR, if_false]`. Establish `hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i)`. Simplify using `only [tab, h2, hl, if_false, if_true]`. Rewrite using `[hlen, hBB]`. Simplify using `[TwistedPlaces.sumOver]`.

Introduce `j hj l hl`. Conclude with `⟨hC.typ j hj l hl, le_rfl⟩`.
-/
theorem localBoundTableAllPrimes_ramified_typePrimes : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ) (tf : TwistedPlaces.Tab L),
    Concl L P X C → TwistedPlaces.RamifiedPrimeLengthBound L (tab L X tf C) C ∧ TwistedPlaces.GeneratorPrimeEtaBound L (tab L X tf C) C := by
  intro D L P X C tf hC
  refine ⟨⟨?_, hC.small.2.2.2.2.1⟩, ?_⟩
  · intro i _ hl
    obtain ⟨hq, hd, hq8, hd16, -⟩ := D.host.hyp
    have h3q := D.host.q_ne_three
    have h2 : D.nd.l i ∉ D.host.small := UpperTheory.Small.not_mem_of_qd D.host hl
    have h3 : D.nd.l i ≠ 3 := by rcases hl with h | h <;> rw [h] <;> omega
    have hR : ¬ KillingConditions.RangeAD L X.exc (D.nd.l i) := fun h => h.2.1 hl
    have hlen : (tab L X tf C).len i = fun _ => 0 := by
      funext lam
      simp only [tab, h2, h3, hR, if_false]
    have hBB : (tab L X tf C).BB i = TwistedPlaces.midG L C (D.nd.l i) := by
      simp only [tab, h2, hl, if_false, if_true]
    rw [hlen, hBB]
    simp [TwistedPlaces.sumOver]
  · intro j hj l hl
    exact ⟨hC.typ j hj l hl, le_rfl⟩

end GlobalTheory.NLink
