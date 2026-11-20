import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.RecT

namespace GlobalTheory.RecT

/- English proof (translation)
The claim follows from `GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds`.
-/
theorem geometricLemma_holds : GlobalTheory.Published.GeometricLemma :=
  GlobalTheory.geometricLemma_of_filtration GlobalTheory.bernsteinZelevinskyFiniteness_holds GlobalTheory.geometricLemmaFiltration_holds

/- English proof (translation)
Introduce `k _ _ _ _ t y x hd hsq`. Establish `hG` using `geometricLemma_holds`. Establish `hBZ` using `GlobalTheory.bernsteinZelevinskyFiniteness_holds`. Use `choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)`. Establish `hx : HasSupport x.rep (∑ i, s i)` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq`.

Establish `down : ∀ P : IrrGL k → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) → ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z`. Introduce and unpack `P ⟨u, hu, hP⟩ i`. Use `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx` as an intermediate fact. Conclude with `⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩`. Establish `up : ∀ P : IrrGL k → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) → ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z`.

Introduce `P h`. Use `choose u hu hP using h`. Use `⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨i, -, hz⟩` from `Multiset.mem_sum.1 hz`. Conclude with `hP i z hz`.

Conclude with `⟨down _, down _, up _, up _⟩`.
-/
theorem good_toral_of_isSubquotient_prodIrr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : ℕ) (y : Fin t → IrrGL k) (x : IrrGL k) (hd : ∑ i, (y i).1 = x.1),
    IsSubquotient x.rep (prodIrr y hd) → (Good x → ∀ i, Good (y i)) ∧ (Toral x → ∀ i, Toral (y i)) ∧
      ((∀ i, Good (y i)) → Good x) ∧ ((∀ i, Toral (y i)) → Toral x) := by
  intro k _ _ _ _ t y x hd hsq
  have hG := geometricLemma_holds
  have hBZ := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  choose s hs using fun i => GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG (y i)
  have hx : HasSupport x.rep (∑ i, s i) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hs x.2.rep.irr hsq

  have down : ∀ P : IrrGL k → Prop, (∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z) →
      ∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z := by
    rintro P ⟨u, hu, hP⟩ i
    have := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hu hx
    exact ⟨s i, hs i, fun z hz => hP z (this ▸ Multiset.mem_sum.2 ⟨i, Finset.mem_univ _, hz⟩)⟩

  have up : ∀ P : IrrGL k → Prop, (∀ i, ∃ u, HasSupport (y i).rep u ∧ ∀ z ∈ u, P z) →
      ∃ u, HasSupport x.rep u ∧ ∀ z ∈ u, P z := by
    intro P h
    choose u hu hP using h
    refine ⟨∑ i, u i, GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr hu x.2.rep.irr hsq, fun z hz => ?_⟩
    obtain ⟨i, -, hz⟩ := Multiset.mem_sum.1 hz
    exact hP i z hz
  exact ⟨down _, down _, up _, up _⟩

end GlobalTheory.RecT
