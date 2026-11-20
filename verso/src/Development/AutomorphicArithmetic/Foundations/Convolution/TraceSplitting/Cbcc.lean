import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.NormCharacterPowers.NormCharPowHolds

open NumberField in
/- English proof (translation)
Take `⟨v⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Conclude with `(InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)`.
-/
private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

open NumberField in
/- English proof (translation)
Introduce `hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn`. Use `haveI := hK`. Use `haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M`. Use `haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩`. Use `haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos`.

Use `haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)`. Take `⟨σ, hσ⟩` from `IsCyclic.exists_generator (α := M ≃ₐ[K] M)`. Use `⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩` and prove the remaining obligations. Break down `π with @⟨_, π⟩ | @⟨hR, π⟩ swap` into its components or cases. Conclude with `(not_both K hR hK).elim`.

Break down `hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩` into its components or cases. Take `⟨η, hη, e⟩` from `UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw`. Conclude with `Or.inl ⟨η, hη, Quotient.exact e⟩`. Conclude with `Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩`. Break down `P with @⟨_, P⟩ | @⟨hR, P⟩ swap` into its components or cases.

Conclude with `(not_both M hR hM).elim`. Take `⟨hinf, -, hne, -⟩` from `hPl K M hp`. Take `⟨v, hv⟩` from `hinf.nonempty`. Take `⟨w⟩` from `hne v`. Take `⟨π, ⟨h1, h2⟩, -⟩` from `hDS K M σ hσ hp n hn P hP v w hv`.

Conclude with `⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩`.
-/
theorem UpperTheory.ConvolutionTheory.T.cbcc :
    UpperTheory.ConvolutionTheory.T.Places → UpperTheory.ConvolutionTheory.T.LiftStep → UpperTheory.ConvolutionTheory.T.LiftAll → UpperTheory.ConvolutionTheory.T.DescStep → UpperTheory.ConvolutionTheory.T.SplitStrong → UpperTheory.V.Z.Bc.CBCc := by
  intro hPl hLS hLA hDS hSS K M _ _ _ _ _ _ hp hK n hn
  haveI := hK
  haveI hM : IsTotallyComplex M := isTotallyComplex_of_algebra K M
  haveI : Fact (Module.finrank K M).Prime := ⟨hp⟩
  haveI : FiniteDimensional K M := Module.finite_of_finrank_pos hp.pos
  haveI : IsCyclic (M ≃ₐ[K] M) := isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank K M)
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := M ≃ₐ[K] M)
  refine ⟨fun π => ?_, fun P hP => ?_, fun π P _ hw => UpperTheory.ConvolutionTheory.R.fibre_holds K M hp n hn π P hw⟩
  · rcases π with @⟨_, π⟩ | @⟨hR, π⟩
    swap
    · exact (not_both K hR hK).elim
    rcases hLS K M σ hσ hp n hn (fun m hm _ => hLA K M σ hσ hp m hm) π with ⟨ι, _, m, Q, hm, h2, hw⟩ | ⟨P, ⟨h1, h2⟩, h3⟩
    · obtain ⟨η, hη, e⟩ := UpperTheory.ConvolutionTheory.R.twoParts_holds K M hp n _ ι m Q hn hm h2 hw
      exact Or.inl ⟨η, hη, Quotient.exact e⟩
    · exact Or.inr ⟨.cx P, h1, fun τ m h => (h2 τ m).1 h, hSS K M σ hσ hp n hn π P h3 h1⟩
  · rcases P with @⟨_, P⟩ | @⟨hR, P⟩
    swap
    · exact (not_both M hR hM).elim
    obtain ⟨hinf, -, hne, -⟩ := hPl K M hp
    obtain ⟨v, hv⟩ := hinf.nonempty
    obtain ⟨w⟩ := hne v
    obtain ⟨π, ⟨h1, h2⟩, -⟩ := hDS K M σ hσ hp n hn P hP v w hv
    exact ⟨.cx π, h1, fun τ m h => (h2 τ m).2 h, hSS K M σ hσ hp n hn π P hP h1⟩
