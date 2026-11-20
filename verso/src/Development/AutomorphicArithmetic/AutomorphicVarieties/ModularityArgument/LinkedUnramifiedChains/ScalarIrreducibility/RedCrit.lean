import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Introduce `A _ _ q hq h1 h2 a ha`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `N : Submodule A A` to `Submodule.span A {a}`. Establish `hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0`.

Introduce `x`. Rewrite using `[Module.mem_annihilator]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)`.

Introduce `h m`. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.mp m.2`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `x * (m : A) = 0`. Rewrite using `[← hc, smul_eq_mul, mul_left_comm, h, mul_zero]`.

Establish `hle : Module.annihilator A N ≤ q`. Introduce `x hx`. Assume the negation of the conclusion as `hxq`. Conclude with `hcon x hxq ((hann x).mp hx)`. Take `⟨P, hP, hPq⟩` from `Ideal.exists_minimalPrimes_le hle`.

Establish `hPass : P ∈ associatedPrimes A N` using `Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP`. Establish `hPA : P ∈ associatedPrimes A A` using `associatedPrimes.subset_of_injective N.injective_subtype hPass`. Establish `hPmin` using `h1 P hPA hPq`. Take `⟨s, hsP, hs⟩` from `h2 P hPmin hPq a (ha P hPmin.1.1 hPq)`. Conclude with `hsP (hP.1.2 ((hann s).mpr hs))`.
-/
theorem UpperTheory.V.J.redCrit :
    ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (q : Ideal A), q.IsPrime → (∀ P ∈ associatedPrimes A A, P ≤ q → P ∈ minimalPrimes A) →
        (∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0) → ∀ a : A, (∀ P : Ideal A, P.IsPrime → P ≤ q → a ∈ P) → ∃ s ∉ q, s * a = 0 := by
  intro A _ _ q hq h1 h2 a ha
  by_contra hcon
  push_neg at hcon
  let N : Submodule A A := Submodule.span A {a}
  have hann : ∀ x, x ∈ Module.annihilator A N ↔ x * a = 0 := by
    intro x
    rw [Module.mem_annihilator]
    constructor
    · intro h
      exact congrArg Subtype.val (h ⟨a, Submodule.mem_span_singleton_self a⟩)
    · intro h m
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp m.2
      apply Subtype.ext
      change x * (m : A) = 0
      rw [← hc, smul_eq_mul, mul_left_comm, h, mul_zero]
  have hle : Module.annihilator A N ≤ q := by
    intro x hx
    by_contra hxq
    exact hcon x hxq ((hann x).mp hx)
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le hle
  have hPass : P ∈ associatedPrimes A N :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes A N hP
  have hPA : P ∈ associatedPrimes A A :=
    associatedPrimes.subset_of_injective N.injective_subtype hPass
  have hPmin := h1 P hPA hPq
  obtain ⟨s, hsP, hs⟩ := h2 P hPmin hPq a (ha P hPmin.1.1 hPq)
  exact hsP (hP.1.2 ((hann s).mpr hs))
