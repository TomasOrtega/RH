import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CplUniq
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.GoingDown

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

/- English proof (translation)
Introduce `C R _ _ _ _ _ x _ h`. Take `⟨-, ⟨e⟩, -⟩` from `UpperTheory.V.CA.cpl_uniq x h`. Establish `hflat : Module.Flat C R`. Establish `h1 : Module.Flat (Localization.AtPrime x) (Cpl x)` using `inferInstance`. Establish `h2 : Module.Flat C (Localization.AtPrime x)` using `IsLocalization.flat _ x.primeCompl`.

Establish `h3 : Module.Flat C (Cpl x)` using `Module.Flat.trans C (Localization.AtPrime x) (Cpl x)`. Conclude with `Module.Flat.of_linearEquiv e.toLinearEquiv`. Establish `hx : (maximalIdeal R).comap (algebraMap C R) = x` using `by simpa using h.comap_pow 1`. Establish `gd : ∀ (p : Ideal C) (q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q.comap (algebraMap C R) → ∃ Q : Ideal R, Q ≤ q ∧ Q.IsPrime ∧ Q.comap (algebraMap C R) = p`. Introduce `p q hp hq hle`.

Use `haveI : q.LiesOver (q.comap (algebraMap C R)) := ⟨rfl⟩`. Take `⟨Q, hQ, hQp, hQo⟩` from `Ideal.exists_ideal_le_liesOver_of_le q hle`. Conclude with `⟨Q, hQ, hQp, hQo.over.symm⟩`. Establish `hmin : ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes, q.comap (algebraMap C R) ∈ I.minimalPrimes`. Introduce `I q hq`.

Use `haveI : q.IsPrime := hq.1.1`. Use `⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hq.1.2⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `p ⟨hp, hIp⟩ hle`. Take `⟨Q, hQ, hQp, hQo⟩` from `gd p q hp this hle`. Establish `: q ≤ Q` using `hq.2 ⟨hQp, Ideal.map_le_iff_le_comap.2 (hQo ▸ hIp)⟩ hQ`.

Rewrite using `[← hQo]`. Conclude with `Ideal.comap_mono this`. Use `⟨hflat, ?_, ?_, ?_, hmin⟩` and prove the remaining obligations. Introduce `p hp hle`. Take `⟨Q, -, hQp, hQo⟩` from `gd p (maximalIdeal R) hp inferInstance (hx.symm ▸ hle)`.

Conclude with `⟨Q, hQp, hQo⟩`. Introduce `q hq`. Rewrite using `[← hx]`. Conclude with `Ideal.comap_mono (le_maximalIdeal hq.ne_top)`. Introduce `q hq`.

Apply `hmin ⊥ q` to reduce the goal to its premises. Rewrite using `[Ideal.map_bot]`. Conclude with `hq`.
-/
theorem UpperTheory.V.CA.c3a :
    ∀ {C R : Type} [CommRing C] [IsNoetherianRing C] [CommRing R] [Algebra C R] [IsLocalRing R] (x : Ideal C) [x.IsMaximal], IsCplAt x R → Module.Flat C R ∧ (∀ p : Ideal C, p.IsPrime → p ≤ x → ∃ q : Ideal R, q.IsPrime ∧ q.comap (algebraMap C R) = p) ∧ (∀ q : Ideal R, q.IsPrime → q.comap (algebraMap C R) ≤ x) ∧ (∀ q ∈ minimalPrimes R, q.comap (algebraMap C R) ∈ minimalPrimes C) ∧ ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes, q.comap (algebraMap C R) ∈ I.minimalPrimes := by
  intro C R _ _ _ _ _ x _ h
  obtain ⟨-, ⟨e⟩, -⟩ := UpperTheory.V.CA.cpl_uniq x h
  have hflat : Module.Flat C R := by
    have h1 : Module.Flat (Localization.AtPrime x) (Cpl x) := inferInstance
    have h2 : Module.Flat C (Localization.AtPrime x) := IsLocalization.flat _ x.primeCompl
    have h3 : Module.Flat C (Cpl x) := Module.Flat.trans C (Localization.AtPrime x) (Cpl x)
    exact Module.Flat.of_linearEquiv e.toLinearEquiv
  have hx : (maximalIdeal R).comap (algebraMap C R) = x := by simpa using h.comap_pow 1
  have gd : ∀ (p : Ideal C) (q : Ideal R), p.IsPrime → q.IsPrime → p ≤ q.comap (algebraMap C R) →
      ∃ Q : Ideal R, Q ≤ q ∧ Q.IsPrime ∧ Q.comap (algebraMap C R) = p := by
    intro p q hp hq hle
    haveI : q.LiesOver (q.comap (algebraMap C R)) := ⟨rfl⟩
    obtain ⟨Q, hQ, hQp, hQo⟩ := Ideal.exists_ideal_le_liesOver_of_le q hle
    exact ⟨Q, hQ, hQp, hQo.over.symm⟩
  have hmin : ∀ (I : Ideal C), ∀ q ∈ (I.map (algebraMap C R)).minimalPrimes,
      q.comap (algebraMap C R) ∈ I.minimalPrimes := by
    intro I q hq
    haveI : q.IsPrime := hq.1.1
    refine ⟨⟨Ideal.comap_isPrime _ _, Ideal.map_le_iff_le_comap.1 hq.1.2⟩, ?_⟩
    rintro p ⟨hp, hIp⟩ hle
    obtain ⟨Q, hQ, hQp, hQo⟩ := gd p q hp this hle
    have : q ≤ Q := hq.2 ⟨hQp, Ideal.map_le_iff_le_comap.2 (hQo ▸ hIp)⟩ hQ
    rw [← hQo]
    exact Ideal.comap_mono this
  refine ⟨hflat, ?_, ?_, ?_, hmin⟩
  · intro p hp hle
    obtain ⟨Q, -, hQp, hQo⟩ := gd p (maximalIdeal R) hp inferInstance (hx.symm ▸ hle)
    exact ⟨Q, hQp, hQo⟩
  · intro q hq
    rw [← hx]
    exact Ideal.comap_mono (le_maximalIdeal hq.ne_top)
  · intro q hq
    apply hmin ⊥ q
    rw [Ideal.map_bot]
    exact hq
