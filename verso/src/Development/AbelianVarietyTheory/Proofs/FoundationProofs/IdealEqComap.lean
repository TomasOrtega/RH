import Mathlib

namespace GlobalTheory.IdealComapPreimage

open IsDedekindDomain

/- English proof (translation)
Use `set e := Rat.ringOfIntegersEquiv`. Use `haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Use `haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.surjective`. Use `symm`. Use `Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_` and prove the remaining obligations.

Introduce `x hx`. Rewrite `hx` using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Take `⟨k, hk⟩` from `hx`. Establish `: x = (p : NumberField.RingOfIntegers ℚ) * e.symm k`. Apply `e.injective` to reduce the goal to its premises.

Simplify using `using hk`. Rewrite using `[this]`. Conclude with `v.asIdeal.mul_mem_right _ hv`.
-/
theorem ideal_eq_comap {p : ℕ} (hp : Nat.Prime p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (Ideal.span {(p : ℤ)}) := by
  set e := Rat.ringOfIntegersEquiv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.surjective
  symm
  refine Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  have : x = (p : NumberField.RingOfIntegers ℚ) * e.symm k := by
    apply e.injective
    simpa using hk
  rw [this]
  exact v.asIdeal.mul_mem_right _ hv

/- English proof (translation)
Introduce `p hp v v' hv hv'`. Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Rewrite using `[ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']`.
-/
theorem main : ∀ {p : ℕ}, Nat.Prime p → ∀ {v v' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}, (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v' → v = v' := by
  intro p hp v v' hv hv'
  apply HeightOneSpectrum.ext
  rw [ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']

end GlobalTheory.IdealComapPreimage
