import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.TypePrimeProduct

/- English proof (translation)
Introduce `hqv`. Establish `hcop : Nat.Coprime p q` using `(Nat.coprime_primes hp hq).2 hpq`. Establish `hZ : IsCoprime (p : ℤ) (q : ℤ)` using `Nat.isCoprime_iff_coprime.2 hcop`. Establish `hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F)`. Use `hZ.map (Int.castRingHom (𝓞 F))` as an intermediate fact.

Simplify using `using this`. Take `⟨a, b, hab⟩` from `hO`. Establish `h1 : (1 : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[← hab]`. Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)`.

Conclude with `v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)`.
-/
theorem natPrime_not_mem_of_other (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal) : (q : 𝓞 F) ∉ v.asIdeal := by
  intro hqv
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  have hZ : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hO : IsCoprime (p : 𝓞 F) (q : 𝓞 F) := by
    have := hZ.map (Int.castRingHom (𝓞 F))
    simpa using this
  obtain ⟨a, b, hab⟩ := hO
  have h1 : (1 : 𝓞 F) ∈ v.asIdeal := by
    rw [← hab]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hpv) (v.asIdeal.mul_mem_left b hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]`. Establish `h` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)`. Rewrite `h` using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq]`. Simplify using `using h`.
-/
theorem isUnit_natCast_of_not_mem (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (q : ℕ) (hq : (q : 𝓞 F) ∉ v.asIdeal) :
    IsUnit ((q : ℕ) : v.adicCompletionIntegers F) := by
  rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (q : 𝓞 F)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hq] at h
  simpa using h

/- English proof (translation)
Establish `hqv` using `natPrime_not_mem_of_other F v hp hq hpq hpv`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]`. Rewrite using `[Nat.cast_mul]`. Conclude with `v.asIdeal.mul_mem_right _ hpv`.
-/
theorem main_two (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hpv : (p : 𝓞 F) ∈ v.asIdeal)
    (hm : IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p : ℕ) : v.adicCompletionIntegers F)}) :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) =
      Ideal.span {((p * q : ℕ) : v.adicCompletionIntegers F)} ∧
      ((p * q : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hqv := natPrime_not_mem_of_other F v hp hq hpq hpv
  refine ⟨?_, ?_⟩
  · rw [hm, Nat.cast_mul, Ideal.span_singleton_mul_right_unit (isUnit_natCast_of_not_mem F v q hqv)]
  · rw [Nat.cast_mul]; exact v.asIdeal.mul_mem_right _ hpv

end GlobalTheory.St.G.TypePrimeProduct

open GlobalTheory.St.G.TypePrimeProduct in

/- English proof (translation)
Introduce `F _ _ gp hgp hne i v hv hm`. Use `fin_cases i`. Take `⟨h1, h2⟩` from `main_two F v (hgp 0) (hgp 1) hne hv hm`. Conclude with `⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩`. Take `⟨h1, h2⟩` from `main_two F v (hgp 1) (hgp 0) hne.symm hv hm`.

Rewrite using `[mul_comm (gp 0)]`. Conclude with `⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩`.
-/
theorem GlobalTheory.St.G.TypePrimeProduct.uniformiser_prod : ∀ (F : Type) [Field F] [NumberField F] (gp : Fin 2 → ℕ), (∀ i, (gp i).Prime) → gp 0 ≠ gp 1 → ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp i : ℕ) : v.adicCompletionIntegers F)} → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((gp 0 * gp 1 : ℕ) : v.adicCompletionIntegers F)} ∧ ((gp 0 * gp 1 : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ ∃ q : ℕ, 0 < q ∧ gp 0 * gp 1 = gp i * q := by
  intro F _ _ gp hgp hne i v hv hm
  fin_cases i
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 0) (hgp 1) hne hv hm
    exact ⟨h1, h2, gp 1, (hgp 1).pos, rfl⟩
  · obtain ⟨h1, h2⟩ := main_two F v (hgp 1) (hgp 0) hne.symm hv hm
    rw [mul_comm (gp 0)]
    exact ⟨h1, h2, gp 0, (hgp 0).pos, rfl⟩
