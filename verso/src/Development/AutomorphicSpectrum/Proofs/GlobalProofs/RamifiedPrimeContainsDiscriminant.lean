import Mathlib

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.GlobalFiniteness

/- English proof (translation)
Assume the negation of the conclusion as `ht`. Establish `hv0 : P.under (𝓞 F) ≠ ⊥` using `Ideal.under_ne_bot (𝓞 F) hP0`. Establish `hvp : (P.under (𝓞 F)).IsPrime` using `inferInstance`. Set `v : HeightOneSpectrum (𝓞 F)` to `⟨P.under (𝓞 F), hvp, hv0⟩`. Establish `hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P` using `fun n hn => by`.

Establish `: algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P` using `hn`. Simplify `this` using `[map_natCast]`. Establish `hvS : v ∉ S`. Introduce `hvS`. Apply `ht` to reduce the goal to its premises.

Rewrite using `[Nat.cast_mul]`. Apply `Ideal.mul_mem_left` to reduce the goal to its premises. Establish `hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm` using `Finset.dvd_prod_of_mem _ hvS`. Take `⟨c, hc⟩` from `hd`. Rewrite using `[hc, Nat.cast_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))`. Establish `hlies : P.LiesOver v.asIdeal` using `⟨rfl⟩`. Establish `hun : Algebra.IsUnramifiedAt (𝓞 F) P` using `hS v hvS P hP hlies`. Rewrite `hdvd` using `[differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)]`. Break down `(Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h` into its components or cases.

Conclude with `not_dvd_differentIdeal_iff.2 hun h`. Apply `ht` to reduce the goal to its premises. Rewrite using `[Nat.cast_mul]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `hcast` to reduce the goal to its premises.

Establish `hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal` using `Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)`. Apply `hmap` to reduce the goal to its premises. Rewrite using `[← absNorm_differentIdeal F (𝓞 F)]`. Conclude with `Ideal.absNorm_mem _`.
-/
theorem natAbs_discr_mul_prod_absNorm_mem_of_dvd_differentIdeal
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : ∀ v ∉ S, Algebra.IsUnramifiedIn (𝓞 E) v.asIdeal)
    (P : Ideal (𝓞 E)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) (hdvd : P ∣ differentIdeal ℤ (𝓞 E)) :
    (((discr F).natAbs * ∏ v ∈ S, v.asIdeal.absNorm : ℕ) : 𝓞 E) ∈ P := by
  by_contra ht
  have hv0 : P.under (𝓞 F) ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
  have hvp : (P.under (𝓞 F)).IsPrime := inferInstance
  let v : HeightOneSpectrum (𝓞 F) := ⟨P.under (𝓞 F), hvp, hv0⟩
  have hcast : ∀ (n : ℕ), (n : 𝓞 F) ∈ v.asIdeal → (n : 𝓞 E) ∈ P := fun n hn => by
    have : algebraMap (𝓞 F) (𝓞 E) (n : 𝓞 F) ∈ P := hn
    simpa [map_natCast] using this
  have hvS : v ∉ S := by
    intro hvS
    apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_left
    have hd : v.asIdeal.absNorm ∣ ∏ w ∈ S, w.asIdeal.absNorm := Finset.dvd_prod_of_mem _ hvS
    obtain ⟨c, hc⟩ := hd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hcast _ (Ideal.absNorm_mem _))
  have hlies : P.LiesOver v.asIdeal := ⟨rfl⟩
  have hun : Algebra.IsUnramifiedAt (𝓞 F) P := hS v hvS P hP hlies
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E)] at hdvd
  rcases (Ideal.prime_of_isPrime hP0 hP).dvd_or_dvd hdvd with h | h
  · exact not_dvd_differentIdeal_iff.2 hun h
  · apply ht
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    apply hcast
    have hmap : differentIdeal ℤ (𝓞 F) ≤ v.asIdeal := Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hmap
    rw [← absNorm_differentIdeal F (𝓞 F)]
    exact Ideal.absNorm_mem _

end GlobalTheory.CompanionTheory.GlobalFiniteness
