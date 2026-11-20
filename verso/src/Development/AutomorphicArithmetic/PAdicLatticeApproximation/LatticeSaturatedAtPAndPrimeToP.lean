import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Introduce `p hp D X`. Establish `hpp : p.Prime` using `hp.out`. Establish `h2 : ∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat`. Introduce `w hw`. Take `⟨t, ht0, htc, ht⟩` from `DenEnd.exists_coprime_nsmul_mem D (X.r w)`.

Use `⟨t, ht0, htc, nsmul_mem hw t, ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul]`. Conclude with `ht`. Use `⟨?_, h2, ?_⟩` and prove the remaining obligations. Introduce `w hw`.

Take `⟨k, hk⟩` from `(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[map_nsmul]`. Conclude with `nsmul_mem hw _`. Introduce `w`.

Take `⟨k, hk⟩` from `(UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w`. Take `⟨t, ht0, -, ht⟩` from `h2 _ hk`. Use `⟨t * p ^ k, Nat.mul_ne_zero ht0.ne' (pow_ne_zero _ hpp.ne_zero), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `ht`.
-/
theorem UpperTheory.lattice_saturated_at_p_and_prime_to_p :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D), (∀ w : VQ D, X.r w ∈ LaHat D → ∃ k : ℕ, p ^ k • w ∈ X.lat) ∧ (∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat) ∧ ∀ w : VQ D, ∃ m : ℕ, m ≠ 0 ∧ m • w ∈ X.lat := by
  intro p hp D X
  have hpp : p.Prime := hp.out
  have h2 : ∀ w ∈ X.M, ∃ m : ℕ, 0 < m ∧ m.Coprime p ∧ m • w ∈ X.lat := by
    intro w hw
    obtain ⟨t, ht0, htc, ht⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r w)
    refine ⟨t, ht0, htc, nsmul_mem hw t, ?_⟩
    rw [map_nsmul]
    exact ht
  refine ⟨?_, h2, ?_⟩
  · intro w hw
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    refine ⟨k, hk, ?_⟩
    rw [map_nsmul]
    exact nsmul_mem hw _
  · intro w
    obtain ⟨k, hk⟩ := (UpperTheory.p_lattice_saturated_and_cofinite p D X.M X.hM).2 w
    obtain ⟨t, ht0, -, ht⟩ := h2 _ hk
    refine ⟨t * p ^ k, Nat.mul_ne_zero ht0.ne' (pow_ne_zero _ hpp.ne_zero), ?_⟩
    rw [mul_smul]
    exact ht
