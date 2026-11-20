import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FunObj

/- English proof (translation)
Establish `e` using `Nat.factorization_prod_pow_eq_self hM`. Rewrite `h` using `[← e, Finsupp.prod, Nat.cast_prod]`. Take `⟨p, hp, hmem⟩` from `(Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h`. Use `⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩` and prove the remaining obligations. Rewrite `hmem` using `[Nat.cast_pow]`.

Conclude with `w.isPrime.mem_of_pow_mem _ hmem`.
-/
theorem exists_primeFactor_mem_of_natCast_mem {D : D7} (w : Pl D.host.E) {M : ℕ} (hM : M ≠ 0)
    (h : (M : 𝓞 D.host.E) ∈ w.asIdeal) : ∃ p ∈ M.primeFactors, (p : 𝓞 D.host.E) ∈ w.asIdeal := by
  have e := Nat.factorization_prod_pow_eq_self hM
  rw [← e, Finsupp.prod, Nat.cast_prod] at h
  obtain ⟨p, hp, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 h
  refine ⟨p, by simpa [Nat.support_factorization] using hp, ?_⟩
  rw [Nat.cast_pow] at hmem
  exact w.isPrime.mem_of_pow_mem _ hmem

/- English proof (translation)
Substitute `h` using the available equality. Establish `: (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))` using `hn`. Rewrite `this` using `[Ideal.mem_comap, map_natCast]`. Conclude with `this`.
-/
theorem natCast_mem_of_under_eq {D : D7} (w : Pl D.host.E) {v : Pl D.host.F} (h : w.under (𝓞 D.host.F) = v) (n : ℕ)
    (hn : (n : 𝓞 D.host.F) ∈ v.asIdeal) : (n : 𝓞 D.host.E) ∈ w.asIdeal := by
  subst h
  have : (n : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := hn
  rw [Ideal.mem_comap, map_natCast] at this
  exact this

/- English proof (translation)
Introduce `D T L sc G U hU`. Use `set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN`. Use `set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA`. Use `set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB`. Establish `hN0 : N ≠ 0`.

Establish `h1` using `D.host.hyp.1.ne_zero`. Establish `h2` using `D.host.hyp.2.1.ne_zero`. Establish `h3` using `(D.host.g_prime 0).ne_zero`. Establish `h4` using `(D.host.g_prime 1).ne_zero`. Establish `h5 : Ideal.absNorm D.host.ccK ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `D.host.ccK_ne_bot`. Establish `h0 : D.host.QS ≠ 0` using `D.host.QS_pos.ne'`. Conclude with `mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5`. Establish `hA0 : A ≠ 0`.

Rewrite using `[hA, Finset.prod_ne_zero_iff]`. Introduce `v _`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `hB0 : B ≠ 0`.

Rewrite using `[hB, Finset.prod_ne_zero_iff]`. Introduce `t _`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `w' _`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `(w'.under (𝓞 D.host.F)).ne_bot`. Establish `hM0 : N * A * B ≠ 0` using `mul_ne_zero (mul_ne_zero hN0 hA0) hB0`. Use `⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩` and prove the remaining obligations. Introduce `w hw`. Establish `key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal`.

Introduce `n hn hmem`. Take `⟨k, hk⟩` from `hn`. Establish `hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal`. Rewrite using `[hk, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hmem`.

Take `⟨p, hp, hpm⟩` from `exists_primeFactor_mem_of_natCast_mem w hM0 hM`. Conclude with `hw p hp hpm`. Use `⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩` and prove the remaining obligations. Apply `key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)` to reduce the goal to its premises. Conclude with `dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _`.

Conclude with `natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)`. Apply `key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)` to reduce the goal to its premises. Conclude with `dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) (hU.mem_toFinset.2 ht))) _`. Conclude with `natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)`.
-/
theorem exists_std_primes : ∀ (D : D7) (T : Type) (L : LevCh D T) (sc : Consts) (G : GridData L sc) (U : Set T), U.Finite →
    ∃ S : Finset ℕ, (∀ q ∈ S, q.Prime) ∧ ∀ w : Pl D.host.E, Off S w → w.under (𝓞 D.host.F) ∉ G.pl.S0 ∧
      (∀ t ∈ U, ∀ w' ∈ L.Q t, w.under (𝓞 D.host.F) ≠ w'.under (𝓞 D.host.F)) ∧
      ((D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  intro D T L sc G U hU
  set N : ℕ := D.host.QS * D.host.q * D.host.d * D.host.g 0 * D.host.g 1 * Ideal.absNorm D.host.ccK with hN
  set A : ℕ := ∏ v ∈ G.pl.S0, Ideal.absNorm v.asIdeal with hA
  set B : ℕ := ∏ t ∈ hU.toFinset, ∏ w' ∈ L.Q t, Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal with hB
  have hN0 : N ≠ 0 := by
    have h1 := D.host.hyp.1.ne_zero
    have h2 := D.host.hyp.2.1.ne_zero
    have h3 := (D.host.g_prime 0).ne_zero
    have h4 := (D.host.g_prime 1).ne_zero
    have h5 : Ideal.absNorm D.host.ccK ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    have h0 : D.host.QS ≠ 0 := D.host.QS_pos.ne'
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4) h5
  have hA0 : A ≠ 0 := by
    rw [hA, Finset.prod_ne_zero_iff]
    intro v _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hB0 : B ≠ 0 := by
    rw [hB, Finset.prod_ne_zero_iff]
    intro t _
    rw [Finset.prod_ne_zero_iff]
    intro w' _
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact (w'.under (𝓞 D.host.F)).ne_bot
  have hM0 : N * A * B ≠ 0 := mul_ne_zero (mul_ne_zero hN0 hA0) hB0
  refine ⟨(N * A * B).primeFactors, fun p hp => Nat.prime_of_mem_primeFactors hp, ?_⟩
  intro w hw
  have key : ∀ n : ℕ, n ∣ N * A * B → (n : 𝓞 D.host.E) ∉ w.asIdeal := by
    intro n hn hmem
    obtain ⟨k, hk⟩ := hn
    have hM : ((N * A * B : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [hk, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hmem
    obtain ⟨p, hp, hpm⟩ := exists_primeFactor_mem_of_natCast_mem w hM0 hM
    exact hw p hp hpm
  refine ⟨fun hv => ?_, fun t ht w' hw' heq => ?_, key N (dvd_mul_of_dvd_left (dvd_mul_right _ _) _)⟩
  · apply key (Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hv) _) _
    · exact natCast_mem_of_under_eq w rfl _ (Ideal.absNorm_mem _)
  · apply key (Ideal.absNorm (w'.under (𝓞 D.host.F)).asIdeal)
    · exact dvd_mul_of_dvd_right ((Finset.dvd_prod_of_mem (fun w'' : Pl D.host.E => Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal) hw').trans
        (Finset.dvd_prod_of_mem (fun t => ∏ w'' ∈ L.Q t, Ideal.absNorm (w''.under (𝓞 D.host.F)).asIdeal)
          (hU.mem_toFinset.2 ht))) _
    · exact natCast_mem_of_under_eq w heq _ (Ideal.absNorm_mem _)

end GlobalTheory.FunObj
