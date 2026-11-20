import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.HostCls
open Formalism.BasicNotions NumberField

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `I using UniqueFactorizationMonoid.induction_on_prime with`. Consider the case `h₁ => exact absurd rfl hI`. Consider the case `h₂ J hJ`. Rewrite `h` using `[Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top]`. Conclude with `absurd (Nat.dvd_one.1 h) hp.one_lt.ne'`.

Consider the case `h₃ J P hJ hP ih`. Rewrite `h` using `[map_mul]`. Break down `(Nat.Prime.dvd_mul hp).1 h with h | h` into its components or cases. Conclude with `⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩`. Take `⟨Q, hQ, hle, hd⟩` from `ih hJ h`.

Conclude with `⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩`.
-/
theorem exists_prime_ge_dvd_absNorm {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] {p : ℕ} (hp : p.Prime) (I : Ideal S) (hI : I ≠ ⊥)
    (h : p ∣ Ideal.absNorm I) :
    ∃ P : Ideal S, P.IsPrime ∧ I ≤ P ∧ p ∣ Ideal.absNorm P := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ J hJ =>
    rw [Ideal.isUnit_iff.1 hJ, Ideal.absNorm_top] at h
    exact absurd (Nat.dvd_one.1 h) hp.one_lt.ne'
  | h₃ J P hJ hP ih =>
    rw [map_mul] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact ⟨P, Ideal.isPrime_of_prime hP, Ideal.mul_le_left, h⟩
    · obtain ⟨Q, hQ, hle, hd⟩ := ih hJ h
      exact ⟨Q, hQ, Ideal.mul_le_right.trans hle, hd⟩

/- English proof (translation)
Introduce `D T p h`. Take `⟨hp, -, hc, -⟩` from `h`. Establish `hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1` using `((primeClass_eq_inert_iff _).1 hc).2.2.2.1`. Rewrite using `[Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]`. Introduce `hd`.

Take `⟨P, hP, hle, hdP⟩` from `exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd`. Take `⟨h1, h2⟩` from `D.host.ccK_split P hP hle`. Rewrite `h2` using `[← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP]`. Conclude with `hj h2`.
-/
theorem coprime_absNorm_ccK_of_gIdx :
    ∀ (D : D7) (T p : ℕ), GIdx D.host T p → Nat.Coprime (Ideal.absNorm D.host.ccK) p := by
  intro D T p h
  obtain ⟨hp, -, hc, -⟩ := h
  have hj : jacobiSym (-(D.host.d : ℤ)) p ≠ 1 :=
    ((primeClass_eq_inert_iff _).1 hc).2.2.2.1
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hd
  obtain ⟨P, hP, hle, hdP⟩ := exists_prime_ge_dvd_absNorm hp _ D.host.ccK_ne_bot hd
  obtain ⟨h1, h2⟩ := D.host.ccK_split P hP hle
  rw [← (Nat.prime_dvd_prime_iff_eq hp h1).1 hdP] at h2
  exact hj h2

end GlobalTheory
