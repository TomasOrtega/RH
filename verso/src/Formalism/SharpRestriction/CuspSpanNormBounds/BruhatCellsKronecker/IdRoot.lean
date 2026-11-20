import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.UnitriangularFrameLift
import Lemmata.GeneralBFactUpperVersion.Imports

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open NumberField IsDedekindDomain

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_upper_version.goal1 .. | (apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply @Bl.genera …`.
-/
theorem iroot_mem {R : Type} [CommRing R] [IsDomain R] (ζ : R) (M : ℕ) (P : Ideal R) (h1 : ζ ≠ 1) (hM : ζ ^ M = 1)
    (hP : ζ - 1 ∈ P) : (M : R) ∈ P := by
  first | exact Bl.general_b_fact_upper_version.goal1 .. | (apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_upper_version.goal1 <;> assumption) | (apply @Bl.general_b_fact_upper_version.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM hP | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 hM | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P h1 | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M P | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ M | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› ζ | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R ‹_› | exact @Bl.general_b_fact_upper_version.goal1 R

/- English proof (translation)
Introduce `R _ _ ζ N g1 g2 P1 P2 hN hζN hg1 hg2 hne hP1 hP2 h1 h2 hz1 hz2`. Assume the negation of the conclusion as `hζ`. Establish `hfin : IsOfFinOrder ζ` using `isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hζN⟩`. Establish `hMpos : 0 < orderOf ζ` using `orderOf_pos_iff.2 hfin`. Establish `hM1 : ((orderOf ζ : ℕ) : R) ∈ P1` using `iroot_mem ζ _ P1 hζ (pow_orderOf_eq_one ζ) hz1`.

Establish `hdvd : g1 ∣ orderOf ζ`. Assume the negation of the conclusion as `hnd`. Conclude with `id_coprime_notMem P1 hP1 g1 _ ((Nat.Prime.coprime_iff_not_dvd hg1).2 hnd) h1 hM1`. Take `⟨k, hk⟩` from `hdvd`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hk` using `[mul_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hklt : k < orderOf ζ`. Rewrite using `[hk]`.

Use `hg1.two_le` as an intermediate fact. Establish `hkpos : 0 < k` using `Nat.pos_of_ne_zero hk0`. Use the polynomial consequences of the given equalities and inequalities. Establish `hη : ζ ^ k ≠ 1` using `pow_ne_one_of_lt_orderOf hk0 hklt`. Establish `hηg : (ζ ^ k) ^ g1 = 1`.

Rewrite using `[← pow_mul, mul_comm, ← hk]`. Conclude with `pow_orderOf_eq_one ζ`. Establish `hηP : ζ ^ k - 1 ∈ P2`. Take `⟨w, hw⟩` from `sub_dvd_pow_sub_pow ζ 1 k`. Rewrite `hw` using `[one_pow]`.

Rewrite using `[hw]`. Conclude with `P2.mul_mem_right _ hz2`. Establish `hg1P2 : (g1 : R) ∈ P2` using `iroot_mem (ζ ^ k) g1 P2 hη hηg hηP`. Conclude with `id_coprime_notMem P2 hP2 g2 g1 ((Nat.coprime_primes hg2 hg1).2 hne.symm) h2 hg1P2`.
-/
theorem id_root : RootsOfUnityFormal := by
  intro R _ _ ζ N g1 g2 P1 P2 hN hζN hg1 hg2 hne hP1 hP2 h1 h2 hz1 hz2
  by_contra hζ
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN, hζN⟩
  have hMpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hM1 : ((orderOf ζ : ℕ) : R) ∈ P1 := iroot_mem ζ _ P1 hζ (pow_orderOf_eq_one ζ) hz1
  have hdvd : g1 ∣ orderOf ζ := by
    by_contra hnd
    exact id_coprime_notMem P1 hP1 g1 _ ((Nat.Prime.coprime_iff_not_dvd hg1).2 hnd) h1 hM1
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hk
    omega
  have hklt : k < orderOf ζ := by
    rw [hk]
    have := hg1.two_le
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    nlinarith
  have hη : ζ ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hklt
  have hηg : (ζ ^ k) ^ g1 = 1 := by
    rw [← pow_mul, mul_comm, ← hk]
    exact pow_orderOf_eq_one ζ
  have hηP : ζ ^ k - 1 ∈ P2 := by
    obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow ζ 1 k
    rw [one_pow] at hw
    rw [hw]
    exact P2.mul_mem_right _ hz2
  have hg1P2 : (g1 : R) ∈ P2 := iroot_mem (ζ ^ k) g1 P2 hη hηg hηP
  exact id_coprime_notMem P2 hP2 g2 g1 ((Nat.coprime_primes hg2 hg1).2 hne.symm) h2 hg1P2

/- English proof (translation)
Introduce `E _ _ p hp`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `(Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp) |>.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.2 hp.ne_zero)`. Take `⟨Q, hQ, hc⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]`. Conclude with `bot_le)`.

Establish `hpQ : (p : 𝓞 E) ∈ Q`. Establish `: (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E))`. Rewrite using `[hc]`. Conclude with `Ideal.mem_span_singleton_self _`. Simplify using `using this`.

Use `⟨⟨Q, hQ.isPrime, ?_⟩, hpQ⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `(Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 hpQ)`.
-/
theorem id_over : ExistsPrimeAbove := by
  intro E _ _ p hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    (Ideal.span_singleton_prime (Int.natCast_ne_zero.2 hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp) |>.isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact Int.natCast_ne_zero.2 hp.ne_zero)
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) (Ideal.span {(p : ℤ)}) (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact bot_le)
  have hpQ : (p : 𝓞 E) ∈ Q := by
    have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
      rw [hc]; exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, ?_⟩, hpQ⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Submodule.mem_bot _).1 hpQ)

end Formalism.MainNotions.BridgeLemma

end
