import Mathlib

namespace Bl.general_b_fact_right_more

/- English proof (translation)
Introduce `E _ _ _ P`. Establish `h0 : P.asIdeal ≠ ⊥` using `P.ne_bot`. Establish `h1 : P.asIdeal ≠ ⊤` using `P.isPrime.ne_top`. Establish `hlt : P.asIdeal ^ 2 < P.asIdeal` using `Ideal.pow_lt_self _ h0 h1 2 le_rfl`. Take `⟨a, haP, ha2⟩` from `SetLike.exists_of_lt hlt`.

Establish `hdvd : P.asIdeal ∣ Ideal.span {a}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haP)`. Take `⟨J, hJ⟩` from `hdvd`. Establish `hJP : ¬ J ≤ P.asIdeal`. Introduce `hle`. Apply `ha2` to reduce the goal to its premises.

Establish `h2 : Ideal.span {a} ≤ P.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Conclude with `(Ideal.span_singleton_le_iff_mem _).mp h2`. Take `⟨c, hcJ, hcP⟩` from `SetLike.not_le_iff_exists.mp hJP`.

Use `⟨a, haP, c, hcP, fun p hp => ?_⟩` and prove the remaining obligations. Establish `hm : c * p ∈ Ideal.span {a}`. Rewrite using `[hJ, mul_comm c p]`. Conclude with `Ideal.mul_mem_mul hp hcJ`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.mp hm`.

Conclude with `⟨t, by rw [← ht, mul_comm]⟩`.
-/
theorem goal1 :
  ∀ {E : Type} [inst : Field.{0} E] [NumberField.{0} E] [StarRing.{0} E]
  (P : IsDedekindDomain.HeightOneSpectrum.{0} (NumberField.RingOfIntegers.{0} E)),
  Exists.{1} fun (a : NumberField.RingOfIntegers.{0} E) ↦
    And (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) a)
      (Exists.{1} fun (c : NumberField.RingOfIntegers.{0} E) ↦
        And (Not (Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) c))
          (∀ (p : NumberField.RingOfIntegers.{0} E),
            Membership.mem.{0, 0} (IsDedekindDomain.HeightOneSpectrum.asIdeal.{0} P) p →
              Exists.{1} fun (t : NumberField.RingOfIntegers.{0} E) ↦
                Eq.{1} (HMul.hMul.{0, 0, 0} c p) (HMul.hMul.{0, 0, 0} a t)))  := by
  intro E _ _ _ P
  have h0 : P.asIdeal ≠ ⊥ := P.ne_bot
  have h1 : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : P.asIdeal ^ 2 < P.asIdeal := Ideal.pow_lt_self _ h0 h1 2 le_rfl
  obtain ⟨a, haP, ha2⟩ := SetLike.exists_of_lt hlt
  have hdvd : P.asIdeal ∣ Ideal.span {a} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haP)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ J ≤ P.asIdeal := by
    intro hle
    apply ha2
    have h2 : Ideal.span {a} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right hle
    exact (Ideal.span_singleton_le_iff_mem _).mp h2
  obtain ⟨c, hcJ, hcP⟩ := SetLike.not_le_iff_exists.mp hJP
  refine ⟨a, haP, c, hcP, fun p hp => ?_⟩
  have hm : c * p ∈ Ideal.span {a} := by
    rw [hJ, mul_comm c p]; exact Ideal.mul_mem_mul hp hcJ
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨t, by rw [← ht, mul_comm]⟩

end Bl.general_b_fact_right_more
