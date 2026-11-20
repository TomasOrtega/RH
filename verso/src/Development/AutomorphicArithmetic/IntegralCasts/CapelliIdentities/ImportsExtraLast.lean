import Mathlib

namespace DedekindLocalUniformizer
end DedekindLocalUniformizer

/- English proof (translation)
Introduce `R _ _ P hmax hbot`. Use `haveI : P.IsPrime := hmax.isPrime`. Establish `hlt : P ^ (1 + 1) < P ^ 1` using `Ideal.pow_succ_lt_pow hbot 1`. Rewrite `hlt` using `[pow_one]`. Take `⟨π, hπP, hπ2⟩` from `SetLike.exists_of_lt hlt`.

Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Conclude with `hπ2 (Ideal.zero_mem _)`. Use `⟨π, hπ0, hπP, ?_⟩` and prove the remaining obligations. Establish `hle : Ideal.span {π} ≤ P` using `(Ideal.span_singleton_le_iff_mem P).2 hπP`.

Take `⟨J, hJ⟩` from `(Ideal.dvd_iff_le).2 hle`. Establish `hJP : ¬ J ≤ P`. Introduce `h`. Apply `hπ2` to reduce the goal to its premises. Establish `: Ideal.span {π} ≤ P ^ 2`.

Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`. Conclude with `this (Ideal.mem_span_singleton_self π)`. Take `⟨s, hsJ, hsP⟩` from `Set.not_subset.1 hJP`. Use `⟨s, hsP, fun y hy => ?_⟩` and prove the remaining obligations.

Establish `hmem : s * y ∈ Ideal.span {π}`. Rewrite using `[hJ, mul_comm s y]`. Conclude with `Ideal.mul_mem_mul hy hsJ`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.1 hmem`. Conclude with `⟨c, by rw [← hc, mul_comm]⟩`.
-/
theorem UpperTheory.Reformulated.B.Yde5.main :
    ∀ {R : Type} [inst : CommRing R] [IsDedekindDomain R] (P : Ideal R),
      P.IsMaximal → P ≠ ⊥ → ∃ (π : R), π ≠ (0 : R) ∧ π ∈ P ∧ ∃ s ∉ P, ∀ y ∈ P, ∃ (c : R), s * y = π * c := by
  intro R _ _ P hmax hbot
  haveI : P.IsPrime := hmax.isPrime
  have hlt : P ^ (1 + 1) < P ^ 1 := Ideal.pow_succ_lt_pow hbot 1
  rw [pow_one] at hlt
  obtain ⟨π, hπP, hπ2⟩ := SetLike.exists_of_lt hlt
  have hπ0 : π ≠ 0 := by
    rintro rfl; exact hπ2 (Ideal.zero_mem _)
  refine ⟨π, hπ0, hπP, ?_⟩
  have hle : Ideal.span {π} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 hπP
  obtain ⟨J, hJ⟩ := (Ideal.dvd_iff_le).2 hle
  have hJP : ¬ J ≤ P := by
    intro h
    apply hπ2
    have : Ideal.span {π} ≤ P ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.1 hJP
  refine ⟨s, hsP, fun y hy => ?_⟩
  have hmem : s * y ∈ Ideal.span {π} := by
    rw [hJ, mul_comm s y]; exact Ideal.mul_mem_mul hy hsJ
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨c, by rw [← hc, mul_comm]⟩
