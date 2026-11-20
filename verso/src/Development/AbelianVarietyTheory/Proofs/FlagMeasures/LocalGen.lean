import Mathlib

namespace GlobalTheory.LocalGenerators

/- English proof (translation)
Establish `hP : P.asIdeal ≠ ⊤` using `P.isPrime.ne_top`. Establish `hlt : ¬ J ≤ J * P.asIdeal`. Introduce `h`. Establish `heq : J * P.asIdeal = J * ⊤`. Rewrite using `[Ideal.mul_top]`.

Conclude with `le_antisymm Ideal.mul_le_left h`. Conclude with `hP (mul_left_cancel₀ hJ heq)`. Take `⟨d, hdJ, hdn⟩` from `SetLike.not_le_iff_exists.mp hlt`. Establish `hd0 : d ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hdn (Submodule.zero_mem _)`. Establish `hdvd : J ∣ Ideal.span {d}` using `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)`. Take `⟨K, hK⟩` from `hdvd`. Establish `hKP : ¬ K ≤ P.asIdeal`. Introduce `h`.

Apply `hdn` to reduce the goal to its premises. Establish `: Ideal.span {d} ≤ J * P.asIdeal` using `hK ▸ Ideal.mul_mono_right h`. Conclude with `this (Ideal.mem_span_singleton_self d)`. Take `⟨s, hsK, hsP⟩` from `SetLike.not_le_iff_exists.mp hKP`. Use `⟨d, hdJ, hd0, s, hsP, ?_⟩` and prove the remaining obligations.

Introduce `y hy`. Establish `hm : s * y ∈ Ideal.span {d}`. Rewrite using `[hK, mul_comm s y]`. Conclude with `Ideal.mul_mem_mul hy hsK`. Take `⟨o, ho⟩` from `Ideal.mem_span_singleton'.mp hm`.

Conclude with `⟨o, ho.symm⟩`.
-/
theorem local_gen {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : IsDedekindDomain.HeightOneSpectrum R) (J : Ideal R) (hJ : J ≠ ⊥) :
    ∃ d ∈ J, d ≠ (0 : R) ∧ ∃ s ∉ P.asIdeal, ∀ y ∈ J, ∃ o : R, s * y = o * d := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : ¬ J ≤ J * P.asIdeal := by
    intro h
    have heq : J * P.asIdeal = J * ⊤ := by
      rw [Ideal.mul_top]; exact le_antisymm Ideal.mul_le_left h
    exact hP (mul_left_cancel₀ hJ heq)
  obtain ⟨d, hdJ, hdn⟩ := SetLike.not_le_iff_exists.mp hlt
  have hd0 : d ≠ 0 := by
    rintro rfl; exact hdn (Submodule.zero_mem _)
  have hdvd : J ∣ Ideal.span {d} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  obtain ⟨K, hK⟩ := hdvd
  have hKP : ¬ K ≤ P.asIdeal := by
    intro h
    apply hdn
    have : Ideal.span {d} ≤ J * P.asIdeal := hK ▸ Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self d)
  obtain ⟨s, hsK, hsP⟩ := SetLike.not_le_iff_exists.mp hKP
  refine ⟨d, hdJ, hd0, s, hsP, ?_⟩
  intro y hy
  have hm : s * y ∈ Ideal.span {d} := by
    rw [hK, mul_comm s y]; exact Ideal.mul_mem_mul hy hsK
  obtain ⟨o, ho⟩ := Ideal.mem_span_singleton'.mp hm
  exact ⟨o, ho.symm⟩

/- English proof (translation)
Introduce `E _ _ P J hJ`. Conclude with `local_gen P J hJ`.
-/
theorem main : ∀ {E : Type} [inst : Field E] [NumberField E]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (J : Ideal (NumberField.RingOfIntegers E)), J ≠ ⊥ →
    ∃ d ∈ J, d ≠ (0 : NumberField.RingOfIntegers E) ∧
      ∃ s ∉ IsDedekindDomain.HeightOneSpectrum.asIdeal P, ∀ y ∈ J,
        ∃ (o : NumberField.RingOfIntegers E), s * y = o * d := by
  intro E _ _ P J hJ
  exact local_gen P J hJ

end GlobalTheory.LocalGenerators
