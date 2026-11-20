import Mathlib

/- English proof (translation)
Introduce `B _ _ I p hp`. Distinguish the cases in `hI : I = ⊥`. Use `⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[hI, Ideal.mem_bot]`. Simplify using `[hx]`.

Establish `hne : ¬ I ≤ I * p`. Introduce `h`. Establish `h1 : I * p = I * 1`. Rewrite using `[mul_one]`. Conclude with `le_antisymm Ideal.mul_le_left h`.

Establish `h2 : p = 1` using `mul_left_cancel₀ (show I ≠ 0 from hI) h1`. Conclude with `hp.ne_top (by rw [h2, Ideal.one_eq_top])`. Take `⟨π, hπ, hπ'⟩` from `SetLike.not_le_iff_exists.mp hne`. Establish `hle : Ideal.span {π} ≤ I` using `(Ideal.span_singleton_le_iff_mem I).mpr hπ`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr hle`.

Establish `hJp : ¬ J ≤ p`. Introduce `h`. Apply `hπ'` to reduce the goal to its premises. Establish `: π ∈ I * J` using `hJ ▸ Ideal.mem_span_singleton_self π`. Conclude with `Ideal.mul_mono_right h this`.

Take `⟨s, hs, hs'⟩` from `SetLike.not_le_iff_exists.mp hJp`. Use `⟨π, hπ, s, hs', fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[hJ, mul_comm s x]`. Conclude with `Ideal.mul_mem_mul hx hs`.
-/
theorem UpperTheory.Reformulated.B.ExistsLocalGenerator.exists_local_generator :
    ∀ {B : Type} [inst : CommRing B] [IsDedekindDomain B] (I p : Ideal B) [hp : p.IsPrime],
      ∃ π ∈ I, ∃ s ∉ p, ∀ x ∈ I, s * x ∈ Ideal.span {π} := by
  intro B _ _ I p hp
  by_cases hI : I = ⊥
  · refine ⟨0, I.zero_mem, 1, (Ideal.ne_top_iff_one p).mp hp.ne_top, fun x hx => ?_⟩
    rw [hI, Ideal.mem_bot] at hx
    simp [hx]
  have hne : ¬ I ≤ I * p := by
    intro h
    have h1 : I * p = I * 1 := by
      rw [mul_one]
      exact le_antisymm Ideal.mul_le_left h
    have h2 : p = 1 := mul_left_cancel₀ (show I ≠ 0 from hI) h1
    exact hp.ne_top (by rw [h2, Ideal.one_eq_top])
  obtain ⟨π, hπ, hπ'⟩ := SetLike.not_le_iff_exists.mp hne
  have hle : Ideal.span {π} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hJp : ¬ J ≤ p := by
    intro h
    apply hπ'
    have : π ∈ I * J := hJ ▸ Ideal.mem_span_singleton_self π
    exact Ideal.mul_mono_right h this
  obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.mp hJp
  refine ⟨π, hπ, s, hs', fun x hx => ?_⟩
  rw [hJ, mul_comm s x]
  exact Ideal.mul_mem_mul hx hs
