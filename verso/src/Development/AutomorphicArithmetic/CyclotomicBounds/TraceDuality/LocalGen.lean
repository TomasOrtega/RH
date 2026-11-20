import Mathlib
open NumberField
open scoped TensorProduct NNReal

/- English proof (translation)
Introduce `E _ _ p hp`. Establish `hD : differentIdeal ℤ (𝓞 E) ≠ ⊥` using `differentIdeal_ne_bot`. Generalize the expression as in `differentIdeal ℤ (𝓞 E) = D at hD ⊢`. Establish `hP : Ideal.span {(p : 𝓞 E)} ≠ ⊥` using `by simpa using hp.ne_zero`. Establish `hPtop : Ideal.span {(p : 𝓞 E)} ≠ ⊤`.

Introduce `h`. Establish `h1` using `congrArg Ideal.absNorm h`. Rewrite `h1` using `[Ideal.absNorm_span_natCast, Ideal.absNorm_top]`. Establish `h2 : 0 < Module.finrank ℤ (𝓞 E)` using `Module.finrank_pos`. Break down `Nat.pow_eq_one.mp h1 with h | h` into its components or cases.

Conclude with `hp.one_lt.ne' h`. Use linear arithmetic over natural numbers and integers. Take `⟨d, hd⟩` from `IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(p : 𝓞 E)} * D) (J := D) Ideal.mul_le_right (mul_ne_zero hP hD)`. Establish `hle : Ideal.span {d} ≤ D` using `hd ▸ le_sup_right`. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.mpr hle`.

Establish `hco : Ideal.span {(p : 𝓞 E)} ⊔ J = ⊤`. Apply `mul_left_cancel₀ hD` to reduce the goal to its premises. Rewrite using `[Ideal.mul_sup, Ideal.mul_top, ← hJ, mul_comm]`. Conclude with `hd`. Establish `hJ0 : J ≠ ⊥`.

Introduce and unpack `rfl`. Conclude with `hPtop (by simpa using hco)`. Use `⟨d, Ideal.absNorm J, hle (Ideal.mem_span_singleton_self d), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `: D * J = 0` using `by rw [← hJ]; simp`.

Conclude with `mul_ne_zero hD hJ0 this`. Introduce `h`. Take `⟨P, hPm, hu, hdv⟩` from `Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h`. Establish `hpP : (p : 𝓞 E) ∈ P`. Establish `h1 : (p : ℤ) ∈ Ideal.under ℤ P` using `hu ▸ Ideal.mem_span_singleton_self _`.

Simplify `h1` using `[Ideal.under, Ideal.mem_comap]`. Apply `hPm.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hco]`. Conclude with `sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP) (Ideal.dvd_iff_le.mp hdv)`. Introduce `a ha`.

Rewrite using `[← Ideal.mem_span_singleton, hJ, mul_comm (_ : 𝓞 E)]`. Conclude with `Ideal.mul_mem_mul ha (Ideal.absNorm_mem J)`.
-/
theorem UpperTheory.WildB.localGen :
    ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → ∃ (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) ∧ d ≠ 0 ∧ ¬ p ∣ m ∧ ∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a := by
  intro E _ _ p hp
  have hD : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  generalize differentIdeal ℤ (𝓞 E) = D at hD ⊢
  have hP : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by simpa using hp.ne_zero
  have hPtop : Ideal.span {(p : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    have h2 : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
    rcases Nat.pow_eq_one.mp h1 with h | h
    · exact hp.one_lt.ne' h
    · omega
  obtain ⟨d, hd⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(p : 𝓞 E)} * D) (J := D)
    Ideal.mul_le_right (mul_ne_zero hP hD)
  have hle : Ideal.span {d} ≤ D := hd ▸ le_sup_right
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hco : Ideal.span {(p : 𝓞 E)} ⊔ J = ⊤ := by
    apply mul_left_cancel₀ hD
    rw [Ideal.mul_sup, Ideal.mul_top, ← hJ, mul_comm]
    exact hd
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    exact hPtop (by simpa using hco)
  refine ⟨d, Ideal.absNorm J, hle (Ideal.mem_span_singleton_self d), ?_, ?_, ?_⟩
  · rintro rfl
    have : D * J = 0 := by rw [← hJ]; simp
    exact mul_ne_zero hD hJ0 this
  · intro h
    obtain ⟨P, hPm, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp J h
    have hpP : (p : 𝓞 E) ∈ P := by
      have h1 : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
      simpa [Ideal.under, Ideal.mem_comap] using h1
    apply hPm.ne_top
    rw [eq_top_iff, ← hco]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr hpP) (Ideal.dvd_iff_le.mp hdv)
  · intro a ha
    rw [← Ideal.mem_span_singleton, hJ, mul_comm (_ : 𝓞 E)]
    exact Ideal.mul_mem_mul ha (Ideal.absNorm_mem J)
