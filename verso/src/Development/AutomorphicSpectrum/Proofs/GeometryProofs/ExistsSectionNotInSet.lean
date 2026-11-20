import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes

/- English proof (translation)
Introduce `R _ _ _ M _ _ htf t _ d₀ hd₀ hb V P hP hP0 hV`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `I : Ideal R` to `{ carrier := {x | ∃ u : M, d₀ • u = x • t} add_mem' := by`. Introduce and unpack `a b ⟨u, hu⟩ ⟨v, hv⟩`.

Conclude with `⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c x ⟨u, hu⟩`. Use `⟨c • u, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_comm, hu, smul_eq_mul, mul_smul] }`. Establish `hImem : ∀ x, x ∈ I ↔ ∃ u : M, d₀ • u = x • t` using `fun x => Iff.rfl`. Establish `hI0 : I ≠ ⊥`. Introduce `h`. Establish `: d₀ ∈ I` using `(hImem _).2 ⟨t, rfl⟩`.

Rewrite `this` using `[h]`. Conclude with `hd₀ (by simpa using this)`. Take `⟨e, heP, he0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`. Establish `hle : Ideal.span {e} ≤ P` using `(Ideal.span_singleton_le_iff_mem P).2 heP`. Take `⟨C, hC⟩` from `Ideal.dvd_iff_le.2 hle`.

Establish `hcz : ∀ c ∈ C, ∀ z ∈ I, c * z ∈ Ideal.span {e} * I`. Introduce `c hc z hz`. Take `⟨u, hu⟩` from `(hImem z).1 hz`. Establish `huV : u ∈ V` using `hcon z u hu`. Establish `hdiv : ∀ π ∈ P, e ∣ c * π`.

Introduce `π hπ`. Establish `: π * c ∈ Ideal.span {e}`. Rewrite using `[hC]`. Conclude with `Ideal.mul_mem_mul hπ hc`. Rewrite using `[mul_comm]`.

Conclude with `Ideal.mem_span_singleton.1 this`. Take `⟨u', hu'⟩` from `hV u huV c e he0 hdiv`. Establish `h1 : (d₀ * e) • u' = (c * z) • t`. Rewrite using `[mul_smul, hu', smul_comm, hu, mul_smul]`. Establish `h2 : d₀ * e ∣ d₀ * (c * z)` using `hb (c * z) (d₀ * e) u' (mul_ne_zero hd₀ he0) h1`.

Take `⟨w, hw⟩` from `(mul_dvd_mul_iff_left hd₀).1 h2`. Establish `h3 : d₀ • u' = w • t`. Establish `h4 : e • (d₀ • u' - w • t) = 0`. Rewrite using `[smul_sub, smul_comm, ← mul_smul e w, ← hw, ← h1, mul_smul, sub_self]`. Conclude with `sub_eq_zero.1 (htf e _ he0 h4)`.

Establish `hwI : w ∈ I` using `(hImem w).2 ⟨u', h3⟩`. Rewrite using `[hw]`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hwI`. Establish `hCI : C * I ≤ Ideal.span {e} * I` using `Ideal.mul_le.2 hcz`. Establish `h5 : Ideal.span {e} * I ≤ Ideal.span {e} * (P * I)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h6 : I ≤ P * I` using `(Ideal.span_singleton_mul_right_mono he0).1 h5`. Establish `h8 : P * I = ⊤ * I`. Rewrite using `[Ideal.top_mul]`. Conclude with `le_antisymm Ideal.mul_le_right h6`.

Conclude with `hP.ne_top (mul_right_cancel₀ hI0 h8)`.
-/
theorem exists_multiple_not_mem :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M], (∀ (a : R) (m : M), a ≠ 0 → a • m = 0 → m = 0) → ∀ t : M, t ≠ 0 → ∀ d₀ : R, d₀ ≠ 0 → (∀ (x d : R) (u : M), d ≠ 0 → d • u = x • t → d ∣ d₀ * x) → ∀ (V : Set M) (P : Ideal R), P.IsMaximal → P ≠ ⊥ → (∀ u ∈ V, ∀ c e : R, e ≠ 0 → (∀ π ∈ P, e ∣ c * π) → ∃ u' : M, e • u' = c • u) → ∃ (x : R) (u : M), d₀ • u = x • t ∧ u ∉ V := by
  intro R _ _ _ M _ _ htf t _ d₀ hd₀ hb V P hP hP0 hV
  by_contra hcon
  push_neg at hcon
  let I : Ideal R :=
    { carrier := {x | ∃ u : M, d₀ • u = x • t}
      add_mem' := by
        rintro a b ⟨u, hu⟩ ⟨v, hv⟩
        exact ⟨u + v, by rw [smul_add, hu, hv, add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c x ⟨u, hu⟩
        refine ⟨c • u, ?_⟩
        rw [smul_comm, hu, smul_eq_mul, mul_smul] }
  have hImem : ∀ x, x ∈ I ↔ ∃ u : M, d₀ • u = x • t := fun x => Iff.rfl
  have hI0 : I ≠ ⊥ := by
    intro h
    have : d₀ ∈ I := (hImem _).2 ⟨t, rfl⟩
    rw [h] at this
    exact hd₀ (by simpa using this)
  obtain ⟨e, heP, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hle : Ideal.span {e} ≤ P := (Ideal.span_singleton_le_iff_mem P).2 heP
  obtain ⟨C, hC⟩ := Ideal.dvd_iff_le.2 hle
  have hcz : ∀ c ∈ C, ∀ z ∈ I, c * z ∈ Ideal.span {e} * I := by
    intro c hc z hz
    obtain ⟨u, hu⟩ := (hImem z).1 hz
    have huV : u ∈ V := hcon z u hu
    have hdiv : ∀ π ∈ P, e ∣ c * π := by
      intro π hπ
      have : π * c ∈ Ideal.span {e} := by
        rw [hC]
        exact Ideal.mul_mem_mul hπ hc
      rw [mul_comm]
      exact Ideal.mem_span_singleton.1 this
    obtain ⟨u', hu'⟩ := hV u huV c e he0 hdiv
    have h1 : (d₀ * e) • u' = (c * z) • t := by
      rw [mul_smul, hu', smul_comm, hu, mul_smul]
    have h2 : d₀ * e ∣ d₀ * (c * z) := hb (c * z) (d₀ * e) u' (mul_ne_zero hd₀ he0) h1
    obtain ⟨w, hw⟩ := (mul_dvd_mul_iff_left hd₀).1 h2
    have h3 : d₀ • u' = w • t := by
      have h4 : e • (d₀ • u' - w • t) = 0 := by
        rw [smul_sub, smul_comm, ← mul_smul e w, ← hw, ← h1, mul_smul, sub_self]
      exact sub_eq_zero.1 (htf e _ he0 h4)
    have hwI : w ∈ I := (hImem w).2 ⟨u', h3⟩
    rw [hw]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self e) hwI
  have hCI : C * I ≤ Ideal.span {e} * I := Ideal.mul_le.2 hcz
  have h5 : Ideal.span {e} * I ≤ Ideal.span {e} * (P * I) := by
    calc Ideal.span {e} * I = P * (C * I) := by rw [hC, mul_assoc]
      _ ≤ P * (Ideal.span {e} * I) := Ideal.mul_mono_right hCI
      _ = Ideal.span {e} * (P * I) := by ring
  have h6 : I ≤ P * I := (Ideal.span_singleton_mul_right_mono he0).1 h5
  have h8 : P * I = ⊤ * I := by
    rw [Ideal.top_mul]
    exact le_antisymm Ideal.mul_le_right h6
  exact hP.ne_top (mul_right_cancel₀ hI0 h8)

end GlobalTheory.CompanionTheory.Ggeo.KeydegPrimes
