import Mathlib
open scoped NumberField

namespace GlobalTheory.IdealPrincipalCoprime

/- English proof (translation)
Introduce `h`. Establish `h1` using `h.map (Algebra.norm ℤ (S := 𝓞 F))`. Rewrite `h1` using `[← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`. Conclude with `hp.ne_one h1`.
-/
theorem natCast_prime_not_isUnit (F : Type) [Field F] [NumberField F] {p : ℕ} (hp : p.Prime) :
    ¬ IsUnit (p : 𝓞 F) := by
  intro h
  have h1 := h.map (Algebra.norm ℤ (S := 𝓞 F))
  rw [← map_natCast (algebraMap ℤ (𝓞 F)), Algebra.norm_algebraMap,
    isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
  exact hp.ne_one h1

/- English proof (translation)
Introduce `F _ _ p hp w hw`. Use `set N : Ideal (𝓞 F) := Ideal.span {(p : 𝓞 F)} * w with hN`. Establish `hp0 : (p : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hN0 : N ≠ ⊥`. Rewrite using `[hN, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]`.

Conclude with `⟨hp0, hw⟩`. Take `⟨g, hg⟩` from `IsDedekindDomain.exists_sup_span_eq (I := w * N) (J := w) Ideal.mul_le_left (mul_ne_zero hw hN0)`. Establish `hgw : Ideal.span {g} ≤ w` using `hg ▸ le_sup_right`. Take `⟨𝔟, h𝔟⟩` from `Ideal.dvd_iff_le.mpr hgw`. Establish `hsup : N ⊔ 𝔟 = ⊤`.

Apply `mul_left_cancel₀ (show w ≠ 0 from hw)` to reduce the goal to its premises. Rewrite using `[Ideal.mul_sup, ← h𝔟, hg, Ideal.mul_top]`. Establish `hNp : N ≤ Ideal.span {(p : 𝓞 F)}` using `Ideal.mul_le_left`. Establish `hNw : N ≤ w` using `Ideal.mul_le_right`. Establish `hbp : 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤`.

Establish `h : N ⊔ 𝔟 ≤ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)}` using `sup_le (le_sup_of_le_right hNp) le_sup_left`. Rewrite `h` using `[hsup]`. Conclude with `eq_top_iff.mpr h`. Establish `hwb : w ⊔ 𝔟 = ⊤`. Establish `h : N ⊔ 𝔟 ≤ w ⊔ 𝔟` using `sup_le (le_sup_of_le_left hNw) le_sup_right`.

Rewrite `h` using `[hsup]`. Conclude with `eq_top_iff.mpr h`. Establish `h1 : (1 : 𝓞 F) ∈ w ⊔ 𝔟` using `by rw [hwb]; exact Submodule.mem_top`. Take `⟨e, he, f, hf, hef⟩` from `Submodule.mem_sup.mp h1`. Use `⟨g, e, 𝔟, ?_, he, ?_, h𝔟.symm, hbp⟩` and prove the remaining obligations.

Introduce `hg0`. Establish `hb0 : 𝔟 = ⊥`. Establish `: w * 𝔟 = ⊥` using `by rw [← h𝔟, hg0, Ideal.span_singleton_eq_bot.mpr rfl]`. Break down `Ideal.mul_eq_bot.mp this with h | h` into its components or cases. Conclude with `absurd h hw`.

Conclude with `h`. Rewrite `hbp` using `[hb0, bot_sup_eq]`. Conclude with `natCast_prime_not_isUnit F hp (Ideal.span_singleton_eq_top.mp hbp)`. Rewrite using `[← hef, add_sub_cancel_left]`. Conclude with `hf`.
-/
theorem exists_mul_eq_span_coprime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ), p.Prime →
    ∀ (w : Ideal (𝓞 F)), w ≠ ⊥ → ∃ (g e : 𝓞 F) (𝔟 : Ideal (𝓞 F)), g ≠ 0 ∧ e ∈ w ∧ 1 - e ∈ 𝔟 ∧
      w * 𝔟 = Ideal.span {g} ∧ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
  intro F _ _ p hp w hw
  set N : Ideal (𝓞 F) := Ideal.span {(p : 𝓞 F)} * w with hN
  have hp0 : (p : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hN0 : N ≠ ⊥ := by
    rw [hN, Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hp0, hw⟩
  obtain ⟨g, hg⟩ := IsDedekindDomain.exists_sup_span_eq (I := w * N) (J := w) Ideal.mul_le_left
    (mul_ne_zero hw hN0)
  have hgw : Ideal.span {g} ≤ w := hg ▸ le_sup_right
  obtain ⟨𝔟, h𝔟⟩ := Ideal.dvd_iff_le.mpr hgw
  have hsup : N ⊔ 𝔟 = ⊤ := by
    apply mul_left_cancel₀ (show w ≠ 0 from hw)
    rw [Ideal.mul_sup, ← h𝔟, hg, Ideal.mul_top]
  have hNp : N ≤ Ideal.span {(p : 𝓞 F)} := Ideal.mul_le_left
  have hNw : N ≤ w := Ideal.mul_le_right
  have hbp : 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} = ⊤ := by
    have h : N ⊔ 𝔟 ≤ 𝔟 ⊔ Ideal.span {(p : 𝓞 F)} := sup_le (le_sup_of_le_right hNp) le_sup_left
    rw [hsup] at h; exact eq_top_iff.mpr h
  have hwb : w ⊔ 𝔟 = ⊤ := by
    have h : N ⊔ 𝔟 ≤ w ⊔ 𝔟 := sup_le (le_sup_of_le_left hNw) le_sup_right
    rw [hsup] at h; exact eq_top_iff.mpr h
  have h1 : (1 : 𝓞 F) ∈ w ⊔ 𝔟 := by rw [hwb]; exact Submodule.mem_top
  obtain ⟨e, he, f, hf, hef⟩ := Submodule.mem_sup.mp h1
  refine ⟨g, e, 𝔟, ?_, he, ?_, h𝔟.symm, hbp⟩
  · intro hg0
    have hb0 : 𝔟 = ⊥ := by
      have : w * 𝔟 = ⊥ := by rw [← h𝔟, hg0, Ideal.span_singleton_eq_bot.mpr rfl]
      rcases Ideal.mul_eq_bot.mp this with h | h
      · exact absurd h hw
      · exact h
    rw [hb0, bot_sup_eq] at hbp
    exact natCast_prime_not_isUnit F hp (Ideal.span_singleton_eq_top.mp hbp)
  · rw [← hef, add_sub_cancel_left]; exact hf

end GlobalTheory.IdealPrincipalCoprime
