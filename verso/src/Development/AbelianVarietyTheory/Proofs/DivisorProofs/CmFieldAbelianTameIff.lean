import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt

set_option autoImplicit false

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.HostModel

namespace GlobalTheory.HostRamif

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hn`. Assume the negation of the conclusion as `hnd`. Establish `hc : IsCoprime (l : ℤ) n` using `((Nat.prime_iff_prime_int.mp hl).irreducible.coprime_iff_not_dvd).2 hnd`. Take `⟨a, b, hab⟩` from `hc`.

Apply `hw.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : (1 : 𝓞 E) = (a : 𝓞 E) * (l : 𝓞 E) + (b : 𝓞 E) * (n : 𝓞 E)`. Use `congrArg (Int.cast : ℤ → 𝓞 E) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this.symm`. Rewrite using `[h1]`. Conclude with `add_mem (w.mul_mem_left _ hlw) (w.mul_mem_left _ hn)`. Introduce and unpack `⟨c, rfl⟩`. Use `push_cast`.

Conclude with `w.mul_mem_right _ hlw`.
-/
theorem intCast_mem_iff {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal) (hlw : (l : 𝓞 E) ∈ w) (n : ℤ) :
    (n : 𝓞 E) ∈ w ↔ (l : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hc : IsCoprime (l : ℤ) n := ((Nat.prime_iff_prime_int.mp hl).irreducible.coprime_iff_not_dvd).2 hnd
    obtain ⟨a, b, hab⟩ := hc
    apply hw.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : 𝓞 E) = (a : 𝓞 E) * (l : 𝓞 E) + (b : 𝓞 E) * (n : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [h1]
    exact add_mem (w.mul_mem_left _ hlw) (w.mul_mem_left _ hn)
  · rintro ⟨c, rfl⟩
    push_cast
    exact w.mul_mem_right _ hlw

/- English proof (translation)
Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `hwp` using `hw.isPrime`. Use `haveI : w.LiesOver (Ideal.span {(l : ℤ)}) := (Ideal.liesOver_span_iff hw.ne_top hp).mpr (by simpa using hlw)`. Rewrite using `[← not_iff_not, not_dvd_differentIdeal_iff, not_dvd_discr_iff_forall_liesOver E (𝓞 E) hp]`. Use `⟨fun h P hP hPl => ?_, fun h => h w hw inferInstance⟩` and prove the remaining obligations.

Establish `hPp` using `hP.isPrime`. Rewrite `h`, the goal using `[← Ideal.ramificationIdx_eq_one_iff]`. Rewrite using `[← h]`. Conclude with `Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) _ _ (E ≃ₐ[ℚ] E)`.
-/
theorem dvd_different_iff [IsGalois ℚ E] {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) : w ∣ differentIdeal ℤ (𝓞 E) ↔ (l : ℤ) ∣ discr E := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have hwp := hw.isPrime
  haveI : w.LiesOver (Ideal.span {(l : ℤ)}) := (Ideal.liesOver_span_iff hw.ne_top hp).mpr (by simpa using hlw)
  rw [← not_iff_not, not_dvd_differentIdeal_iff, not_dvd_discr_iff_forall_liesOver E (𝓞 E) hp]
  refine ⟨fun h P hP hPl => ?_, fun h => h w hw inferInstance⟩
  have hPp := hP.isPrime
  rw [← Ideal.ramificationIdx_eq_one_iff] at h ⊢
  rw [← h]
  exact Ideal.ramificationIdx_eq_of_isGaloisGroup (Ideal.span {(l : ℤ)}) _ _ (E ≃ₐ[ℚ] E)

variable [IsCMField E]

/- English proof (translation)
Take `⟨k, hk⟩ : ∃ k : ℕ, H.d = 4 * k + 3` from `⟨H.d / 4, by have := H.d_mod; omega⟩`. Establish `hsq : H.w0 ^ 2 = H.w0 - (k + 1)`. Establish `h` using `H.rt_sq`. Rewrite `h` using `[rt_eq, hk]`. Move the coercions through the operations in `at h`.

Apply `mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)` to reduce the goal to its premises. Take the linear combination `h`. Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩`. Consider the case `algebraMap r => exact ⟨r, 0, by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨x, y, rfl⟩` from `ha`. Take `⟨x', y', rfl⟩` from `hb`. Conclude with `⟨x + x', y + y', by push_cast; ring⟩`. Consider the case `mul a b _ _ ha hb`.

Take `⟨x, y, rfl⟩` from `ha`. Take `⟨x', y', rfl⟩` from `hb`. Conclude with `⟨x * x' - y * y' * (k + 1), x * y' + y * x' + y * y', by push_cast; linear_combination (y : 𝓞 E) * y' * hsq⟩`.
-/
theorem exists_coords (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ x y : ℤ, a = x + y * H.w0 := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 4 * k + 3 := ⟨H.d / 4, by have := H.d_mod; omega⟩
  have hsq : H.w0 ^ 2 = H.w0 - (k + 1) := by
    have h := H.rt_sq
    rw [rt_eq, hk] at h
    push_cast at h
    apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
    linear_combination h
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact ⟨0, 1, by rw [Set.mem_singleton_iff.mp hx]; simp⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, y, rfl⟩ := ha
    obtain ⟨x', y', rfl⟩ := hb
    exact ⟨x + x', y + y', by push_cast; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨x, y, rfl⟩ := ha
    obtain ⟨x', y', rfl⟩ := hb
    exact ⟨x * x' - y * y' * (k + 1), x * y' + y * x' + y * y', by
      push_cast; linear_combination (y : 𝓞 E) * y' * hsq⟩

/- English proof (translation)
Establish `hwp` using `hw.isPrime`. Use `haveI := Fact.mk hl`. Establish `h1 : (1 : 𝓞 E) ∉ w` using `fun h => hw.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hw0 : H.w0 ∈ Algebra.adjoin ℤ {H.w0}` using `Algebra.self_mem_adjoin_singleton ℤ _`. Distinguish the cases in `h2 : l = 2`.

Substitute `h2` using the available equality. Use `⟨fun _ => ?_, fun _ => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩ : ∃ k : ℕ, H.d = 8 * k + 7` from `⟨H.d / 8, by have := H.d_mod; omega⟩`. Establish `hsq : H.w0 * (1 - H.w0) = (k + 1) * ((2 : ℕ) : 𝓞 E)`. Establish `h` using `H.rt_sq`.

Rewrite `h` using `[rt_eq, hk]`. Move the coercions through the operations in `at h ⊢`. Apply `mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)` to reduce the goal to its premises. Take the linear combination `-h`. Establish `hm : H.w0 * (1 - H.w0) ∈ w` using `hsq ▸ w.mul_mem_left _ hlw`.

Break down `hwp.mem_or_mem hm with h | h` into its components or cases. Use `⟨_, hw0, h, fun h' => h1 ?_⟩` and prove the remaining obligations. Rewrite `h'` using `[cmHost_bar_halfIntegerGenerator]`. Simplify using `using add_mem h h'`. Use `⟨_, sub_mem (one_mem _) hw0, h, fun h' => h1 ?_⟩` and prove the remaining obligations.

Rewrite `h'` using `[map_sub, map_one, cmHost_bar_halfIntegerGenerator]`. Simplify using `using add_mem h h'`. Generalize the expression as in `(-(H.d : ZMod 2)) = z revert z`. Evaluate the decidable proposition. Establish `hl2 : ¬ (l : ℤ) ∣ 2` using `fun h => h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by exact_mod_cast h))`.

Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs⟩`. Take `⟨s, rfl⟩` from `ZMod.intCast_surjective s`. Establish `hdv : (l : ℤ) ∣ -(H.d : ℤ) - s * s`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Rewrite using `[hs, sub_self]`. Establish `hm : (H.rt - s) * (-H.rt - s) ∈ w`. Use `(intCast_mem_iff hl hw hlw _).2 hdv` as an intermediate fact.

Establish `e : (H.rt - s) * (-H.rt - s) = -((-(H.d : ℤ) - s * s : ℤ) : 𝓞 E)`. Use `push_cast`. Take the linear combination `-H.rt_sq`. Rewrite using `[e]`. Conclude with `neg_mem this`.

Establish `hnb : ¬ (H.rt - s ∈ w ∧ -H.rt - s ∈ w)`. Introduce and unpack `⟨ha, hb⟩`. Establish `: ((2 * s : ℤ) : 𝓞 E) ∈ w`. Establish `e : ((2 * s : ℤ) : 𝓞 E) = -((H.rt - s) + (-H.rt - s))` using `by push_cast; ring`. Rewrite using `[e]`.

Conclude with `neg_mem (add_mem ha hb)`. Establish `hs'` using `(hp.dvd_or_dvd ((intCast_mem_iff hl hw hlw _).1 this)).resolve_left hl2`. Establish `: (l : ℤ) ∣ (H.d : ℤ)`. Use `dvd_add hdv (hs'.mul_right s)` as an intermediate fact. Simplify using `using this`.

Conclude with `hd ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 (by exact_mod_cast this))`. Break down `hwp.mem_or_mem hm with h | h` into its components or cases. Use `⟨_, sub_mem (rt_mem_adjoin H) (intCast_mem _ s), h, fun h' => hnb ⟨h, ?_⟩⟩` and prove the remaining obligations. Rewrite `h'` using `[map_sub, bar_rt, map_intCast]`. Then use the resulting hypothesis. Use `⟨_, sub_mem (neg_mem (rt_mem_adjoin H)) (intCast_mem _ s), h, fun h' => hnb ⟨?_, h⟩⟩` and prove the remaining obligations.

Rewrite `h'` using `[map_sub, map_neg, bar_rt, neg_neg, map_intCast]`. Then use the resulting hypothesis. Introduce and unpack `⟨a, ha, haw, hbw⟩`. Take `⟨x, y, rfl⟩` from `exists_coords H ha`. Establish `hb : H.bar (x + y * H.w0) = x + y * (1 - H.w0)`. Rewrite using `[map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]`.

Rewrite `hbw` using `[hb]`. Establish `hy : ¬ (l : ℤ) ∣ y`. Introduce `hy`. Apply `hbw` to reduce the goal to its premises. Establish `hyw` using `(intCast_mem_iff hl hw hlw _).2 hy`.

Establish `e : (x : 𝓞 E) + y * (1 - H.w0) = (x + y * H.w0) + y * (1 - 2 * H.w0)` using `by ring`. Rewrite using `[e]`. Conclude with `add_mem haw (w.mul_mem_right _ hyw)`. Establish `hn : (l : ℤ) ∣ (2 * x + y) ^ 2 + H.d * y ^ 2`. Rewrite using `[← intCast_mem_iff hl hw hlw]`.

Establish `e : (((2 * x + y) ^ 2 + H.d * y ^ 2 : ℤ) : 𝓞 E) = (x + y * H.w0) * (4 * (x + y * (1 - H.w0)))`. Establish `h` using `H.rt_sq`. Rewrite `h` using `[rt_eq]`. Use `push_cast`. Take the linear combination `(y : 𝓞 E) ^ 2 * h`.

Rewrite using `[e]`. Conclude with `w.mul_mem_right _ haw`. Rewrite `hn`, `hy` using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Move the coercions through the operations in `at hn`. Use `⟨(2 * x + y) / y, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-hn`.
-/
theorem isSquare_iff (H : Host E) {l : ℕ} (hl : l.Prime) {w : Ideal (𝓞 E)} (hw : w.IsMaximal)
    (hlw : (l : 𝓞 E) ∈ w) (hd : l ≠ H.d) :
    IsSquare (-(H.d : ZMod l)) ↔ ∃ a ∈ Algebra.adjoin ℤ {H.w0}, a ∈ w ∧ H.bar a ∉ w := by
  have hwp := hw.isPrime
  haveI := Fact.mk hl
  have h1 : (1 : 𝓞 E) ∉ w := fun h => hw.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hw0 : H.w0 ∈ Algebra.adjoin ℤ {H.w0} := Algebra.self_mem_adjoin_singleton ℤ _
  by_cases h2 : l = 2
  · subst h2
    refine ⟨fun _ => ?_, fun _ => ?_⟩
    · obtain ⟨k, hk⟩ : ∃ k : ℕ, H.d = 8 * k + 7 := ⟨H.d / 8, by have := H.d_mod; omega⟩
      have hsq : H.w0 * (1 - H.w0) = (k + 1) * ((2 : ℕ) : 𝓞 E) := by
        have h := H.rt_sq
        rw [rt_eq, hk] at h
        push_cast at h ⊢
        apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
        linear_combination -h
      have hm : H.w0 * (1 - H.w0) ∈ w := hsq ▸ w.mul_mem_left _ hlw
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, hw0, h, fun h' => h1 ?_⟩
        rw [cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
      · refine ⟨_, sub_mem (one_mem _) hw0, h, fun h' => h1 ?_⟩
        rw [map_sub, map_one, cmHost_bar_halfIntegerGenerator] at h'
        simpa using add_mem h h'
    · generalize (-(H.d : ZMod 2)) = z
      revert z
      decide
  · have hl2 : ¬ (l : ℤ) ∣ 2 := fun h => h2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).1 (by exact_mod_cast h))
    have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
    constructor
    · rintro ⟨s, hs⟩
      obtain ⟨s, rfl⟩ := ZMod.intCast_surjective s
      have hdv : (l : ℤ) ∣ -(H.d : ℤ) - s * s := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        push_cast
        rw [hs, sub_self]
      have hm : (H.rt - s) * (-H.rt - s) ∈ w := by
        have := (intCast_mem_iff hl hw hlw _).2 hdv
        have e : (H.rt - s) * (-H.rt - s) = -((-(H.d : ℤ) - s * s : ℤ) : 𝓞 E) := by
          push_cast
          linear_combination -H.rt_sq
        rw [e]
        exact neg_mem this
      have hnb : ¬ (H.rt - s ∈ w ∧ -H.rt - s ∈ w) := by
        rintro ⟨ha, hb⟩
        have : ((2 * s : ℤ) : 𝓞 E) ∈ w := by
          have e : ((2 * s : ℤ) : 𝓞 E) = -((H.rt - s) + (-H.rt - s)) := by push_cast; ring
          rw [e]
          exact neg_mem (add_mem ha hb)
        have hs' := (hp.dvd_or_dvd ((intCast_mem_iff hl hw hlw _).1 this)).resolve_left hl2
        have : (l : ℤ) ∣ (H.d : ℤ) := by
          have := dvd_add hdv (hs'.mul_right s)
          simpa using this
        exact hd ((Nat.prime_dvd_prime_iff_eq hl H.d_prime).1 (by exact_mod_cast this))
      rcases hwp.mem_or_mem hm with h | h
      · refine ⟨_, sub_mem (rt_mem_adjoin H) (intCast_mem _ s), h, fun h' => hnb ⟨h, ?_⟩⟩
        rwa [map_sub, bar_rt, map_intCast] at h'
      · refine ⟨_, sub_mem (neg_mem (rt_mem_adjoin H)) (intCast_mem _ s), h, fun h' => hnb ⟨?_, h⟩⟩
        rwa [map_sub, map_neg, bar_rt, neg_neg, map_intCast] at h'
    · rintro ⟨a, ha, haw, hbw⟩
      obtain ⟨x, y, rfl⟩ := exists_coords H ha
      have hb : H.bar (x + y * H.w0) = x + y * (1 - H.w0) := by
        rw [map_add, map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
      rw [hb] at hbw
      have hy : ¬ (l : ℤ) ∣ y := by
        intro hy
        apply hbw
        have hyw := (intCast_mem_iff hl hw hlw _).2 hy
        have e : (x : 𝓞 E) + y * (1 - H.w0) = (x + y * H.w0) + y * (1 - 2 * H.w0) := by ring
        rw [e]
        exact add_mem haw (w.mul_mem_right _ hyw)
      have hn : (l : ℤ) ∣ (2 * x + y) ^ 2 + H.d * y ^ 2 := by
        rw [← intCast_mem_iff hl hw hlw]
        have e : (((2 * x + y) ^ 2 + H.d * y ^ 2 : ℤ) : 𝓞 E) =
            (x + y * H.w0) * (4 * (x + y * (1 - H.w0))) := by
          have h := H.rt_sq
          rw [rt_eq] at h
          push_cast
          linear_combination (y : 𝓞 E) ^ 2 * h
        rw [e]
        exact w.mul_mem_right _ haw
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hn hy
      push_cast at hn
      refine ⟨(2 * x + y) / y, ?_⟩
      field_simp
      linear_combination -hn

/- English proof (translation)
Introduce `E _ _ _ H`. Unfold `EigenvectorLieDegree.IsHostField AdelicDegreeTameRamification.TameAtRamified`. Use `and_congr_right fun hab => ⟨fun h l w hl hld hw hlw => ?_, fun h w hwd => ?_⟩` and prove the remaining obligations. Establish `hne : w ≠ ⊥`. Introduce and unpack `rfl`.

Conclude with `hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hlw))`. Take `⟨h1, h2⟩` from `h ⟨w, hw.isPrime, hne⟩ ((dvd_different_iff hl hw hlw).2 hld)`. Use `⟨h1, fun hd => ?_, fun hd => ?_⟩` and prove the remaining obligations. Break down `h2 l hl hlw with h3 | h3` into its components or cases. Conclude with `(isSquare_iff H hl hw hlw hd).1 h3.2`.

Conclude with `absurd h3.1 hd`. Break down `h2 l hl hlw with h3 | h3` into its components or cases. Conclude with `absurd hd h3.1`. Conclude with `fun h4 => h3.2 (Ideal.dvd_span_singleton.2 h4)`. Establish `hw` using `w.isMaximal`.

Use `⟨?_, fun l hl hlw => ?_⟩` and prove the remaining obligations. Take `⟨l, hl, hlw⟩ : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ w.asIdeal` from `by haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `letI := Ideal.Quotient.field w.asIdeal`. Use `⟨ringChar (𝓞 E ⧸ w.asIdeal), CharP.char_is_prime (𝓞 E ⧸ w.asIdeal) _, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`.

Conclude with `ringChar.Nat.cast_ringChar`. Conclude with `(h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw).1`. Take `⟨-, h2, h3⟩` from `h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw`. Distinguish the cases in `hd : l = H.d`. Conclude with `Or.inr ⟨hd, fun h4 => h3 hd (Ideal.dvd_span_singleton.1 h4)⟩`.

Conclude with `Or.inl ⟨hd, (isSquare_iff H hl hw hlw hd).2 (h2 hd)⟩`.
-/
theorem isHostField_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
    EigenvectorLieDegree.IsHostField H ↔ IsAbelianGalois ℚ E ∧ AdelicDegreeTameRamification.TameAtRamified H := by
  intro E _ _ _ H
  unfold EigenvectorLieDegree.IsHostField AdelicDegreeTameRamification.TameAtRamified
  refine and_congr_right fun hab => ⟨fun h l w hl hld hw hlw => ?_, fun h w hwd => ?_⟩
  · have hne : w ≠ ⊥ := by
      rintro rfl
      exact hl.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp hlw))
    obtain ⟨h1, h2⟩ := h ⟨w, hw.isPrime, hne⟩ ((dvd_different_iff hl hw hlw).2 hld)
    refine ⟨h1, fun hd => ?_, fun hd => ?_⟩
    · rcases h2 l hl hlw with h3 | h3
      · exact (isSquare_iff H hl hw hlw hd).1 h3.2
      · exact absurd h3.1 hd
    · rcases h2 l hl hlw with h3 | h3
      · exact absurd hd h3.1
      · exact fun h4 => h3.2 (Ideal.dvd_span_singleton.2 h4)
  · have hw := w.isMaximal
    refine ⟨?_, fun l hl hlw => ?_⟩
    · obtain ⟨l, hl, hlw⟩ : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ w.asIdeal := by
        haveI : Finite (𝓞 E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
        letI := Ideal.Quotient.field w.asIdeal
        refine ⟨ringChar (𝓞 E ⧸ w.asIdeal), CharP.char_is_prime (𝓞 E ⧸ w.asIdeal) _, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
        exact ringChar.Nat.cast_ringChar
      exact (h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw).1
    · obtain ⟨-, h2, h3⟩ := h l _ hl ((dvd_different_iff hl hw hlw).1 hwd) hw hlw
      by_cases hd : l = H.d
      · exact Or.inr ⟨hd, fun h4 => h3 hd (Ideal.dvd_span_singleton.1 h4)⟩
      · exact Or.inl ⟨hd, (isSquare_iff H hl hw hlw hd).2 (h2 hd)⟩

end GlobalTheory.HostRamif
