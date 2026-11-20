import Mathlib
import Formalism.PeriodIntegrals.LatMin

namespace PI.LatMinWork

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Establish `h2 : ¬ (p : ℤ) ∣ 2`. Introduce `h`. Establish `h' : p ∣ 2` using `by exact_mod_cast h`. Conclude with `hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')`. Establish `h1 : ‖((2 : ℤ) : ℚ_[p])‖ ≤ 1` using `by first`.

Consider the case `exact Padic.norm_int_le_one 2`. Consider the case `exact padicNormE.norm_int_le_one 2`. Establish `h3 : ¬ ‖((2 : ℤ) : ℚ_[p])‖ < 1` using `fun h => h2 (by first`. Consider the case `exact Padic.norm_intCast_lt_one_iff.mp h`. Consider the case `exact (Padic.norm_int_lt_one_iff_dvd 2).1 h`.

Consider the case `exact (padicNormE.norm_int_lt_one_iff_dvd 2).1 h)`. Use `le_antisymm h1 (not_lt.1 h3)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
lemma norm_two_eq_one (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have h1 : ‖((2 : ℤ) : ℚ_[p])‖ ≤ 1 := by
    first
      | exact Padic.norm_int_le_one 2
      | exact padicNormE.norm_int_le_one 2
  have h3 : ¬ ‖((2 : ℤ) : ℚ_[p])‖ < 1 := fun h => h2 (by
    first
      | exact Padic.norm_intCast_lt_one_iff.mp h
      | exact (Padic.norm_int_lt_one_iff_dvd 2).1 h
      | exact (padicNormE.norm_int_lt_one_iff_dvd 2).1 h)
  have := le_antisymm h1 (not_lt.1 h3)
  exact_mod_cast this

variable {V : Type*} [AddCommGroup V] [Module ℤ_[p] V]

/- English proof (translation)
Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => exact hS x hx`. Consider the case `zero`. Establish `h0 : B 0 w = 0` using `by simpa using hsm 0 0 w`.

Rewrite using `[h0, norm_zero]`. Conclude with `hM`. Consider the case `add x y _ _ hx hy`. Rewrite using `[hadd]`. Apply the tactic sequence `exact (show ‖B x w + B y w‖ ≤ max ‖B x w‖ ‖B y w‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`.

Consider the case `smul c x _ hx`. Rewrite using `[hsm, norm_mul]`. Establish `hc : ‖(c : ℚ_[p])‖ ≤ 1` using `by first`. Consider the case `exact c.2`. Consider the case `simpa using PadicInt.norm_le_one c`.

Combine the equalities or inequalities in the displayed calculation.
-/
lemma bound_span (B : V → V → ℚ_[p])
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (S : Set V) (w : V) (M : ℝ) (hM : 0 ≤ M) (hS : ∀ b ∈ S, ‖B b w‖ ≤ M) :
    ∀ v ∈ Submodule.span ℤ_[p] S, ‖B v w‖ ≤ M := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    have h0 : B 0 w = 0 := by simpa using hsm 0 0 w
    rw [h0, norm_zero]; exact hM
  | add x y _ _ hx hy =>
    rw [hadd]
    exact (show ‖B x w + B y w‖ ≤ max ‖B x w‖ ‖B y w‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul c x _ hx =>
    rw [hsm, norm_mul]
    have hc : ‖(c : ℚ_[p])‖ ≤ 1 := by
      first
        | exact c.2
        | simpa using PadicInt.norm_le_one c
    calc ‖(c : ℚ_[p])‖ * ‖B x w‖ ≤ 1 * ‖B x w‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ M := by rw [one_mul]; exact hx

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Take `⟨u0, hu0, v0, hv0, hne0⟩` from `hne`. Establish `hSL : ∀ a ∈ S, a ∈ L` using `fun a ha => hS ▸ Submodule.subset_span ha`. Establish `hB0 : ∀ v, B 0 v = 0` using `fun v => by simpa using hsm 0 0 v`. Establish `hSn : S.Nonempty`.

Break down `S.eq_empty_or_nonempty with h | h` into its components or cases. Substitute `h` using the available equality. Rewrite `hS` using `[Finset.coe_empty, Submodule.span_empty]`. Rewrite `hu0` using `[← hS, Submodule.mem_bot]`. Substitute `hu0` using the available equality.

Conclude with `absurd (hB0 v0) hne0`. Conclude with `h`. Take `⟨q, hq, hqmax⟩` from `(S ×ˢ S).exists_max_image (fun q : V × V => ‖B q.1 q.2‖) (hSn.product hSn)`. Take `⟨a, b⟩` from `q`. Establish `ha : a ∈ S` using `(Finset.mem_product.1 hq).1`.

Establish `hb : b ∈ S` using `(Finset.mem_product.1 hq).2`. Establish `hmaxS : ∀ a' ∈ S, ∀ b' ∈ S, ‖B a' b'‖ ≤ ‖B a b‖` using `fun a' ha' b' hb' => hqmax (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)`. Establish `hM0 : 0 ≤ ‖B a b‖` using `norm_nonneg _`. Establish `h1 : ∀ b' ∈ S, ∀ u ∈ L, ‖B u b'‖ ≤ ‖B a b‖` using `fun b' hb' u hu => by`. Rewrite `hu` using `[← hS]`.

Conclude with `bound_span B hsm hadd (↑S) b' _ hM0 (fun a' ha' => hmaxS a' ha' b' hb') u hu`. Establish `hbound : ∀ u ∈ L, ∀ v ∈ L, ‖B u v‖ ≤ ‖B a b‖`. Introduce `u hu v hv`. Rewrite using `[hsym u hu v hv]`. Establish `h2 : ∀ b' ∈ (S : Set V), ‖B b' u‖ ≤ ‖B a b‖` using `fun b' hb' => by`.

Rewrite using `[hsym b' (hSL b' hb') u hu]`. Conclude with `h1 b' hb' u hu`. Rewrite `hv` using `[← hS]`. Conclude with `bound_span B hsm hadd (↑S) u _ hM0 h2 v hv`. Establish `hMpos : 0 < ‖B a b‖` using `lt_of_lt_of_le (norm_pos_iff.2 hne0) (hbound u0 hu0 v0 hv0)`.

Establish `haL` using `hSL a ha`. Establish `hbL` using `hSL b hb`. Establish `hx : ∃ x ∈ L, ‖B x x‖ = ‖B a b‖`. Distinguish the cases in `haa : ‖B a a‖ = ‖B a b‖`. Conclude with `⟨a, haL, haa⟩`.

Distinguish the cases in `hbb : ‖B b b‖ = ‖B a b‖`. Conclude with `⟨b, hbL, hbb⟩`. Establish `habL` using `L.add_mem haL hbL`. Use `⟨a + b, habL, ?_⟩` and prove the remaining obligations. Establish `e : B (a + b) (a + b) = 2 * B a b + (B a a + B b b)`.

Rewrite using `[hadd, hsym a haL _ habL, hsym b hbL _ habL, hadd, hadd, hsym b hbL a haL]`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `have hlt : ‖B a a + B b b‖ < ‖B a b‖ := lt_of_le_of_lt (show ‖B a a + B b b‖ ≤ max ‖B a a‖ ‖B b b‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _) (max_lt (lt_of_le_of_ne (hbound a haL a haL) haa) (lt_of_le_of_ne (hbound b hbL b hbL) hbb))`. Establish `h2ab : ‖2 * B a b‖ = ‖B a b‖` using `by rw [norm_mul, norm_two_eq_one hp2, one_mul]`. Rewrite using `[e, (show ‖2 * B a b + (B a a + B b b)‖ = max ‖2 * B a b‖ ‖B a a + B b b‖ by first`.

Consider the case `exact Padic.add_eq_max_of_ne (by rw [h2ab]; exact hlt.ne')`. Consider the case `exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2ab]; exact hlt.ne')), h2ab]`. Conclude with `max_eq_left hlt.le`. Take `⟨x, hxL, hxn⟩` from `hx`. Establish `hxx : B x x ≠ 0` using `fun h => by rw [h, norm_zero] at hxn; linarith`.

Use `⟨x, hxL, hxx, fun u hu => ?_⟩` and prove the remaining obligations. Establish `hc : ‖B u x / B x x‖ ≤ 1`. Rewrite using `[norm_div, hxn, div_le_one hMpos]`. Conclude with `hbound u hu x hxL`. Conclude with `⟨(⟨B u x / B x x, hc⟩ : {y : ℚ_[p] // ‖y‖ ≤ 1}), (div_mul_cancel₀ _ hxx).symm⟩`.
-/
theorem main (hp2 : p ≠ 2) (B : V → V → ℚ_[p]) (L : Submodule ℤ_[p] V) (hL : L.FG)
    (hsm : ∀ (c : ℤ_[p]) u v, B (c • u) v = (c : ℚ_[p]) * B u v)
    (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (hsym : ∀ u ∈ L, ∀ v ∈ L, B u v = B v u) (hne : ∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) :
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨u0, hu0, v0, hv0, hne0⟩ := hne
  have hSL : ∀ a ∈ S, a ∈ L := fun a ha => hS ▸ Submodule.subset_span ha
  have hB0 : ∀ v, B 0 v = 0 := fun v => by simpa using hsm 0 0 v
  have hSn : S.Nonempty := by
    rcases S.eq_empty_or_nonempty with h | h
    · subst h
      rw [Finset.coe_empty, Submodule.span_empty] at hS
      rw [← hS, Submodule.mem_bot] at hu0
      subst hu0
      exact absurd (hB0 v0) hne0
    · exact h
  obtain ⟨q, hq, hqmax⟩ := (S ×ˢ S).exists_max_image (fun q : V × V => ‖B q.1 q.2‖) (hSn.product hSn)
  obtain ⟨a, b⟩ := q
  have ha : a ∈ S := (Finset.mem_product.1 hq).1
  have hb : b ∈ S := (Finset.mem_product.1 hq).2
  have hmaxS : ∀ a' ∈ S, ∀ b' ∈ S, ‖B a' b'‖ ≤ ‖B a b‖ := fun a' ha' b' hb' =>
    hqmax (a', b') (Finset.mem_product.2 ⟨ha', hb'⟩)
  have hM0 : 0 ≤ ‖B a b‖ := norm_nonneg _
  have h1 : ∀ b' ∈ S, ∀ u ∈ L, ‖B u b'‖ ≤ ‖B a b‖ := fun b' hb' u hu => by
    rw [← hS] at hu
    exact bound_span B hsm hadd (↑S) b' _ hM0 (fun a' ha' => hmaxS a' ha' b' hb') u hu
  have hbound : ∀ u ∈ L, ∀ v ∈ L, ‖B u v‖ ≤ ‖B a b‖ := by
    intro u hu v hv
    rw [hsym u hu v hv]
    have h2 : ∀ b' ∈ (S : Set V), ‖B b' u‖ ≤ ‖B a b‖ := fun b' hb' => by
      rw [hsym b' (hSL b' hb') u hu]; exact h1 b' hb' u hu
    rw [← hS] at hv
    exact bound_span B hsm hadd (↑S) u _ hM0 h2 v hv
  have hMpos : 0 < ‖B a b‖ := lt_of_lt_of_le (norm_pos_iff.2 hne0) (hbound u0 hu0 v0 hv0)
  have haL := hSL a ha
  have hbL := hSL b hb
  have hx : ∃ x ∈ L, ‖B x x‖ = ‖B a b‖ := by
    by_cases haa : ‖B a a‖ = ‖B a b‖
    · exact ⟨a, haL, haa⟩
    by_cases hbb : ‖B b b‖ = ‖B a b‖
    · exact ⟨b, hbL, hbb⟩
    have habL := L.add_mem haL hbL
    refine ⟨a + b, habL, ?_⟩
    have e : B (a + b) (a + b) = 2 * B a b + (B a a + B b b) := by
      rw [hadd, hsym a haL _ habL, hsym b hbL _ habL, hadd, hadd, hsym b hbL a haL]; ring
    have hlt : ‖B a a + B b b‖ < ‖B a b‖ := lt_of_le_of_lt (show ‖B a a + B b b‖ ≤ max ‖B a a‖ ‖B b b‖ by first | exact Padic.nonarchimedean _ _ | exact IsUltrametricDist.norm_add_le_max _ _)
      (max_lt (lt_of_le_of_ne (hbound a haL a haL) haa) (lt_of_le_of_ne (hbound b hbL b hbL) hbb))
    have h2ab : ‖2 * B a b‖ = ‖B a b‖ := by rw [norm_mul, norm_two_eq_one hp2, one_mul]
    rw [e, (show ‖2 * B a b + (B a a + B b b)‖ = max ‖2 * B a b‖ ‖B a a + B b b‖ by
      first
        | exact Padic.add_eq_max_of_ne (by rw [h2ab]; exact hlt.ne')
        | exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2ab]; exact hlt.ne')), h2ab]
    exact max_eq_left hlt.le
  obtain ⟨x, hxL, hxn⟩ := hx
  have hxx : B x x ≠ 0 := fun h => by rw [h, norm_zero] at hxn; linarith
  refine ⟨x, hxL, hxx, fun u hu => ?_⟩
  have hc : ‖B u x / B x x‖ ≤ 1 := by
    rw [norm_div, hxn, div_le_one hMpos]; exact hbound u hu x hxL
  exact ⟨(⟨B u x / B x x, hc⟩ : {y : ℚ_[p] // ‖y‖ ≤ 1}), (div_mul_cancel₀ _ hxx).symm⟩

end PI.LatMinWork

namespace PI

end PI
