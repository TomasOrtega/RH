import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro s _ hs`. Simplify using `at hs`. Consider the case `succ N ih`.

Introduce `s hs hsN`. Distinguish the cases in `hm : s ∈ IsLocalRing.maximalIdeal V`. Take `⟨t, htS, rfl⟩` from `hdiv s hs hm`. Establish `htN : t ∉ (IsLocalRing.maximalIdeal V) ^ N`. Introduce `ht`.

Apply `hsN` to reduce the goal to its premises. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul hπm ht`. Take `⟨k, u, huS, hum, rfl⟩` from `ih t htS htN`. Conclude with `⟨k + 1, u, huS, hum, by ring⟩`.

Conclude with `⟨0, s, hs, hm, by simp⟩`.
-/
theorem dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t) :
    ∀ N : ℕ, ∀ s ∈ S, s ∉ (IsLocalRing.maximalIdeal V) ^ N →
      ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  intro N
  induction N with
  | zero => intro s _ hs; simp at hs
  | succ N ih =>
    intro s hs hsN
    by_cases hm : s ∈ IsLocalRing.maximalIdeal V
    · obtain ⟨t, htS, rfl⟩ := hdiv s hs hm
      have htN : t ∉ (IsLocalRing.maximalIdeal V) ^ N := by
        intro ht
        apply hsN
        rw [pow_succ']
        exact Ideal.mul_mem_mul hπm ht
      obtain ⟨k, u, huS, hum, rfl⟩ := ih t htS htN
      exact ⟨k + 1, u, huS, hum, by ring⟩
    · exact ⟨0, s, hs, hm, by simp⟩

/- English proof (translation)
Establish `hinf` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top`. Establish `: ∃ N : ℕ, s ∉ (maximalIdeal V) ^ N`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `: s ∈ ⨅ i : ℕ, (maximalIdeal V) ^ i` using `Ideal.mem_iInf.2 hc`.

Rewrite `this` using `[hinf, Ideal.mem_bot]`. Conclude with `h0 this`. Take `⟨N, hN⟩` from `this`. Conclude with `dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow S π hπm hdiv N s hs hN`.
-/
theorem dvrSubring_factor {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (s : V) (hs : s ∈ S) (h0 : s ≠ 0) :
    ∃ k : ℕ, ∃ u ∈ S, u ∉ IsLocalRing.maximalIdeal V ∧ s = π ^ k * u := by
  have hinf := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V)
    (maximalIdeal.isMaximal V).ne_top
  have : ∃ N : ℕ, s ∉ (maximalIdeal V) ^ N := by
    by_contra hc
    push_neg at hc
    have : s ∈ ⨅ i : ℕ, (maximalIdeal V) ^ i := Ideal.mem_iInf.2 hc
    rw [hinf, Ideal.mem_bot] at this
    exact h0 this
  obtain ⟨N, hN⟩ := this
  exact dvrSubring_eq_pow_mul_nonmem_of_not_mem_pow S π hπm hdiv N s hs hN

/- English proof (translation)
Use `eq_top_iff.2 fun v _ => ?_` and prove the remaining obligations. Take `⟨a, haS, b, hbS, hb0, hvb⟩` from `hfrac v`. Distinguish the cases in `ha0 : a = 0`. Substitute `ha0` using the available equality. Establish `: v = 0` using `(mul_eq_zero.1 hvb).resolve_right hb0`.

Rewrite using `[this]`. Conclude with `S.zero_mem`. Take `⟨k, u, huS, hum, rfl⟩` from `dvrSubring_factor S π hπm hdiv a haS ha0`. Take `⟨l, u', hu'S, hu'm, rfl⟩` from `dvrSubring_factor S π hπm hdiv b hbS hb0`. Take `⟨t', ht'S, ht'⟩` from `hinv u' hu'S hu'm`.

Establish `hπl : π ^ l ≠ 0` using `pow_ne_zero _ hπ0`. Distinguish the cases in `hkl : l ≤ k`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hkl`. Establish `h1 : v * u' = π ^ d * u`. Apply `mul_left_cancel₀ hπl` to reduce the goal to its premises.

Rewrite `hvb` using `[pow_add]`. Take the linear combination `hvb`. Establish `h2 : v = π ^ d * u * t'`. Take the linear combination `t' * h1 - v * ht'`. Rewrite using `[h2]`.

Conclude with `S.mul_mem (S.mul_mem (S.pow_mem hπS _) huS) ht'S`. Use `push_neg at hkl`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_lt hkl`. Substitute `hd` using the available equality. Establish `hπk : π ^ k ≠ 0` using `pow_ne_zero _ hπ0`.

Establish `h1 : v * π ^ (d + 1) * u' = u`. Apply `mul_left_cancel₀ hπk` to reduce the goal to its premises. Rewrite `hvb` using `[show k + d + 1 = k + (d + 1) by ring, pow_add]`. Take the linear combination `hvb`. Apply `absurd _ hum` to reduce the goal to its premises.

Rewrite using `[← h1, pow_succ]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hπm))`.
-/
theorem dvrSubring_eq_top (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (S : Subring V) (π : V) (hπS : π ∈ S) (hπ0 : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal V)
    (hinv : ∀ s ∈ S, s ∉ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s * t = 1)
    (hdiv : ∀ s ∈ S, s ∈ IsLocalRing.maximalIdeal V → ∃ t ∈ S, s = π * t)
    (hfrac : ∀ v : V, ∃ a ∈ S, ∃ b ∈ S, b ≠ 0 ∧ v * b = a) : S = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  obtain ⟨a, haS, b, hbS, hb0, hvb⟩ := hfrac v
  by_cases ha0 : a = 0
  · subst ha0
    have : v = 0 := (mul_eq_zero.1 hvb).resolve_right hb0
    rw [this]; exact S.zero_mem
  obtain ⟨k, u, huS, hum, rfl⟩ := dvrSubring_factor S π hπm hdiv a haS ha0
  obtain ⟨l, u', hu'S, hu'm, rfl⟩ := dvrSubring_factor S π hπm hdiv b hbS hb0
  obtain ⟨t', ht'S, ht'⟩ := hinv u' hu'S hu'm
  have hπl : π ^ l ≠ 0 := pow_ne_zero _ hπ0
  by_cases hkl : l ≤ k
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
    have h1 : v * u' = π ^ d * u := by
      apply mul_left_cancel₀ hπl
      rw [pow_add] at hvb
      linear_combination hvb
    have h2 : v = π ^ d * u * t' := by
      linear_combination t' * h1 - v * ht'
    rw [h2]
    exact S.mul_mem (S.mul_mem (S.pow_mem hπS _) huS) ht'S
  · push_neg at hkl
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt hkl
    subst hd
    have hπk : π ^ k ≠ 0 := pow_ne_zero _ hπ0
    have h1 : v * π ^ (d + 1) * u' = u := by
      apply mul_left_cancel₀ hπk
      rw [show k + d + 1 = k + (d + 1) by ring, pow_add] at hvb
      linear_combination hvb
    apply absurd _ hum
    rw [← h1, pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hπm))

end GlobalTheory
