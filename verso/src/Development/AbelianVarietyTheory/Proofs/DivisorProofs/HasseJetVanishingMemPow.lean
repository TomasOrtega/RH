import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapQuotBijective
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Take `⟨π, hπ⟩` from `hπ`. Establish `hN0 : 0 < N` using `by omega`. Establish `hN1 : 1 < N` using `by omega`. Establish `hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w`. Introduce `u w`.

Use `hL 0 hN0 u w` as an intermediate fact. Simplify using `using this`. Set `φ : A →+* k` to `{ toFun := Δ 0 map_one' := h01 map_mul' := hmul0 map_zero' := map_zero _ map_add' := map_add _ }`. Establish `hφ : ∀ u, φ u = Δ 0 u` using `fun _ => rfl`. Establish `halg : ∀ l c, Δ l (algebraMap k A c) = c * Δ l 1`.

Introduce `l c`. Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]`. Establish `hsurj : Function.Surjective φ`. Introduce `c`. Use `⟨algebraMap k A c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hφ, halg, h01, mul_one]`. Use `set Q : Ideal A := RingHom.ker φ with hQdef`. Establish `hQmax : Q.IsMaximal` using `RingHom.ker_isMaximal_of_surjective φ hsurj`. Establish `hQmem : ∀ u, u ∈ Q ↔ Δ 0 u = 0` using `fun u => RingHom.mem_ker`. Establish `h11 : Δ 1 (1 : A) = 0`.

Use `hL 1 hN1 1 1` as an intermediate fact. Rewrite `this` using `[Finset.sum_range_succ, Finset.sum_range_one]`. Evaluate the numerical expressions using `[h01] at this`. Apply the tactic sequence `first | exact this | linear_combination -this`. Establish `hvan : ∀ j, ∀ u ∈ Q ^ j, ∀ l < N, l < j → Δ l u = 0`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro u _ l _ hl`. Use linear arithmetic over natural numbers and integers. Consider the case `succ j ih`.

Introduce `u hu`. Rewrite `hu` using `[pow_succ]`. Use `Submodule.mul_induction_on (C := fun r => ∀ l < N, l < j + 1 → Δ l r = 0) hu ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb l hl hlj`. Rewrite using `[hL l hl]`.

Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p < l + 1` using `Finset.mem_range.mp hp`. Distinguish the cases in `hpj : p < j`. Rewrite using `[ih a ha p (by omega) hpj, zero_mul]`. Establish `: l - p = 0` using `by omega`.

Rewrite using `[this, (hQmem b).mp hb, mul_zero]`. Introduce `a b ha hb l hl hlj`. Rewrite using `[map_add, ha l hl hlj, hb l hl hlj, add_zero]`. Use `set x : A := π - algebraMap k A (Δ 0 π) with hx`. Establish `hx0 : Δ 0 x = 0` using `by rw [hx, map_sub, halg, h01, mul_one, sub_self]`.

Establish `hx1 : Δ 1 x = 1` using `by rw [hx, map_sub, halg, h11, mul_zero, sub_zero, hπ]`. Establish `hxQ : x ∈ Q` using `(hQmem x).mpr hx0`. Establish `hxpow : ∀ j < N, Δ j (x ^ j) = 1`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero => intro _`. Simplify using `using h01`. Consider the case `succ j ih`. Introduce `hj`. Rewrite using `[pow_succ, hL (j + 1) hj, Finset.sum_eq_single j]`.

Rewrite using `[ih (by omega), show j + 1 - j = 1 by omega, hx1, one_mul]`. Introduce `p hp hpj`. Establish `hp'` using `Finset.mem_range.mp hp`. Distinguish the cases in `hlt : p < j`. Rewrite using `[hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) hlt, zero_mul]`.

Establish `: p = j + 1` using `by omega`. Substitute `this` using the available equality. Rewrite using `[Nat.sub_self, hx0, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (by omega)) h`.

Establish `hxQ2 : x ∉ Q ^ 2`. Introduce `h`. Use `hvan 2 x h 1 hN1 (by norm_num)` as an intermediate fact. Rewrite `this` using `[hx1]`. Conclude with `one_ne_zero this`.

Take `⟨J, hJ⟩ : Q ∣ Ideal.span {x}` from `Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)`. Establish `hJQ : Q ⊔ J = ⊤`. Assume the negation of the conclusion as `hne`. Establish `hle : J ≤ Q`. Use `hQmax.eq_of_le hne le_sup_left` as an intermediate fact.

Rewrite using `[this]`. Conclude with `le_sup_right`. Apply `hxQ2` to reduce the goal to its premises. Establish `: Ideal.span {x} ≤ Q ^ 2`. Rewrite using `[hJ, sq]`.

Conclude with `Ideal.mul_mono_right hle`. Conclude with `this (Ideal.mem_span_singleton_self x)`. Establish `hdec : ∀ j, Q ^ j ≤ Ideal.span {x ^ j} ⊔ Q ^ (j + 1)`. Introduce `j`. Establish `htop : J ^ j ⊔ Q = ⊤`.

Rewrite using `[sup_comm]`. Conclude with `Ideal.sup_pow_eq_top hJQ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]`. Use `_ ≤ _ := le_rfl`.

Use `⟨Q, hQmax, hQmem, fun f hf => ?_⟩` and prove the remaining obligations. Establish `key : ∀ j ≤ N, f ∈ Q ^ j`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _`.

Simplify using the standard rewrite rules. Consider the case `succ j ih`. Introduce `hj`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp (hdec j (ih (by omega)))`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`.

Establish `hzv : Δ j z = 0` using `hvan (j + 1) z hz j (by omega) (by omega)`. Establish `hfj : Δ j f = 0` using `hf j (by omega)`. Establish `ha : Δ 0 a = 0`. Rewrite `hfj` using `[← hyz, map_add, hzv, add_zero, mul_comm a, hL j (by omega), Finset.sum_eq_single j]`. Rewrite `hfj` using `[hxpow j (by omega), Nat.sub_self, one_mul]`. Then use the resulting hypothesis.

Introduce `p hp hpj`. Establish `hp'` using `Finset.mem_range.mp hp`. Rewrite using `[hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) (by omega), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_range.mpr (by omega)) h`.

Rewrite using `[← hyz]`. Use `Ideal.add_mem _ ?_ hz` and prove the remaining obligations. Rewrite using `[pow_succ, mul_comm a]`. Conclude with `Ideal.mul_mem_mul (Ideal.pow_mem_pow hxQ j) ((hQmem a).mpr ha)`. Conclude with `key N le_rfl`.
-/
theorem hasseJet_vanishing_mem_pow (k A : Type) [Field k] [IsAlgClosed k] [CommRing A]
    [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (Δ : ℕ → A →ₗ[k] k)
    (hN : 2 ≤ N) (h01 : Δ 0 1 = 1)
    (hL : ∀ l < N, ∀ u w : A, Δ l (u * w) = ∑ p ∈ Finset.range (l + 1), Δ p u * Δ (l - p) w)
    (hπ : ∃ π : A, Δ 1 π = 1) :
    ∃ Q : Ideal A, Q.IsMaximal ∧ (∀ u, u ∈ Q ↔ Δ 0 u = 0) ∧
      ∀ f : A, (∀ l < N, Δ l f = 0) → f ∈ Q ^ N := by
  classical
  obtain ⟨π, hπ⟩ := hπ
  have hN0 : 0 < N := by omega
  have hN1 : 1 < N := by omega
  have hmul0 : ∀ u w : A, Δ 0 (u * w) = Δ 0 u * Δ 0 w := by
    intro u w
    have := hL 0 hN0 u w
    simpa using this
  let φ : A →+* k :=
    { toFun := Δ 0
      map_one' := h01
      map_mul' := hmul0
      map_zero' := map_zero _
      map_add' := map_add _ }
  have hφ : ∀ u, φ u = Δ 0 u := fun _ => rfl
  have halg : ∀ l c, Δ l (algebraMap k A c) = c * Δ l 1 := by
    intro l c
    rw [Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul]
  have hsurj : Function.Surjective φ := by
    intro c
    refine ⟨algebraMap k A c, ?_⟩
    rw [hφ, halg, h01, mul_one]
  set Q : Ideal A := RingHom.ker φ with hQdef
  have hQmax : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  have hQmem : ∀ u, u ∈ Q ↔ Δ 0 u = 0 := fun u => RingHom.mem_ker
  have h11 : Δ 1 (1 : A) = 0 := by
    have := hL 1 hN1 1 1
    rw [Finset.sum_range_succ, Finset.sum_range_one] at this
    norm_num [h01] at this
    first | exact this | linear_combination -this
  have hvan : ∀ j, ∀ u ∈ Q ^ j, ∀ l < N, l < j → Δ l u = 0 := by
    intro j
    induction j with
    | zero => intro u _ l _ hl; omega
    | succ j ih =>
      intro u hu
      rw [pow_succ] at hu
      refine Submodule.mul_induction_on (C := fun r => ∀ l < N, l < j + 1 → Δ l r = 0) hu ?_ ?_
      · intro a ha b hb l hl hlj
        rw [hL l hl]
        refine Finset.sum_eq_zero fun p hp => ?_
        have hp' : p < l + 1 := Finset.mem_range.mp hp
        by_cases hpj : p < j
        · rw [ih a ha p (by omega) hpj, zero_mul]
        · have : l - p = 0 := by omega
          rw [this, (hQmem b).mp hb, mul_zero]
      · intro a b ha hb l hl hlj
        rw [map_add, ha l hl hlj, hb l hl hlj, add_zero]
  set x : A := π - algebraMap k A (Δ 0 π) with hx
  have hx0 : Δ 0 x = 0 := by rw [hx, map_sub, halg, h01, mul_one, sub_self]
  have hx1 : Δ 1 x = 1 := by rw [hx, map_sub, halg, h11, mul_zero, sub_zero, hπ]
  have hxQ : x ∈ Q := (hQmem x).mpr hx0
  have hxpow : ∀ j < N, Δ j (x ^ j) = 1 := by
    intro j
    induction j with
    | zero => intro _; simpa using h01
    | succ j ih =>
      intro hj
      rw [pow_succ, hL (j + 1) hj, Finset.sum_eq_single j]
      · rw [ih (by omega), show j + 1 - j = 1 by omega, hx1, one_mul]
      · intro p hp hpj
        have hp' := Finset.mem_range.mp hp
        by_cases hlt : p < j
        · rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) hlt, zero_mul]
        · have : p = j + 1 := by omega
          subst this
          rw [Nat.sub_self, hx0, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr (by omega)) h
  have hxQ2 : x ∉ Q ^ 2 := by
    intro h
    have := hvan 2 x h 1 hN1 (by norm_num)
    rw [hx1] at this
    exact one_ne_zero this
  obtain ⟨J, hJ⟩ : Q ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hxQ)
  have hJQ : Q ⊔ J = ⊤ := by
    by_contra hne
    have hle : J ≤ Q := by
      have := hQmax.eq_of_le hne le_sup_left
      rw [this]
      exact le_sup_right
    apply hxQ2
    have : Ideal.span {x} ≤ Q ^ 2 := by
      rw [hJ, sq]
      exact Ideal.mul_mono_right hle
    exact this (Ideal.mem_span_singleton_self x)
  have hdec : ∀ j, Q ^ j ≤ Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
    intro j
    have htop : J ^ j ⊔ Q = ⊤ := by
      rw [sup_comm]
      exact Ideal.sup_pow_eq_top hJQ
    calc Q ^ j = Q ^ j * (J ^ j ⊔ Q) := by rw [htop, Ideal.mul_top]
      _ = Q ^ j * J ^ j ⊔ Q ^ j * Q := Ideal.mul_sup _ _ _
      _ = Ideal.span {x ^ j} ⊔ Q ^ (j + 1) := by
        rw [← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]
      _ ≤ _ := le_rfl
  refine ⟨Q, hQmax, hQmem, fun f hf => ?_⟩
  have key : ∀ j ≤ N, f ∈ Q ^ j := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hdec j (ih (by omega)))
      obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
      have hzv : Δ j z = 0 := hvan (j + 1) z hz j (by omega) (by omega)
      have hfj : Δ j f = 0 := hf j (by omega)
      have ha : Δ 0 a = 0 := by
        rw [← hyz, map_add, hzv, add_zero, mul_comm a, hL j (by omega),
          Finset.sum_eq_single j] at hfj
        · rwa [hxpow j (by omega), Nat.sub_self, one_mul] at hfj
        · intro p hp hpj
          have hp' := Finset.mem_range.mp hp
          rw [hvan j (x ^ j) (Ideal.pow_mem_pow hxQ j) p (by omega) (by omega), zero_mul]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      rw [← hyz]
      refine Ideal.add_mem _ ?_ hz
      rw [pow_succ, mul_comm a]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxQ j) ((hQmem a).mpr ha)
  exact key N le_rfl

end GlobalTheory
