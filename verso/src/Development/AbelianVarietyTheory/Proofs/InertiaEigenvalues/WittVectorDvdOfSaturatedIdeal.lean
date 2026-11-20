import Mathlib

namespace GlobalTheory

open WittVector

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro t j hj`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`.

Introduce `t j hj`. Establish `h : (l : WittVector l R) ^ (m + 1) * t = verschiebung (frobenius ((l : WittVector l R) ^ m * t))`. Rewrite using `[verschiebung_frobenius]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`.

Consider the cases of `j with`. Consider the case `zero => exact verschiebung_coeff_zero _`. Consider the case `succ j`. Rewrite using `[verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]`. Conclude with `zero_pow hl.out.ne_zero`.
-/
theorem wittVector_coeff_pow_mul_eq_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by
  intro m
  induction m with
  | zero => intro t j hj; omega
  | succ m ih =>
    intro t j hj
    have h : (l : WittVector l R) ^ (m + 1) * t
        = verschiebung (frobenius ((l : WittVector l R) ^ m * t)) := by
      rw [verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact verschiebung_coeff_zero _
    | succ j =>
      rw [verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]
      exact zero_pow hl.out.ne_zero

/- English proof (translation)
Establish `h0 : truncate m ((l : WittVector l R) ^ m * t) = 0`. Use extensionality with `i`. Rewrite using `[WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]`. Conclude with `wittVector_coeff_pow_mul_eq_zero m t i i.2`. Establish `h1 : truncate m (x + (l : WittVector l R) ^ m * t) = truncate m x`.

Rewrite using `[map_add, h0, add_zero]`. Use `congrArg (fun y => TruncatedWittVector.coeff ⟨j, hj⟩ y) h1` as an intermediate fact. Simplify `this` using `only [WittVector.coeff_truncate]`.
-/
theorem wittVector_coeff_add_pow_mul {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] (x t : WittVector l R) (m j : ℕ) (hj : j < m) :
    (x + (l : WittVector l R) ^ m * t).coeff j = x.coeff j := by
  have h0 : truncate m ((l : WittVector l R) ^ m * t) = 0 := by
    ext i
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact wittVector_coeff_pow_mul_eq_zero m t i i.2
  have h1 : truncate m (x + (l : WittVector l R) ^ m * t) = truncate m x := by
    rw [map_add, h0, add_zero]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨j, hj⟩ y) h1
  simpa only [WittVector.coeff_truncate] using this

/- English proof (translation)
Distinguish the cases in `h : x = 0`. Conclude with `⟨0, by rw [h, mul_zero]⟩`. Take `⟨m, b, hb, hxb⟩` from `exists_eq_pow_p_mul x h`. Consider the cases of `m with`. Consider the case `zero => rw [pow_zero, one_mul] at hxb`.

Conclude with `absurd (hxb ▸ hx) hb`. Consider the case `succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩`.
-/
theorem wittVector_dvd_of_coeff_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] [PerfectRing R l] (x : WittVector l R) (hx : x.coeff 0 = 0) :
    ∃ y, x = (l : WittVector l R) * y := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := exists_eq_pow_p_mul x h
  cases m with
  | zero => rw [pow_zero, one_mul] at hxb; exact absurd (hxb ▸ hx) hb
  | succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩

/- English proof (translation)
Introduce `l _ R _ _ _ J μ hμ hsat hdiv a ha`. Establish `step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J, (d : WittVector l R) = μ * c + (l : WittVector l R) * d'`. Introduce `d`. Take `⟨c₀, hc₀⟩` from `hdiv d d.2`. Use `set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef`.

Establish `hx0 : x.coeff 0 = 0`. Establish `e : (d : WittVector l R) = x + μ * teichmuller l c₀` using `by rw [hxdef]; ring`. Establish `h2` using `congrArg (fun y : WittVector l R => y.coeff 0) e`. Simplify using `only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2`. Rewrite `h2` using `[hc₀]`.

Take the linear combination `-h2`. Take `⟨y, hy⟩` from `wittVector_dvd_of_coeff_zero x hx0`. Establish `hyJ : y ∈ J`. Apply `hsat` to reduce the goal to its premises. Rewrite using `[← hy, hxdef]`.

Conclude with `J.sub_mem d.2 (J.mul_mem_right _ hμ)`. Use `⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hy, hxdef]`. Expand and normalize the polynomial expressions, which then agree. Use `choose cf df hcd using step`.

Set `seq : ℕ → J` to `fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n`. Set `s : ℕ → WittVector l R` to `fun n => ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)`. Establish `hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n)`. Introduce `n`. Simplify using `only [s, Finset.sum_range_succ]`.

Establish `hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [s, seq]`. Consider the case `succ n ih`.

Establish `e : (seq (n + 1)).1 = (df (seq n)).1` using `rfl`. Rewrite using `[hs_succ, e]`. Use `hcd (seq n)` as an intermediate fact. Rewrite using `[ih, this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t`. Introduce `n m hnm`. Proceed by induction on `m, hnm using Nat.le_induction with`. Consider the case `base => exact ⟨0, by ring⟩`. Consider the case `succ m hnm ih`.

Take `⟨t, ht⟩` from `ih`. Use `⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩` and prove the remaining obligations. Rewrite using `[hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]`. Expand and normalize the polynomial expressions, which then agree. Set `c : WittVector l R` to `WittVector.mk l (fun k => (s (k + 1)).coeff k)`.

Use `⟨c, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Establish `htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1))`. Use extensionality with `i`. Rewrite using `[WittVector.coeff_truncate, WittVector.coeff_truncate]`.

Take `⟨t, ht⟩` from `hstab ((i : ℕ) + 1) (k + 1) (by omega)`. Use `show (s ((i : ℕ) + 1)).coeff i = _`. Rewrite using `[ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]`. Establish `hta : truncate (k + 1) a = truncate (k + 1) (μ * c)`. Establish `e` using `hmain (k + 1)`.

Establish `h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1) = 0`. Use extensionality with `i`. Rewrite using `[WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]`. Conclude with `wittVector_coeff_pow_mul_eq_zero _ _ i i.2`. Use `conv_lhs => rw [e]`.

Rewrite using `[map_add, h0, add_zero, map_mul, map_mul, htc]`. Use `congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta` as an intermediate fact. Simplify `this` using `only [WittVector.coeff_truncate]`.
-/
theorem wittVector_dvd_of_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by
  intro l _ R _ _ _ J μ hμ hsat hdiv a ha

  have step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J,
      (d : WittVector l R) = μ * c + (l : WittVector l R) * d' := by
    intro d
    obtain ⟨c₀, hc₀⟩ := hdiv d d.2
    set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef
    have hx0 : x.coeff 0 = 0 := by
      have e : (d : WittVector l R) = x + μ * teichmuller l c₀ := by rw [hxdef]; ring
      have h2 := congrArg (fun y : WittVector l R => y.coeff 0) e
      simp only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2
      rw [hc₀] at h2
      linear_combination -h2
    obtain ⟨y, hy⟩ := wittVector_dvd_of_coeff_zero x hx0
    have hyJ : y ∈ J := by
      apply hsat
      rw [← hy, hxdef]
      exact J.sub_mem d.2 (J.mul_mem_right _ hμ)
    refine ⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩
    rw [← hy, hxdef]; ring
  choose cf df hcd using step
  let seq : ℕ → J := fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n
  let s : ℕ → WittVector l R := fun n =>
    ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)
  have hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n) := by
    intro n; simp only [s, Finset.sum_range_succ]
  have hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : (seq (n + 1)).1 = (df (seq n)).1 := rfl
      rw [hs_succ, e]
      have := hcd (seq n)
      rw [ih, this]; ring
  have hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨0, by ring⟩
    | succ m hnm ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩
      rw [hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]; ring
  let c : WittVector l R := WittVector.mk l (fun k => (s (k + 1)).coeff k)
  refine ⟨c, ?_⟩
  ext k

  have htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1)) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    obtain ⟨t, ht⟩ := hstab ((i : ℕ) + 1) (k + 1) (by omega)
    show (s ((i : ℕ) + 1)).coeff i = _
    rw [ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]
  have hta : truncate (k + 1) a = truncate (k + 1) (μ * c) := by
    have e := hmain (k + 1)
    have h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1)
        = 0 := by
      ext i
      rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      exact wittVector_coeff_pow_mul_eq_zero _ _ i i.2
    conv_lhs => rw [e]
    rw [map_add, h0, add_zero, map_mul, map_mul, htc]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta
  simpa only [WittVector.coeff_truncate] using this

end GlobalTheory
