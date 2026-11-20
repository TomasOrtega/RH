import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

def ltOneIdeal {R : Type} [CommRing R] [IsDomain R] (μ : R →*₀ ℝ)
    (h0 : ∀ x, 0 ≤ μ x) (h1 : ∀ x, μ x ≤ 1)
    (hadd : ∀ x y, μ (x + y) ≤ max (μ x) (μ y)) : Ideal R where
  carrier := {x | μ x < 1}
  add_mem' := by
    intro x y hx hy
    exact lt_of_le_of_lt (hadd x y) (max_lt hx hy)
  zero_mem' := by
    show μ 0 < 1
    simp
  smul_mem' := by
    intro c x hx
    show μ (c * x) < 1
    rw [map_mul]
    have hx' : μ x < 1 := hx
    nlinarith [h0 c, h0 x, h1 c]

/- English proof (translation)
Establish `hspan : ∀ y : R, y ≠ 0 → Ideal.span {y} ≠ 0` using `fun y hy => by`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hy`. Establish `hadd : ∀ y z : R, y ≠ 0 → z ≠ 0 → (normalizedFactors (Ideal.span {y * z})).count P = (normalizedFactors (Ideal.span {y})).count P + (normalizedFactors (Ideal.span {z})).count P`. Introduce `y z hy hz`.

Rewrite using `[← Ideal.span_singleton_mul_span_singleton, normalizedFactors_mul (hspan y hy) (hspan z hz), Multiset.count_add]`. Establish `hzero : ∀ y : R, y ∉ P → (normalizedFactors (Ideal.span {y})).count P = 0`. Introduce `y hy`. Apply `Ideal.count_normalizedFactors_eq` to reduce the goal to its premises. Rewrite using `[pow_zero, Ideal.one_eq_top]`.

Conclude with `le_top`. Rewrite using `[zero_add, pow_one, Ideal.span_singleton_le_iff_mem]`. Conclude with `hy`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`.

Conclude with `hπ2 (zero_mem _)`. Establish `hπ1 : (normalizedFactors (Ideal.span {π})).count P = 1`. Apply `Ideal.count_normalizedFactors_eq` to reduce the goal to its premises. Rewrite using `[pow_one, Ideal.span_singleton_le_iff_mem]`. Conclude with `hπ`.

Rewrite using `[Ideal.span_singleton_le_iff_mem]`. Conclude with `hπ2`. Take `⟨A, hA⟩ : P ∣ Ideal.span {π}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem P).2 hπ)`. Establish `hAP : ¬A ≤ P`. Introduce `hle`.

Apply `hπ2` to reduce the goal to its premises. Rewrite using `[← Ideal.span_singleton_le_iff_mem, hA, pow_two]`. Conclude with `Ideal.mul_mono_right hle`. Take `⟨s, hsA, hsP⟩` from `SetLike.not_le_iff_exists.1 hAP`. Establish `hs0 : s ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hsP (zero_mem _)`. Establish `hstep : ∀ y : R, y ∈ P → ∃ z, s * y = π * z`. Introduce `y hy`. Establish `: s * y ∈ Ideal.span {π}`.

Rewrite using `[hA, mul_comm s y]`. Conclude with `Ideal.mul_mem_mul hy hsA`. Conclude with `Ideal.mem_span_singleton.1 this`. Establish `hdiv : ∀ y : R, y ≠ 0 → y ∈ P → ∃ z, z ≠ 0 ∧ (normalizedFactors (Ideal.span {y})).count P = (normalizedFactors (Ideal.span {z})).count P + 1 ∧ μ y = μ π * μ z`. Introduce `y hy hyP`.

Take `⟨z, hz⟩` from `hstep y hyP`. Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Rewrite `hz` using `[mul_zero]`. Conclude with `mul_ne_zero hs0 hy hz`.

Establish `hc` using `hadd s y hs0 hy`. Rewrite `hc` using `[hz, hadd π z hπ0 hz0, hπ1, hzero s hsP]`. Use `⟨z, hz0, by omega, ?_⟩` and prove the remaining obligations. Establish `hμ : μ s * μ y = μ π * μ z` using `by rw [← map_mul, ← map_mul, hz]`. Rewrite `hμ` using `[hone s hsP, one_mul]`. Then use the resulting hypothesis.

It suffices to establish `H : ∀ n : ℕ, ∀ y : R, y ≠ 0 → (normalizedFactors (Ideal.span {y})).count P = n → μ y = μ π ^ n from H _ x hx rfl`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `y hy hn`.

Distinguish the cases in `hyP : y ∈ P`. Take `⟨z, _, hc, _⟩` from `hdiv y hy hyP`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hone y hyP, pow_zero]`. Consider the case `succ n ih`.

Introduce `y hy hn`. Distinguish the cases in `hyP : y ∈ P`. Take `⟨z, hz0, hc, hμ⟩` from `hdiv y hy hyP`. Rewrite using `[hμ, ih z hz0 (by omega), pow_succ, mul_comm]`. Rewrite `hn` using `[hzero y hyP]`.

Use linear arithmetic over natural numbers and integers.
-/
private theorem eq_pow_count_normalizedFactors_of_uniformizer {R : Type} [CommRing R] [IsDedekindDomain R]
    (μ : R →*₀ ℝ) (P : Ideal R) [P.IsPrime] (hone : ∀ x, x ∉ P → μ x = 1)
    (π : R) (hπ : π ∈ P) (hπ2 : π ∉ P ^ 2) (x : R) (hx : x ≠ 0) :
    μ x = μ π ^ (normalizedFactors (Ideal.span {x})).count P := by
  have hspan : ∀ y : R, y ≠ 0 → Ideal.span {y} ≠ 0 := fun y hy => by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact hy
  have hadd : ∀ y z : R, y ≠ 0 → z ≠ 0 → (normalizedFactors (Ideal.span {y * z})).count P =
      (normalizedFactors (Ideal.span {y})).count P + (normalizedFactors (Ideal.span {z})).count P := by
    intro y z hy hz
    rw [← Ideal.span_singleton_mul_span_singleton, normalizedFactors_mul (hspan y hy) (hspan z hz),
      Multiset.count_add]
  have hzero : ∀ y : R, y ∉ P → (normalizedFactors (Ideal.span {y})).count P = 0 := by
    intro y hy
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    · rw [zero_add, pow_one, Ideal.span_singleton_le_iff_mem]
      exact hy
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (zero_mem _)
  have hπ1 : (normalizedFactors (Ideal.span {π})).count P = 1 := by
    apply Ideal.count_normalizedFactors_eq
    · rw [pow_one, Ideal.span_singleton_le_iff_mem]
      exact hπ
    · rw [Ideal.span_singleton_le_iff_mem]
      exact hπ2
  obtain ⟨A, hA⟩ : P ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem P).2 hπ)
  have hAP : ¬A ≤ P := by
    intro hle
    apply hπ2
    rw [← Ideal.span_singleton_le_iff_mem, hA, pow_two]
    exact Ideal.mul_mono_right hle
  obtain ⟨s, hsA, hsP⟩ := SetLike.not_le_iff_exists.1 hAP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hsP (zero_mem _)
  have hstep : ∀ y : R, y ∈ P → ∃ z, s * y = π * z := by
    intro y hy
    have : s * y ∈ Ideal.span {π} := by
      rw [hA, mul_comm s y]
      exact Ideal.mul_mem_mul hy hsA
    exact Ideal.mem_span_singleton.1 this
  have hdiv : ∀ y : R, y ≠ 0 → y ∈ P → ∃ z, z ≠ 0 ∧
      (normalizedFactors (Ideal.span {y})).count P =
        (normalizedFactors (Ideal.span {z})).count P + 1 ∧ μ y = μ π * μ z := by
    intro y hy hyP
    obtain ⟨z, hz⟩ := hstep y hyP
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hz
      exact mul_ne_zero hs0 hy hz
    have hc := hadd s y hs0 hy
    rw [hz, hadd π z hπ0 hz0, hπ1, hzero s hsP] at hc
    refine ⟨z, hz0, by omega, ?_⟩
    have hμ : μ s * μ y = μ π * μ z := by rw [← map_mul, ← map_mul, hz]
    rwa [hone s hsP, one_mul] at hμ
  suffices H : ∀ n : ℕ, ∀ y : R, y ≠ 0 → (normalizedFactors (Ideal.span {y})).count P = n →
      μ y = μ π ^ n from H _ x hx rfl
  intro n
  induction n with
  | zero =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, _, hc, _⟩ := hdiv y hy hyP
      omega
    · rw [hone y hyP, pow_zero]
  | succ n ih =>
    intro y hy hn
    by_cases hyP : y ∈ P
    · obtain ⟨z, hz0, hc, hμ⟩ := hdiv y hy hyP
      rw [hμ, ih z hz0 (by omega), pow_succ, mul_comm]
    · rw [hzero y hyP] at hn
      omega

/- English proof (translation)
Introduce `R _ _ μ a ha h0 h1 hadd hlt hne`. Use `set P := GlobalTheory.CompanionTheory.Ggeo.ltOneIdeal μ h0 h1 hadd with hPdef`. Establish `hmem : ∀ x, x ∈ P ↔ μ x < 1` using `fun x => Iff.rfl`. Establish `hPtop : P ≠ ⊤`. Introduce `htop`.

Establish `h1P` using `(Ideal.eq_top_iff_one P).1 htop`. Rewrite `h1P` using `[hmem, map_one]`. Conclude with `lt_irrefl _ h1P`. Establish `hPprime : P.IsPrime`. Use `⟨hPtop, ?_⟩` and prove the remaining obligations.

Introduce `x y hxy`. Establish `hxy' : μ x * μ y < 1`. Rewrite using `[← map_mul]`. Conclude with `(hmem _).1 hxy`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_or]`. Establish `hx1 : ¬μ x < 1` using `fun h => hc.1 ((hmem x).2 h)`. Establish `hy1 : ¬μ y < 1` using `fun h => hc.2 ((hmem y).2 h)`. Rewrite `hx1`, `hy1` using `[not_lt]`. Use polynomial arithmetic with `[h0 x, h0 y]`.

Use `haveI := hPprime`. Establish `haP : a ∈ P` using `(hmem a).2 hlt`. Establish `hbot : P ≠ ⊥`. Introduce `h`. Rewrite `haP` using `[h, Submodule.mem_bot]`.

Conclude with `ha haP`. Take `⟨π, hπ, hπ2⟩ : ∃ π ∈ P ^ 1, π ∉ P ^ 2` from `SetLike.exists_of_lt (Ideal.pow_right_strictAnti P hbot hPtop (by norm_num : 1 < 2))`. Rewrite `hπ` using `[pow_one]`. Establish `hone : ∀ x, x ∉ P → μ x = 1` using `fun x hx => le_antisymm (h1 x) (not_lt.1 fun h => hx ((hmem x).2 h))`. Establish `hkey` using `eq_pow_count_normalizedFactors_of_uniformizer μ P hone π hπ hπ2`.

Establish `hπne : μ π ≠ 0`. Introduce `h`. Establish `ha'` using `hkey a ha`. Rewrite `ha'` using `[h]`. Break down `Nat.eq_zero_or_pos ((normalizedFactors (Ideal.span {a})).count P) with hk | hk` into its components or cases.

Rewrite `ha'` using `[hk, pow_zero]`. Rewrite `hlt` using `[ha']`. Conclude with `lt_irrefl _ hlt`. Rewrite `ha'` using `[zero_pow hk.ne']`. Conclude with `hne ha'`.

Conclude with `⟨P, μ π, hPprime, hbot, haP, lt_of_le_of_ne (h0 π) (Ne.symm hπne), hkey⟩`.
-/
theorem map_eq_pow_count_of_ultrametric :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (μ : R →*₀ ℝ) (a : R), a ≠ 0 →
      (∀ x, 0 ≤ μ x) → (∀ x, μ x ≤ 1) → (∀ x y, μ (x + y) ≤ max (μ x) (μ y)) →
      μ a < 1 → μ a ≠ 0 →
      ∃ (P : Ideal R) (c : ℝ), P.IsPrime ∧ P ≠ ⊥ ∧ a ∈ P ∧ 0 < c ∧
        ∀ x : R, x ≠ 0 → μ x = c ^ (normalizedFactors (Ideal.span {x})).count P := by
  intro R _ _ μ a ha h0 h1 hadd hlt hne
  set P := GlobalTheory.CompanionTheory.Ggeo.ltOneIdeal μ h0 h1 hadd with hPdef
  have hmem : ∀ x, x ∈ P ↔ μ x < 1 := fun x => Iff.rfl
  have hPtop : P ≠ ⊤ := by
    intro htop
    have h1P := (Ideal.eq_top_iff_one P).1 htop
    rw [hmem, map_one] at h1P
    exact lt_irrefl _ h1P
  have hPprime : P.IsPrime := by
    refine ⟨hPtop, ?_⟩
    intro x y hxy
    have hxy' : μ x * μ y < 1 := by
      rw [← map_mul]
      exact (hmem _).1 hxy
    by_contra hc
    rw [not_or] at hc
    have hx1 : ¬μ x < 1 := fun h => hc.1 ((hmem x).2 h)
    have hy1 : ¬μ y < 1 := fun h => hc.2 ((hmem y).2 h)
    rw [not_lt] at hx1 hy1
    nlinarith [h0 x, h0 y]
  haveI := hPprime
  have haP : a ∈ P := (hmem a).2 hlt
  have hbot : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at haP
    exact ha haP
  obtain ⟨π, hπ, hπ2⟩ : ∃ π ∈ P ^ 1, π ∉ P ^ 2 := SetLike.exists_of_lt
    (Ideal.pow_right_strictAnti P hbot hPtop (by norm_num : 1 < 2))
  rw [pow_one] at hπ
  have hone : ∀ x, x ∉ P → μ x = 1 := fun x hx =>
    le_antisymm (h1 x) (not_lt.1 fun h => hx ((hmem x).2 h))
  have hkey := eq_pow_count_normalizedFactors_of_uniformizer μ P hone π hπ hπ2
  have hπne : μ π ≠ 0 := by
    intro h
    have ha' := hkey a ha
    rw [h] at ha'
    rcases Nat.eq_zero_or_pos ((normalizedFactors (Ideal.span {a})).count P) with hk | hk
    · rw [hk, pow_zero] at ha'
      rw [ha'] at hlt
      exact lt_irrefl _ hlt
    · rw [zero_pow hk.ne'] at ha'
      exact hne ha'
  exact ⟨P, μ π, hPprime, hbot, haP, lt_of_le_of_ne (h0 π) (Ne.symm hπne), hkey⟩

end GlobalTheory.CompanionTheory.Ggeo
