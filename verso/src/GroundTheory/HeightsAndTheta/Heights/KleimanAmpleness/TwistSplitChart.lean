import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistSplitObj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Pointwise

noncomputable section

universe u w

section Chart

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {r : ℕ} (η : Fin (r + 1) → Ω)

def twLocPart (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (I : Finset (Fin (N + 1))) :
    Submodule S Ω :=
  Submodule.span S {y | ∃ (z : Ω) (s : Poly S N) (a : ℤ) (e : ℕ), s ∈ monos I ∧ s.IsHomogeneous e ∧
    z ∈ twPart η M₀ a b ∧ a - e = c ∧ y = (aeval x s)⁻¹ * z}

/- English proof (translation)
Use `Submodule.span_induction (p := fun y _ => η j * y ∈ twLocPart η M₀ (b + 1) c I) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩`. Use `Submodule.subset_span ⟨η j * z, s, a, e, hs, hse, twPart_eta_mul η M₀ j hz, hae, ?_⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `u v _ _ hu hv`. Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hu hv`. Introduce `c' u _ hu`.

Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c' hu`.
-/
theorem twLocPart_eta_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} {I : Finset (Fin (N + 1))}
    (j : Fin (r + 1)) {y : Ω} (hy : y ∈ twLocPart η M₀ b c I) : η j * y ∈ twLocPart η M₀ (b + 1) c I := by
  refine Submodule.span_induction (p := fun y _ => η j * y ∈ twLocPart η M₀ (b + 1) c I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨η j * z, s, a, e, hs, hse, twPart_eta_mul η M₀ j hz, hae, ?_⟩
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

/- English proof (translation)
Take `⟨f, s, e, hs, hf, hse, ha⟩` from `a.2`. Rewrite using `[ha]`. Use `Submodule.span_induction (p := fun y _ => aeval x f / aeval x s * y ∈ twLocPart η M₀ b c K.1) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨z, s₁, a₁, e₁, hs₁, hse₁, hz, hae, rfl⟩`. Use `Submodule.subset_span ⟨aeval x f * z, s * s₁, a₁ + e, e + e₁, mul_mem hs hs₁, hse.mul hse₁, twPart_form_mul η M₀ hf hz, by push_cast; omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `u v _ _ hu hv`.

Rewrite using `[mul_add]`. Conclude with `Submodule.add_mem _ hu hv`. Introduce `c' u _ hu`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ c' hu`.
-/
theorem twLocPart_chart_mul (M₀ : FinGradedSub (S := S) (x := x) Ω) {b c : ℤ} (K : Chart x)
    (a : chartRing S x K) {y : Ω} (hy : y ∈ twLocPart η M₀ b c K.1) : (a : Ω) * y ∈ twLocPart η M₀ b c K.1 := by
  obtain ⟨f, s, e, hs, hf, hse, ha⟩ := a.2
  rw [ha]
  refine Submodule.span_induction (p := fun y _ => aeval x f / aeval x s * y ∈ twLocPart η M₀ b c K.1)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨z, s₁, a₁, e₁, hs₁, hse₁, hz, hae, rfl⟩
    refine Submodule.subset_span ⟨aeval x f * z, s * s₁, a₁ + e, e + e₁, mul_mem hs hs₁, hse.mul hse₁,
      twPart_form_mul η M₀ hf hz, by push_cast; omega, ?_⟩
    rw [map_mul, mul_inv, div_eq_mul_inv]
    ring
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [mul_add]; exact Submodule.add_mem _ hu hv
  · intro c' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_mem _ c' hu

def twLocPartA (M₀ : FinGradedSub (S := S) (x := x) Ω) (b c : ℤ) (K : Chart x) :
    Submodule (chartRing S x K) Ω where
  carrier := twLocPart η M₀ b c K.1
  add_mem' := Submodule.add_mem _
  zero_mem' := Submodule.zero_mem _
  smul_mem' a y hy := by rw [chartRing_smul_def]; exact twLocPart_chart_mul η M₀ K a hy

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction generalizing v with`. Consider the case `mem u hu`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv => exact h u hu v hv`. Consider the case `zero => rw [mul_zero, mul_zero]`.

Conclude with `T.zero_mem`. Consider the case `add v v' _ _ h₁ h₂ => rw [mul_add, mul_add]`. Conclude with `T.add_mem h₁ h₂`. Consider the case `smul a v _ h₁`. Establish `: w * (u * (a • v)) = a • (w * (u * v))` using `by rw [chartRing_smul_def, chartRing_smul_def]; ring`.

Rewrite using `[this]`. Conclude with `T.smul_mem a h₁`. Consider the case `zero => rw [zero_mul, mul_zero]`. Conclude with `T.zero_mem`. Consider the case `add u u' _ _ h₁ h₂ => rw [add_mul, mul_add]`.

Conclude with `T.add_mem (h₁ hv) (h₂ hv)`. Consider the case `smul a u _ h₁`. Establish `: w * ((a • u) * v) = a • (w * (u * v))` using `by rw [chartRing_smul_def, chartRing_smul_def]; ring`. Rewrite using `[this]`. Conclude with `T.smul_mem a (h₁ hv)`.
-/
theorem mul_mem_of_mem_span {K : Chart x} (T : Submodule (chartRing S x K) Ω) {s t : Set Ω} (w : Ω)
    (h : ∀ u ∈ s, ∀ v ∈ t, w * (u * v) ∈ T) {u v : Ω} (hu : u ∈ Submodule.span (chartRing S x K) s)
    (hv : v ∈ Submodule.span (chartRing S x K) t) : w * (u * v) ∈ T := by
  induction hu using Submodule.span_induction generalizing v with
  | mem u hu =>
    induction hv using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => rw [mul_zero, mul_zero]; exact T.zero_mem
    | add v v' _ _ h₁ h₂ => rw [mul_add, mul_add]; exact T.add_mem h₁ h₂
    | smul a v _ h₁ =>
      have : w * (u * (a • v)) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
      rw [this]; exact T.smul_mem a h₁
  | zero => rw [zero_mul, mul_zero]; exact T.zero_mem
  | add u u' _ _ h₁ h₂ => rw [add_mul, mul_add]; exact T.add_mem (h₁ hv) (h₂ hv)
  | smul a u _ h₁ =>
    have : w * ((a • u) * v) = a • (w * (u * v)) := by rw [chartRing_smul_def, chartRing_smul_def]; ring
    rw [this]; exact T.smul_mem a (h₁ hv)

variable {G B : SubSystem S x Ω}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `twistMod S x 0 K ≤ _`. Rewrite using `[twistMod, Submodule.span_le]`. Introduce and unpack `_ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩`.

Establish `he : e' = e` using `by omega`. Substitute `he` using the available equality. Establish `hmem : aeval x f / aeval x s ∈ chartRing S x K` using `⟨f, s, e', hs, hf, hse, rfl⟩`. Establish `h1 : (1 : Ω) ∈ Submodule.span (chartRing S x K) (Set.range η ^ 0)` using `Submodule.subset_span (by rw [pow_zero]; exact Set.mem_one.mpr rfl)`. Use `Submodule.smul_mem _ (⟨_, hmem⟩ : chartRing S x K) h1` as an intermediate fact.

Rewrite `this` using `[chartRing_smul_def, mul_one]`. Then use the resulting hypothesis. Consider the case `succ n ih`. Express the relevant statement in the definitionally equal form `Submodule.span _ _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨q, hq, y, hy, rfl⟩`.

Rewrite `hq` using `[← hB K]`. Use `mul_mem_of_mem_span (Submodule.span (chartRing S x K) (Set.range η ^ (n + 1))) 1 (s := Set.range η) (t := Set.range η ^ n) (fun u hu v hv => by` as an intermediate fact. Rewrite using `[one_mul, pow_succ']`. Conclude with `Submodule.subset_span (Set.mul_mem_mul hu hv)) hq (ih hy)`. Rewrite `this` using `[one_mul, ← smul_eq_mul]`. Then use the resulting hypothesis.
-/
theorem pow_sub_le_span (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) : (B.pow n).sub K ≤ Submodule.span (chartRing S x K) (Set.range η ^ n) := by
  induction n with
  | zero =>
    change twistMod S x 0 K ≤ _
    rw [twistMod, Submodule.span_le]
    rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have he : e' = e := by omega
    subst he
    have hmem : aeval x f / aeval x s ∈ chartRing S x K := ⟨f, s, e', hs, hf, hse, rfl⟩
    have h1 : (1 : Ω) ∈ Submodule.span (chartRing S x K) (Set.range η ^ 0) :=
      Submodule.subset_span (by rw [pow_zero]; exact Set.mem_one.mpr rfl)
    have := Submodule.smul_mem _ (⟨_, hmem⟩ : chartRing S x K) h1
    rwa [chartRing_smul_def, mul_one] at this
  | succ n ih =>
    change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hB K] at hq
    have := mul_mem_of_mem_span (Submodule.span (chartRing S x K) (Set.range η ^ (n + 1))) 1
      (s := Set.range η) (t := Set.range η ^ n)
      (fun u hu v hv => by
        rw [one_mul, pow_succ']
        exact Submodule.subset_span (Set.mul_mem_mul hu hv)) hq (ih hy)
    rwa [one_mul, ← smul_eq_mul] at this

/- English proof (translation)
Proceed by induction on `n generalizing q with`. Consider the case `zero`. Rewrite `hq` using `[pow_zero, Set.mem_one]`. Substitute `hq` using the available equality. Conclude with `one_mem_twistMod_zero (S := S) K`.

Consider the case `succ n ih`. Rewrite `hq` using `[pow_succ', Set.mem_mul]`. Take `⟨u, hu, v, hv, rfl⟩` from `hq`. Establish `hu' : u ∈ B.sub K` using `by rw [← hB K]; exact Submodule.subset_span hu`. Conclude with `Submodule.subset_span ⟨u, hu', v, ih hv, smul_eq_mul _ _⟩`.
-/
theorem range_pow_subset (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x)
    (n : ℕ) {q : Ω} (hq : q ∈ Set.range η ^ n) : q ∈ (B.pow n).sub K := by
  induction n generalizing q with
  | zero =>
    rw [pow_zero, Set.mem_one] at hq
    subst hq
    exact one_mem_twistMod_zero (S := S) K
  | succ n ih =>
    rw [pow_succ', Set.mem_mul] at hq
    obtain ⟨u, hu, v, hv, rfl⟩ := hq
    have hu' : u ∈ B.sub K := by rw [← hB K]; exact Submodule.subset_span hu
    exact Submodule.subset_span ⟨u, hu', v, ih hv, smul_eq_mul _ _⟩

variable (M₀ : FinGradedSub (S := S) (x := x) Ω)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `y ∈ twLocPartA η M₀ n c K`. Use `revert y`. Express the relevant statement in the definitionally equal form `Submodule.span _ _ ≤ twLocPartA η M₀ n c K`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨t, ht, y', hy', rfl⟩`.

Rewrite using `[smul_eq_mul, ← one_mul (t * y')]`. Use `mul_mem_of_mem_span _ 1 ?_ ht hy'` and prove the remaining obligations. Introduce and unpack `u ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ v ⟨q, hq, g, hg, rfl⟩`. Rewrite using `[one_mul, smul_eq_mul]`. Rewrite `hg` using `[← hG K]`.

Use `mul_mem_of_mem_span _ (aeval x f / aeval x s) ?_ (pow_sub_le_span η hB K n hq) hg` and prove the remaining obligations. Introduce and unpack `q' hq' _ ⟨m, s₁, a, e₁, hs₁, hse₁, hm, hae, rfl⟩`. Use `Submodule.subset_span ⟨(aeval x f * m) * q', s * s₁, a + e', e + e₁, mul_mem hs hs₁, hse.mul hse₁, ?_, by push_cast; omega, ?_⟩` and prove the remaining obligations. Rewrite using `[twPart_of_nonneg]`. Conclude with `Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem e' a f m hf hm) hq')`.

Rewrite using `[smul_eq_mul, map_mul, mul_inv, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twistSub_le_twLocPart (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K) :
    y ∈ twLocPart η M₀ n c K.1 := by
  change y ∈ twLocPartA η M₀ n c K
  revert y
  change Submodule.span _ _ ≤ twLocPartA η M₀ n c K
  rw [Submodule.span_le]
  rintro _ ⟨t, ht, y', hy', rfl⟩
  rw [smul_eq_mul, ← one_mul (t * y')]
  refine mul_mem_of_mem_span _ 1 ?_ ht hy'
  rintro u ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩ v ⟨q, hq, g, hg, rfl⟩
  rw [one_mul, smul_eq_mul]
  rw [← hG K] at hg
  refine mul_mem_of_mem_span _ (aeval x f / aeval x s) ?_ (pow_sub_le_span η hB K n hq) hg
  rintro q' hq' _ ⟨m, s₁, a, e₁, hs₁, hse₁, hm, hae, rfl⟩
  refine Submodule.subset_span ⟨(aeval x f * m) * q', s * s₁, a + e', e + e₁, mul_mem hs hs₁,
    hse.mul hse₁, ?_, by push_cast; omega, ?_⟩
  · rw [twPart_of_nonneg]
    exact Submodule.subset_span (Set.mul_mem_mul (M₀.smul_mem e' a f m hf hm) hq')
  · rw [smul_eq_mul, map_mul, mul_inv, div_eq_mul_inv]
    ring

/- English proof (translation)
Take `⟨i, hi⟩` from `K.2.1`. Establish `hxi : x i ≠ 0` using `(mem_support x).mp (K.2.2 hi)`. Use `set T := ((G.twist (B.pow n)).twist (twistSys S x c)).sub K with hT`. Use `Submodule.span_induction (p := fun y _ => y ∈ T) ?_ (T.zero_mem) (fun _ _ _ _ h₁ h₂ => T.add_mem h₁ h₂) (fun r' y _ h => Submodule.smul_of_tower_mem T r' h) hy` and prove the remaining obligations. Introduce and unpack `_ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩`.

Establish `hs0 : aeval x s ≠ 0` using `eval_ne_zero_of_mem_monos K hs`. Rewrite `hz` using `[twPart_of_nonneg]`. Use `Submodule.span_induction (p := fun z _ => (aeval x s)⁻¹ * z ∈ T) ?_ ?_ ?_ ?_ hz` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, q, hq, rfl⟩`. Establish `hq'` using `range_pow_subset η hB K n hq`.

Establish `hxc : x i ^ c ∈ twistMod S x c K`. Rewrite using `[twistMod_eq_span c K hi]`. Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨k, rfl | rfl⟩` from `Int.eq_nat_or_neg c`. Establish `hg : (aeval x (s * X i ^ k))⁻¹ • m ∈ G.sub K`.

Rewrite using `[← hG K]`. Conclude with `Submodule.subset_span ⟨m, s * X i ^ k, a, e + k, mul_mem hs (pow_mem (X_mem_monos hi) k), hse.mul (isHomogeneous_X_pow i k), hm, by push_cast; omega, rfl⟩`. Establish `hmem : x i ^ (k : ℤ) • (q • ((aeval x (s * X i ^ k))⁻¹ • m)) ∈ T` using `Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩`. Use `hmem using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast]`.

Clear the denominators using the available nonvanishing facts. Establish `hg : (aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ G.sub K`. Rewrite using `[← hG K]`. Conclude with `Submodule.subset_span ⟨aeval x (X i ^ k : Poly S N) • m, s, a + k, e, hs, hse, M₀.smul_mem k a (X i ^ k : Poly S N) m (isHomogeneous_X_pow i k) hm, by omega, rfl⟩`. Establish `hmem : x i ^ (-(k : ℤ)) • (q • ((aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m))) ∈ T` using `Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩`.

Use `hmem using 1` and compare the differences between its conclusion and the goal. Simplify using `only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[mul_zero]`. Conclude with `T.zero_mem`.

Introduce `u v _ _ hu hv`. Rewrite using `[mul_add]`. Conclude with `T.add_mem hu hv`. Introduce `r' u _ hu`. Rewrite using `[mul_smul_comm]`.

Conclude with `Submodule.smul_of_tower_mem T r' hu`.
-/
theorem twLocPart_le_twistSub (hG : ∀ I, M₀.tilde 0 I = G.sub I)
    (hB : ∀ I, Submodule.span (chartRing S x I) (Set.range η) = B.sub I) (K : Chart x) (n : ℕ) (c : ℤ)
    {y : Ω} (hy : y ∈ twLocPart η M₀ n c K.1) :
    y ∈ ((G.twist (B.pow n)).twist (twistSys S x c)).sub K := by
  obtain ⟨i, hi⟩ := K.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (K.2.2 hi)
  set T := ((G.twist (B.pow n)).twist (twistSys S x c)).sub K with hT
  refine Submodule.span_induction (p := fun y _ => y ∈ T) ?_ (T.zero_mem) (fun _ _ _ _ h₁ h₂ => T.add_mem h₁ h₂)
    (fun r' y _ h => Submodule.smul_of_tower_mem T r' h) hy
  rintro _ ⟨z, s, a, e, hs, hse, hz, hae, rfl⟩
  have hs0 : aeval x s ≠ 0 := eval_ne_zero_of_mem_monos K hs
  rw [twPart_of_nonneg] at hz
  refine Submodule.span_induction (p := fun z _ => (aeval x s)⁻¹ * z ∈ T) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨m, hm, q, hq, rfl⟩
    have hq' := range_pow_subset η hB K n hq
    have hxc : x i ^ c ∈ twistMod S x c K := by
      rw [twistMod_eq_span c K hi]; exact Submodule.mem_span_singleton_self _
    obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have hg : (aeval x (s * X i ^ k))⁻¹ • m ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨m, s * X i ^ k, a, e + k, mul_mem hs (pow_mem (X_mem_monos hi) k),
          hse.mul (isHomogeneous_X_pow i k), hm, by push_cast; omega, rfl⟩
      have hmem : x i ^ (k : ℤ) • (q • ((aeval x (s * X i ^ k))⁻¹ • m)) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_mul, map_pow, aeval_X, zpow_natCast]
      field_simp
    · have hg : (aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m) ∈ G.sub K := by
        rw [← hG K]
        exact Submodule.subset_span ⟨aeval x (X i ^ k : Poly S N) • m, s, a + k, e, hs, hse,
          M₀.smul_mem k a (X i ^ k : Poly S N) m (isHomogeneous_X_pow i k) hm, by omega, rfl⟩
      have hmem : x i ^ (-(k : ℤ)) • (q • ((aeval x s)⁻¹ • (aeval x (X i ^ k : Poly S N) • m))) ∈ T :=
        Submodule.subset_span ⟨_, hxc, _, Submodule.subset_span ⟨q, hq', _, hg, rfl⟩, rfl⟩
      convert hmem using 1
      simp only [smul_eq_mul, map_pow, aeval_X, zpow_neg, zpow_natCast]
      field_simp
  · rw [mul_zero]; exact T.zero_mem
  · intro u v _ _ hu hv; rw [mul_add]; exact T.add_mem hu hv
  · intro r' u _ hu; rw [mul_smul_comm]; exact Submodule.smul_of_tower_mem T r' hu

end Chart

end

end GroundTheory.Heights₂.Heights.Kleiman
