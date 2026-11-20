import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCurveCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsClosedPointUnitSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ClosedPointAffineChart

variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')

omit [Fintype T] in

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩`.
-/
theorem ratio_mem (t u : T) : y ⟨(), u⟩ / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨⟨(), u⟩, rfl⟩

omit [Fintype T] in

/- English proof (translation)
The claim follows from `mem_curveRing.mp hb (fun _ => t) (fun _ => ht)`.
-/
theorem mem_chart_of_mem_curveRing {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp hb (fun _ => t) (fun _ => ht)

omit [Fintype T] in

/- English proof (translation)
Rewrite using `[mem_curveRing]`. Introduce `c hc`. Establish `hc' : c = fun _ => c ()` using `funext fun u => by cases u; rfl`. Establish `h1` using `h (c ()) (hc ())`. Rewrite `h1` using `[← hc']`. Then use the resulting hypothesis.
-/
theorem mem_curveRing_of_forall {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := h (c ()) (hc ())
  rwa [← hc'] at h1

omit [Fintype T] in

/- English proof (translation)
Establish `h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t)` using `hg (fun _ => t) (fun _ => ht)`. Simplify `h` using `[zpow_neg, zpow_natCast, div_eq_mul_inv]`.
-/
theorem div_pow_mem_of_mem_chartLat {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by
  have h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t) :=
    hg (fun _ => t) (fun _ => ht)
  simpa [zpow_neg, zpow_natCast, div_eq_mul_inv] using h

omit [Fintype T] in

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Set `R : Subring K'` to `(chartRingZ y (fun _ => t)).toSubring`. Establish `hBR : curveRing y ≤ R` using `fun b hb => mem_chart_of_mem_curveRing y hb t ht`. Set `S' : Submonoid R` to `m.primeCompl.map (Subring.inclusion hBR)`.

Set `z : R` to `⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩`. Establish `hyt : y ⟨(), t⟩ ^ e ≠ 0` using `pow_ne_zero _ ht`. Establish `hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R)`. Rewrite using `[Set.disjoint_left]`. Introduce `r hr hrS`.

Take `⟨s, hs, rfl⟩` from `Submonoid.mem_map.mp hrS`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.mp hr`. Establish `h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K')` using `congrArg Subtype.val hw`. Apply `hcon s hs` to reduce the goal to its premises. Rewrite using `[← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]`.

Conclude with `w.2`. Take `⟨q, hq, hzq, hqS⟩` from `Ideal.exists_le_prime_disjoint _ S' hdisj`. Take `⟨W, hRW, hunit, hlt⟩` from `ClosedPointUnitSection.exists_valuationSubring R q`. Establish `hBW : ∀ b : curveRing y, (b : K') ∈ W` using `fun b => hRW (Subring.inclusion hBR b)`. Establish `hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1`.

Introduce `b hb`. Apply `hunit (Subring.inclusion hBR b)` to reduce the goal to its premises. Introduce `hbq`. Conclude with `Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)`. Establish `h1` using `hW W hBW hBunit t`.

Establish `h2 : W.valuation (z : K') < 1` using `hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))`. Establish `h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1` using `by show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1`. Clear the denominators using the available nonvanishing facts. Establish `h4` using `congrArg W.valuation h3`. Rewrite `h4` using `[map_mul, map_one]`.

Establish `h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1` using `(W.valuation_le_one_iff _).mpr h1`. Establish `h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2`. Conclude with `ne_of_lt h6 h4`.
-/
theorem exists_mul_inv_mem {m : Ideal (curveRing y)} [m.IsPrime] {e : ℕ} {g : K'} (hg0 : g ≠ 0)
    (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (y ⟨(), t⟩ ^ e / g) ∈ chartRingZ y (fun _ => t) := by
  by_contra hcon
  push Not at hcon
  let R : Subring K' := (chartRingZ y (fun _ => t)).toSubring
  have hBR : curveRing y ≤ R := fun b hb => mem_chart_of_mem_curveRing y hb t ht
  let S' : Submonoid R := m.primeCompl.map (Subring.inclusion hBR)
  let z : R := ⟨g / y ⟨(), t⟩ ^ e, div_pow_mem_of_mem_chartLat y hgL t ht⟩
  have hyt : y ⟨(), t⟩ ^ e ≠ 0 := pow_ne_zero _ ht
  have hdisj : Disjoint ((Ideal.span {z} : Ideal R) : Set R) (S' : Set R) := by
    rw [Set.disjoint_left]
    intro r hr hrS
    obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.mp hrS
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hr
    have h1 : (w : K') * (g / y ⟨(), t⟩ ^ e) = (s : K') := congrArg Subtype.val hw
    apply hcon s hs
    rw [← h1, show (w : K') * (g / y ⟨(), t⟩ ^ e) * (y ⟨(), t⟩ ^ e / g) = (w : K') by field_simp]
    exact w.2
  obtain ⟨q, hq, hzq, hqS⟩ := Ideal.exists_le_prime_disjoint _ S' hdisj
  obtain ⟨W, hRW, hunit, hlt⟩ := ClosedPointUnitSection.exists_valuationSubring R q
  have hBW : ∀ b : curveRing y, (b : K') ∈ W := fun b => hRW (Subring.inclusion hBR b)
  have hBunit : ∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1 := by
    intro b hb
    apply hunit (Subring.inclusion hBR b)
    intro hbq
    exact Set.disjoint_left.mp hqS hbq (Submonoid.mem_map.mpr ⟨b, hb, rfl⟩)
  have h1 := hW W hBW hBunit t
  have h2 : W.valuation (z : K') < 1 := hlt z (hzq (Ideal.subset_span (Set.mem_singleton z)))
  have h3 : (z : K') * (y ⟨(), t⟩ ^ e / g) = 1 := by
    show g / y ⟨(), t⟩ ^ e * (y ⟨(), t⟩ ^ e / g) = 1
    field_simp
  have h4 := congrArg W.valuation h3
  rw [map_mul, map_one] at h4
  have h5 : W.valuation (y ⟨(), t⟩ ^ e / g) ≤ 1 := (W.valuation_le_one_iff _).mpr h1
  have h6 : W.valuation (z : K') * W.valuation (y ⟨(), t⟩ ^ e / g) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' h5) h2
  exact ne_of_lt h6 h4

/- English proof (translation)
Use `hm.isPrime` as an intermediate fact. Establish `key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧ (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t))`. Introduce `t`. Distinguish the cases in `ht : y ⟨(), t⟩ = 0`. Conclude with `⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩`.

Take `⟨s, hs, hsm⟩` from `exists_mul_inv_mem y hg0 hgL hW t ht`. Use `⟨s, hs, fun _ => ?_⟩` and prove the remaining obligations. Establish `e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e1]`.

Conclude with `mul_mem (hh t ht) hsm`. Use `choose S hSm hS using key`. Use `⟨∏ t, S t, fun hmem => ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, -, ht⟩` from `Ideal.IsPrime.prod_mem_iff.mp hmem`. Conclude with `hSm t ht`.

Apply `mem_curveRing_of_forall` to reduce the goal to its premises. Introduce `t ht`. Establish `e1 : ((∏ u, S u : curveRing y) : K') * (h / g) = (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g))`. Use `push_cast`. Rewrite using `[← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Conclude with `mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)`.
-/
theorem exists_mul_div_mem_curveRing {m : Ideal (curveRing y)} (hm : m.IsMaximal) {e : ℕ} {g : K'}
    (hg0 : g ≠ 0) (hgL : g ∈ chartLat y 1 e)
    (hW : ∀ W : ValuationSubring K', (∀ b : curveRing y, (b : K') ∈ W) →
      (∀ b : curveRing y, b ∉ m → W.valuation (b : K') = 1) → ∀ u : T, y ⟨(), u⟩ ^ e / g ∈ W)
    {h : K'} (hh : ∀ t : T, y ⟨(), t⟩ ≠ 0 → h / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t)) :
    ∃ s : curveRing y, s ∉ m ∧ (s : K') * (h / g) ∈ curveRing y := by
  classical
  have := hm.isPrime
  have key : ∀ t : T, ∃ s : curveRing y, s ∉ m ∧
      (y ⟨(), t⟩ ≠ 0 → (s : K') * (h / g) ∈ chartRingZ y (fun _ => t)) := by
    intro t
    by_cases ht : y ⟨(), t⟩ = 0
    · exact ⟨1, fun h1 => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun h' => (h' ht).elim⟩
    · obtain ⟨s, hs, hsm⟩ := exists_mul_inv_mem y hg0 hgL hW t ht
      refine ⟨s, hs, fun _ => ?_⟩
      have e1 : (s : K') * (h / g) = h / y ⟨(), t⟩ ^ e * ((s : K') * (y ⟨(), t⟩ ^ e / g)) := by
        field_simp
      rw [e1]
      exact mul_mem (hh t ht) hsm
  choose S hSm hS using key
  refine ⟨∏ t, S t, fun hmem => ?_, ?_⟩
  · obtain ⟨t, -, ht⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hSm t ht
  · apply mem_curveRing_of_forall
    intro t ht
    have e1 : ((∏ u, S u : curveRing y) : K') * (h / g) =
        (∏ u ∈ Finset.univ.erase t, (S u : K')) * ((S t : K') * (h / g)) := by
      push_cast
      rw [← Finset.mul_prod_erase Finset.univ (fun u => (S u : K')) (Finset.mem_univ t)]
      ring
    rw [e1]
    exact mul_mem (prod_mem fun u _ => mem_chart_of_mem_curveRing y (S u).2 t ht) (hS t ht)

end ClosedPointAffineChart

/- English proof (translation)
Introduce `T _ K' _ _ y hy m hm`. Take `⟨e, g, he, hg0, hgL, hW⟩` from `hU T K' y hy m hm`. Use `hm.isPrime` as an intermediate fact. Take `⟨W, hBW, hBunit, hBlt⟩` from `ClosedPointUnitSection.exists_valuationSubring (curveRing y) m`. Take `⟨t0, ht0⟩` from `CurveAffineCharts.exists_chart y hy`.

Take `⟨t, -, ht⟩` from `Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩)) ⟨t0, Finset.mem_univ _⟩`. Establish `hyt : y ⟨(), t⟩ ≠ 0`. Introduce `h0`. Establish `h1` using `ht t0 (Finset.mem_univ _)`. Rewrite `h1` using `[h0, map_zero]`.

Conclude with `ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))`. Establish `hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W`. Introduce `u`. Apply `W.mem_of_valuation_le_one` to reduce the goal to its premises. Rewrite using `[map_div₀]`.

Conclude with `(div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr (ht u (Finset.mem_univ _))`. Establish `hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W`. Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`.

Take `⟨⟨⟨⟩, u⟩, rfl⟩` from `hx`. Conclude with `hratio u`. Consider the case `algebraMap r => rw [eq_intCast]`. Conclude with `intCast_mem W r`. Consider the case `add x z _ _ hx hz => exact add_mem hx hz`.

Consider the case `mul x z _ _ hx hz => exact mul_mem hx hz`. Establish `hinv : y ⟨(), t⟩ ^ e / g ∈ W` using `hW W hBW hBunit t`. Establish `hgt : g / y ⟨(), t⟩ ^ e ∈ W` using `hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)`. Establish `hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1`. Establish `h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1`.

Rewrite using `[← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by`. Clear denominators, using `[pow_ne_zero e hyt]]` for the nonvanishing conditions. Conclude with `map_one _`. Establish `h2` using `(W.valuation_le_one_iff _).mpr hinv`. Establish `h3` using `(W.valuation_le_one_iff _).mpr hgt`.

Assume the negation of the conclusion as `hne`. Establish `h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)`. Conclude with `ne_of_lt h4 h1`. Establish `hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 → y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t')`. Introduce `u t' ht'`.

Establish `e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e = (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1)`. Rewrite using `[div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]`. Rewrite using `[e1]`. Conclude with `mul_mem (ClosedPointAffineChart.ratio_mem y t' u) (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)`. Establish `hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e` using `mul_pow_sub_one (by omega) _`.

Take `⟨s0, hs0, hs0B⟩` from `ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)`. Establish `ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m`. Introduce `hmem`. Establish `h1` using `hBlt _ hmem`. Express the relevant statement in the definitionally equal form `W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1`.

Rewrite `h1` using `[map_mul, hpow, hval, hBunit s0 hs0, one_mul]`. Conclude with `lt_irrefl _ h1`. Use `⟨t, hyt, fun u => ?_⟩` and prove the remaining obligations. Take `⟨su, hsu, hsuB⟩` from `ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)`. Use `⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩` and prove the remaining obligations.

Break down `hm.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `hsu h`. Conclude with `ha0 h`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem ClosedPointChart.proof (hU : ClosedPointUnitSection.Statement) : ClosedPointChart.Statement := by
  intro T _ K' _ _ y hy m hm
  obtain ⟨e, g, he, hg0, hgL, hW⟩ := hU T K' y hy m hm
  have := hm.isPrime
  obtain ⟨W, hBW, hBunit, hBlt⟩ := ClosedPointUnitSection.exists_valuationSubring (curveRing y) m
  obtain ⟨t0, ht0⟩ := CurveAffineCharts.exists_chart y hy
  obtain ⟨t, -, ht⟩ := Finset.exists_max_image Finset.univ (fun u => W.valuation (y ⟨(), u⟩))
    ⟨t0, Finset.mem_univ _⟩
  have hyt : y ⟨(), t⟩ ≠ 0 := by
    intro h0
    have h1 := ht t0 (Finset.mem_univ _)
    rw [h0, map_zero] at h1
    exact ht0 ((Valuation.zero_iff _).mp (le_antisymm h1 zero_le))
  have hratio : ∀ u, y ⟨(), u⟩ / y ⟨(), t⟩ ∈ W := by
    intro u
    apply W.mem_of_valuation_le_one
    rw [map_div₀]
    exact (div_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hyt))).mpr
      (ht u (Finset.mem_univ _))
  have hchartW : ∀ x ∈ chartRingZ y (fun _ => t), x ∈ W := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
      exact hratio u
    | algebraMap r => rw [eq_intCast]; exact intCast_mem W r
    | add x z _ _ hx hz => exact add_mem hx hz
    | mul x z _ _ hx hz => exact mul_mem hx hz
  have hinv : y ⟨(), t⟩ ^ e / g ∈ W := hW W hBW hBunit t
  have hgt : g / y ⟨(), t⟩ ^ e ∈ W :=
    hchartW _ (ClosedPointAffineChart.div_pow_mem_of_mem_chartLat y hgL t hyt)
  have hval : W.valuation (y ⟨(), t⟩ ^ e / g) = 1 := by
    have h1 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) = 1 := by
      rw [← map_mul, show y ⟨(), t⟩ ^ e / g * (g / y ⟨(), t⟩ ^ e) = 1 by
        field_simp [pow_ne_zero e hyt]]
      exact map_one _
    have h2 := (W.valuation_le_one_iff _).mpr hinv
    have h3 := (W.valuation_le_one_iff _).mpr hgt
    by_contra hne
    have h4 : W.valuation (y ⟨(), t⟩ ^ e / g) * W.valuation (g / y ⟨(), t⟩ ^ e) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' h3) (lt_of_le_of_ne h2 hne)
    exact ne_of_lt h4 h1
  have hmon : ∀ u t' : T, y ⟨(), t'⟩ ≠ 0 →
      y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e ∈ chartRingZ y (fun _ => t') := by
    intro u t' ht'
    have e1 : y ⟨(), u⟩ * y ⟨(), t⟩ ^ (e - 1) / y ⟨(), t'⟩ ^ e =
        (y ⟨(), u⟩ / y ⟨(), t'⟩) * (y ⟨(), t⟩ / y ⟨(), t'⟩) ^ (e - 1) := by
      rw [div_pow, div_mul_div_comm, mul_pow_sub_one (by omega : e ≠ 0)]
    rw [e1]
    exact mul_mem (ClosedPointAffineChart.ratio_mem y t' u)
      (pow_mem (ClosedPointAffineChart.ratio_mem y t' t) _)
  have hpow : y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) = y ⟨(), t⟩ ^ e := mul_pow_sub_one (by omega) _
  obtain ⟨s0, hs0, hs0B⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon t)
  have ha0 : (⟨_, hs0B⟩ : curveRing y) ∉ m := by
    intro hmem
    have h1 := hBlt _ hmem
    change W.valuation ((s0 : K') * (y ⟨(), t⟩ * y ⟨(), t⟩ ^ (e - 1) / g)) < 1 at h1
    rw [map_mul, hpow, hval, hBunit s0 hs0, one_mul] at h1
    exact lt_irrefl _ h1
  refine ⟨t, hyt, fun u => ?_⟩
  obtain ⟨su, hsu, hsuB⟩ :=
    ClosedPointAffineChart.exists_mul_div_mem_curveRing y hm hg0 hgL hW (hmon u)
  refine ⟨⟨_, hsuB⟩ * s0, su * ⟨_, hs0B⟩, fun hmem => ?_, ?_⟩
  · rcases hm.isPrime.mem_or_mem hmem with h | h
    · exact hsu h
    · exact ha0 h
  · push_cast
    field_simp

end

end GroundTheory.Heights₂.Heights
