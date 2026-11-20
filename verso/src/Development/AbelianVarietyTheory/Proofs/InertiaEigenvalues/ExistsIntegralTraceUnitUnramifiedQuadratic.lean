import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.TraceUnit

section Ultra
variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Simplify `IsUltrametricDist.norm_add_le_max x (-y)` using `[sub_eq_add_neg, norm_neg]`.
-/
theorem norm_sub_le_max_of_ultra (x y : K) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)

/- English proof (translation)
Establish `h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y)` using `by ring`. Rewrite using `[h1, norm_mul]`. Establish `h2 : ‖x + y‖ ≤ 1` using `(IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_sq_sub_sq_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    ‖x ^ 2 - y ^ 2‖ ≤ ‖x - y‖ := by
  have h1 : x ^ 2 - y ^ 2 = (x - y) * (x + y) := by ring
  rw [h1, norm_mul]
  have h2 : ‖x + y‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  calc ‖x - y‖ * ‖x + y‖ ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖x - y‖ := mul_one _

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2 ^ k) ^ 2` using `fun z => by rw [pow_succ, pow_mul]`. Rewrite using `[e, e]`.

Conclude with `(norm_sq_sub_sq_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ih`.
-/
theorem norm_pow_two_pow_sub_le {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ 2 ^ k - y ^ 2 ^ k‖ ≤ ‖x - y‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2 ^ k) ^ 2 := fun z => by rw [pow_succ, pow_mul]
    rw [e, e]
    exact (norm_sq_sub_sq_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx)
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy)).trans ih

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hle : ‖x - y‖ ≤ 1` using `(norm_sub_le_max_of_ultra x y).trans (max_le hx hy)`. Establish `heq : ‖x - y‖ = 1` using `le_antisymm hle hc`. Establish `e : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * y * (x - y)` using `by ring`.

Establish `hA : ‖(x - y) ^ 2‖ = 1` using `by rw [norm_pow, heq, one_pow]`. Establish `hB : ‖2 * y * (x - y)‖ < 1`. Rewrite using `[norm_mul, norm_mul, heq, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖(x - y) ^ 2 + 2 * y * (x - y)‖ = 1`.

Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hA]; exact hB.ne'), hA]`. Conclude with `max_eq_left hB.le`. Rewrite `h` using `[e, h3]`. Conclude with `lt_irrefl _ h`.
-/
theorem norm_sub_lt_one_of_sq {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1)
    (h : ‖x ^ 2 - y ^ 2‖ < 1) : ‖x - y‖ < 1 := by
  by_contra hc
  push_neg at hc
  have hle : ‖x - y‖ ≤ 1 := (norm_sub_le_max_of_ultra x y).trans (max_le hx hy)
  have heq : ‖x - y‖ = 1 := le_antisymm hle hc
  have e : x ^ 2 - y ^ 2 = (x - y) ^ 2 + 2 * y * (x - y) := by ring
  have hA : ‖(x - y) ^ 2‖ = 1 := by rw [norm_pow, heq, one_pow]
  have hB : ‖2 * y * (x - y)‖ < 1 := by
    rw [norm_mul, norm_mul, heq, mul_one]
    calc ‖(2 : K)‖ * ‖y‖ ≤ ‖(2 : K)‖ * 1 := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact h2
  have h3 : ‖(x - y) ^ 2 + 2 * y * (x - y)‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hA]; exact hB.ne'), hA]
    exact max_eq_left hB.le
  rw [e, h3] at h
  exact lt_irrefl _ h

/- English proof (translation)
Proceed by induction on `k generalizing x y with`. Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Establish `e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2) ^ 2 ^ k` using `fun z => by rw [pow_succ', pow_mul]`. Rewrite `h` using `[e, e]`.

Establish `hx2 : ‖x ^ 2‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx`. Establish `hy2 : ‖y ^ 2‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy`. Conclude with `norm_sub_lt_one_of_sq h2 hx hy (ih hx2 hy2 h)`.
-/
theorem norm_sub_lt_one_of_pow {x y : K} (h2 : ‖(2 : K)‖ < 1) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ)
    (h : ‖x ^ 2 ^ k - y ^ 2 ^ k‖ < 1) : ‖x - y‖ < 1 := by
  induction k generalizing x y with
  | zero => simpa using h
  | succ k ih =>
    have e : ∀ z : K, z ^ 2 ^ (k + 1) = (z ^ 2) ^ 2 ^ k := fun z => by rw [pow_succ', pow_mul]
    rw [e, e] at h
    have hx2 : ‖x ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
    have hy2 : ‖y ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    exact norm_sub_lt_one_of_sq h2 hx hy (ih hx2 hy2 h)

/- English proof (translation)
Establish `hmem : ∀ n : ℕ, w ^ 2 ^ n ∈ Metric.closedBall (0 : K) 1` using `fun n => by`. Rewrite using `[mem_closedBall_zero_iff, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hw`. Take `⟨a, -, φ, hφ, hlim⟩` from `(isCompact_closedBall (0 : K) 1).tendsto_subseq hmem`. Take `⟨N, hN⟩` from `(Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)`.

Use `⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩` and prove the remaining obligations. Establish `h1 : dist (w ^ 2 ^ φ N) a < 1 / 2` using `hN N le_rfl`. Establish `h2 : dist (w ^ 2 ^ φ (N + 1)) a < 1 / 2` using `hN (N + 1) (Nat.le_succ N)`. Rewrite using `[← dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_pow_close [ProperSpace K] {w : K} (hw : ‖w‖ ≤ 1) :
    ∃ i j : ℕ, i < j ∧ ‖w ^ 2 ^ i - w ^ 2 ^ j‖ < 1 := by
  have hmem : ∀ n : ℕ, w ^ 2 ^ n ∈ Metric.closedBall (0 : K) 1 := fun n => by
    rw [mem_closedBall_zero_iff, norm_pow]; exact pow_le_one₀ (norm_nonneg _) hw
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : K) 1).tendsto_subseq hmem
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (1 / 2) (by norm_num)
  refine ⟨φ N, φ (N + 1), hφ (Nat.lt_succ_self N), ?_⟩
  have h1 : dist (w ^ 2 ^ φ N) a < 1 / 2 := hN N le_rfl
  have h2 : dist (w ^ 2 ^ φ (N + 1)) a < 1 / 2 := hN (N + 1) (Nat.le_succ N)
  rw [← dist_eq_norm]
  calc dist (w ^ 2 ^ φ N) (w ^ 2 ^ φ (N + 1)) ≤ dist (w ^ 2 ^ φ N) a + dist a (w ^ 2 ^ φ (N + 1)) :=
        dist_triangle _ _ _
    _ < 1 / 2 + 1 / 2 := add_lt_add h1 (by rw [dist_comm]; exact h2)
    _ = 1 := by norm_num

end Ultra

/- English proof (translation)
Introduce `F E _ _ _ _ hU htr`. Use `haveI : IsUltrametricDist F := hU.ultraF`. Use `haveI : IsUltrametricDist E := hU.ultraE`. Use `haveI : LocallyCompactSpace F := hU.lcF`. Use `haveI : LocallyCompactSpace E := hU.lcE`.

Use `haveI : CharZero F := hU.charZero`. Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`. Establish `h20 : (2 : E) ≠ 0`. Rewrite using `[← map_ofNat (algebraMap F E) 2]`.

Conclude with `(map_ne_zero _).2 two_ne_zero`. Establish `h2le : ‖(2 : E)‖ ≤ 1`. Use `IsUltrametricDist.norm_natCast_le_one E 2` as an intermediate fact. Simplify using `using this`. Break down `h2le.lt_or_eq with h2 | h2` into its components or cases.

Use `swap`. Use `⟨2⁻¹, by rw [norm_inv, h2, inv_one], ?_⟩` and prove the remaining obligations. Establish `hs : star (2⁻¹ : E) = 2⁻¹`. Establish `: (2⁻¹ : E) = algebraMap F E 2⁻¹` using `by rw [map_inv₀, map_ofNat]`. Rewrite using `[this, hU.star_fix]`.

Rewrite using `[← norm_algebraMap' E, htr, hs, ← two_mul, mul_inv_cancel₀ h20, norm_one]`. Take `⟨y, hy⟩` from `hU.star_ne`. Establish `hyF : ∀ a : F, y - algebraMap F E a ≠ 0` using `fun a h => hy (by rw [sub_eq_zero.1 h, hU.star_fix])`. Establish `hcont : Continuous fun a : F => ‖y - algebraMap F E a‖` using `by fun_prop`. Take `⟨x, -, hx⟩` from `(isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn (Metric.nonempty_closedBall.2 (norm_nonneg _)) hcont.continuousOn`.

Establish `hmin : ∀ a : F, ‖y - algebraMap F E x‖ ≤ ‖y - algebraMap F E a‖`. Introduce `a`. Establish `h0 : ‖y - algebraMap F E x‖ ≤ ‖y‖`. Use `isMinOn_iff.1 hx 0 (Metric.mem_closedBall_self (norm_nonneg y))` as an intermediate fact. Simplify using `using this`.

Distinguish the cases in `ha : ‖a‖ ≤ ‖y‖`. Conclude with `isMinOn_iff.1 hx a (mem_closedBall_zero_iff.2 ha)`. Use `push_neg at ha`. Establish `hm : ‖a‖ ≤ max ‖y‖ ‖y - algebraMap F E a‖`. Use `norm_sub_le_max_of_ultra y (y - algebraMap F E a)` as an intermediate fact.

Rewrite `this` using `[sub_sub_cancel, norm_algebraMap']`. Then use the resulting hypothesis. Apply the tactic sequence `rcases le_max_iff.1 hm with h | h <;> linarith`. Take `⟨t, ht⟩` from `hU.unram (y - algebraMap F E x)`. Establish `hd : 0 < ‖y - algebraMap F E x‖` using `norm_pos_iff.2 (hyF x)`. Establish `htE : algebraMap F E t ≠ 0`.

Introduce `h0`. Rewrite `ht` using `[← norm_algebraMap' E t, h0, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set u := (y - algebraMap F E x) * (algebraMap F E t)⁻¹ with hu`. Establish `hu1 : ‖u‖ = 1`.

Rewrite using `[hu, norm_mul, norm_inv, norm_algebraMap', ← ht, mul_inv_cancel₀ hd.ne']`. Establish `hfar : ∀ a : F, 1 ≤ ‖u - algebraMap F E a‖`. Introduce `a`. Establish `e : u - algebraMap F E a = (y - algebraMap F E (x + t * a)) * (algebraMap F E t)⁻¹`. Rewrite using `[hu, map_add, map_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_inv, norm_algebraMap', ← ht, le_mul_inv_iff₀ hd, one_mul]`. Conclude with `hmin _`. Use `⟨u, hu1.le, ?_⟩` and prove the remaining obligations.

Establish `hle : ‖Algebra.trace F E u‖ ≤ 1`. Rewrite using `[← norm_algebraMap' E, htr]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu1.le (by rw [hU.norm_star]; exact hu1.le))`. Use `le_antisymm hle (not_lt.1 fun hs => ?_)` and prove the remaining obligations. Use `set n := u * star u with hn`.

Establish `hnn : star n = n` using `by rw [hn, star_mul, star_star, mul_comm]`. Use `set v : F := -(Algebra.trace F E n / 2) with hvd`. Establish `hv : algebraMap F E v = -n`. Rewrite using `[hvd, map_neg, map_div₀, htr, hnn, map_ofNat]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hvn : ‖algebraMap F E v‖ ≤ 1`. Rewrite using `[hv, norm_neg, hn, norm_mul, hU.norm_star, hu1, one_mul]`. Establish `hq : ‖u ^ 2 - algebraMap F E v‖ < 1`. Establish `e : u ^ 2 - algebraMap F E v = algebraMap F E (Algebra.trace F E u) * u`.

Rewrite using `[hv, htr, hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, norm_mul, norm_algebraMap', hu1, mul_one]`. Conclude with `hs`. Take `⟨i, j, hij, hc⟩` from `exists_pow_close hu1.le`.

Take `⟨m, rfl⟩ : ∃ m, j = i + (m + 1)` from `⟨j - i - 1, by omega⟩`. Establish `e1 : u ^ 2 ^ (i + (m + 1)) = (u ^ 2 ^ (m + 1)) ^ 2 ^ i`. Rewrite using `[← pow_mul, ← pow_add, Nat.add_comm (m + 1) i]`. Rewrite `hc` using `[e1]`. Establish `hpow1 : ‖u ^ 2 ^ (m + 1)‖ ≤ 1` using `by rw [norm_pow, hu1, one_pow]`.

Establish `hA : ‖u - u ^ 2 ^ (m + 1)‖ < 1` using `norm_sub_lt_one_of_pow h2 hu1.le hpow1 i hc`. Establish `e2 : u ^ 2 ^ (m + 1) = (u ^ 2) ^ 2 ^ m` using `by rw [pow_succ', pow_mul]`. Establish `hB : ‖(u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m‖ < 1` using `(norm_pow_two_pow_sub_le (by rw [norm_pow, hu1, one_pow]) hvn m).trans_lt hq`. Establish `hC : ‖u - algebraMap F E (v ^ 2 ^ m)‖ < 1`. Rewrite using `[map_pow]`.

Establish `e3 : u - (algebraMap F E v) ^ 2 ^ m = (u - u ^ 2 ^ (m + 1)) + ((u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m)`. Rewrite using `[e2]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)`.

Combine the linear relations using `[hfar (v ^ 2 ^ m)]`.
-/
theorem exists_trace_unit : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E],
    (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) →
      ∃ u : E, ‖u‖ ≤ 1 ∧ ‖Algebra.trace F E u‖ = 1 := by
  intro F E _ _ _ _ hU htr
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : LocallyCompactSpace F := hU.lcF
  haveI : LocallyCompactSpace E := hU.lcE
  haveI : CharZero F := hU.charZero
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  have h20 : (2 : E) ≠ 0 := by
    rw [← map_ofNat (algebraMap F E) 2]
    exact (map_ne_zero _).2 two_ne_zero
  have h2le : ‖(2 : E)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_natCast_le_one E 2
    simpa using this
  rcases h2le.lt_or_eq with h2 | h2
  swap
  ·
    refine ⟨2⁻¹, by rw [norm_inv, h2, inv_one], ?_⟩
    have hs : star (2⁻¹ : E) = 2⁻¹ := by
      have : (2⁻¹ : E) = algebraMap F E 2⁻¹ := by rw [map_inv₀, map_ofNat]
      rw [this, hU.star_fix]
    rw [← norm_algebraMap' E, htr, hs, ← two_mul, mul_inv_cancel₀ h20, norm_one]

  obtain ⟨y, hy⟩ := hU.star_ne
  have hyF : ∀ a : F, y - algebraMap F E a ≠ 0 := fun a h => hy (by rw [sub_eq_zero.1 h, hU.star_fix])
  have hcont : Continuous fun a : F => ‖y - algebraMap F E a‖ := by fun_prop
  obtain ⟨x, -, hx⟩ := (isCompact_closedBall (0 : F) ‖y‖).exists_isMinOn
    (Metric.nonempty_closedBall.2 (norm_nonneg _)) hcont.continuousOn
  have hmin : ∀ a : F, ‖y - algebraMap F E x‖ ≤ ‖y - algebraMap F E a‖ := by
    intro a
    have h0 : ‖y - algebraMap F E x‖ ≤ ‖y‖ := by
      have := isMinOn_iff.1 hx 0 (Metric.mem_closedBall_self (norm_nonneg y))
      simpa using this
    by_cases ha : ‖a‖ ≤ ‖y‖
    · exact isMinOn_iff.1 hx a (mem_closedBall_zero_iff.2 ha)
    · push_neg at ha
      have hm : ‖a‖ ≤ max ‖y‖ ‖y - algebraMap F E a‖ := by
        have := norm_sub_le_max_of_ultra y (y - algebraMap F E a)
        rwa [sub_sub_cancel, norm_algebraMap'] at this
      rcases le_max_iff.1 hm with h | h <;> linarith
  obtain ⟨t, ht⟩ := hU.unram (y - algebraMap F E x)
  have hd : 0 < ‖y - algebraMap F E x‖ := norm_pos_iff.2 (hyF x)
  have htE : algebraMap F E t ≠ 0 := by
    intro h0
    rw [← norm_algebraMap' E t, h0, norm_zero] at ht
    linarith
  set u := (y - algebraMap F E x) * (algebraMap F E t)⁻¹ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_mul, norm_inv, norm_algebraMap', ← ht, mul_inv_cancel₀ hd.ne']
  have hfar : ∀ a : F, 1 ≤ ‖u - algebraMap F E a‖ := by
    intro a
    have e : u - algebraMap F E a = (y - algebraMap F E (x + t * a)) * (algebraMap F E t)⁻¹ := by
      rw [hu, map_add, map_mul]
      field_simp
      ring
    rw [e, norm_mul, norm_inv, norm_algebraMap', ← ht, le_mul_inv_iff₀ hd, one_mul]
    exact hmin _
  refine ⟨u, hu1.le, ?_⟩
  have hle : ‖Algebra.trace F E u‖ ≤ 1 := by
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu1.le (by rw [hU.norm_star]; exact hu1.le))
  refine le_antisymm hle (not_lt.1 fun hs => ?_)

  set n := u * star u with hn
  have hnn : star n = n := by rw [hn, star_mul, star_star, mul_comm]
  set v : F := -(Algebra.trace F E n / 2) with hvd
  have hv : algebraMap F E v = -n := by
    rw [hvd, map_neg, map_div₀, htr, hnn, map_ofNat]
    field_simp
    ring
  have hvn : ‖algebraMap F E v‖ ≤ 1 := by
    rw [hv, norm_neg, hn, norm_mul, hU.norm_star, hu1, one_mul]
  have hq : ‖u ^ 2 - algebraMap F E v‖ < 1 := by
    have e : u ^ 2 - algebraMap F E v = algebraMap F E (Algebra.trace F E u) * u := by
      rw [hv, htr, hn]; ring
    rw [e, norm_mul, norm_algebraMap', hu1, mul_one]
    exact hs
  obtain ⟨i, j, hij, hc⟩ := exists_pow_close hu1.le
  obtain ⟨m, rfl⟩ : ∃ m, j = i + (m + 1) := ⟨j - i - 1, by omega⟩
  have e1 : u ^ 2 ^ (i + (m + 1)) = (u ^ 2 ^ (m + 1)) ^ 2 ^ i := by
    rw [← pow_mul, ← pow_add, Nat.add_comm (m + 1) i]
  rw [e1] at hc
  have hpow1 : ‖u ^ 2 ^ (m + 1)‖ ≤ 1 := by rw [norm_pow, hu1, one_pow]
  have hA : ‖u - u ^ 2 ^ (m + 1)‖ < 1 := norm_sub_lt_one_of_pow h2 hu1.le hpow1 i hc
  have e2 : u ^ 2 ^ (m + 1) = (u ^ 2) ^ 2 ^ m := by rw [pow_succ', pow_mul]
  have hB : ‖(u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m‖ < 1 :=
    (norm_pow_two_pow_sub_le (by rw [norm_pow, hu1, one_pow]) hvn m).trans_lt hq
  have hC : ‖u - algebraMap F E (v ^ 2 ^ m)‖ < 1 := by
    rw [map_pow]
    have e3 : u - (algebraMap F E v) ^ 2 ^ m =
        (u - u ^ 2 ^ (m + 1)) + ((u ^ 2) ^ 2 ^ m - (algebraMap F E v) ^ 2 ^ m) := by
      rw [e2]; ring
    rw [e3]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)
  linarith [hfar (v ^ 2 ^ m)]

end GlobalTheory.TraceUnit
