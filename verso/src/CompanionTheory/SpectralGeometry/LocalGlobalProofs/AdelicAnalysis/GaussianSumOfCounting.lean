import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic

noncomputable def wt (c : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else Real.exp (-(c * 4 ^ j / 4))

/- English proof (translation)
Unfold `wt`. Use `split_ifs`. Conclude with `zero_le_one`. Conclude with `(Real.exp_pos _).le`.
-/
lemma wt_nonneg (c : ℝ) (j : ℕ) : 0 ≤ wt c j := by
  unfold wt; split_ifs
  · exact zero_le_one
  · exact (Real.exp_pos _).le

/- English proof (translation)
Establish `hex : ∃ j : ℕ, u ≤ 2 ^ j`. Take `⟨j, hj⟩` from `pow_unbounded_of_one_lt u (one_lt_two : (1 : ℝ) < 2)`. Conclude with `⟨j, hj.le⟩`. Use `⟨Nat.find hex, Nat.find_spec hex, ?_⟩` and prove the remaining obligations. Break down `hj : Nat.find hex with _ | k` into its components or cases.

Simplify using `only [wt, if_true]`. Rewrite using `[Real.exp_le_one_iff]`. Establish `: 0 ≤ c * u ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlt : ¬ u ≤ 2 ^ k` using `Nat.find_min hex (by omega) push_neg at hlt`.

Establish `hsq : (4 : ℝ) ^ k ≤ u ^ 2`. Establish `h1 : ((2 : ℝ) ^ k) ^ 2 ≤ u ^ 2` using `pow_le_pow_left₀ (by positivity) hlt.le 2`. Establish `h2 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k`. Rewrite using `[← pow_mul, mul_comm, pow_mul]`. Evaluate the numerical expressions.

Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [wt, Nat.succ_ne_zero, if_false]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `h3 : c * 4 ^ (k + 1) / 4 = c * 4 ^ k` using `by rw [pow_succ]; ring`. Rewrite using `[h3]`.

Use `mul_le_mul_of_nonneg_left hsq hc.le` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma exists_dyadic {c u : ℝ} (hc : 0 < c) (hu : 0 ≤ u) :
    ∃ j : ℕ, u ≤ 2 ^ j ∧ Real.exp (-(c * u ^ 2)) ≤ wt c j := by
  classical
  have hex : ∃ j : ℕ, u ≤ 2 ^ j := by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt u (one_lt_two : (1 : ℝ) < 2)
    exact ⟨j, hj.le⟩
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hj : Nat.find hex with _ | k
  · simp only [wt, if_true]
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * u ^ 2 := by positivity
    linarith
  · have hlt : ¬ u ≤ 2 ^ k := Nat.find_min hex (by omega)
    push_neg at hlt
    have hsq : (4 : ℝ) ^ k ≤ u ^ 2 := by
      have h1 : ((2 : ℝ) ^ k) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hlt.le 2
      have h2 : ((2 : ℝ) ^ k) ^ 2 = 4 ^ k := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
      linarith
    simp only [wt, Nat.succ_ne_zero, if_false]
    apply Real.exp_le_exp.mpr
    have h3 : c * 4 ^ (k + 1) / 4 = c * 4 ^ k := by rw [pow_succ]; ring
    rw [h3]
    have := mul_le_mul_of_nonneg_left hsq hc.le
    linarith

/- English proof (translation)
Use `set K : ℝ := ((n + 1).factorial : ℝ) * (4 / c) ^ (n + 1) with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hgeo : Summable fun j : ℕ => (K + 1) * ((1 : ℝ) / 4) ^ j` using `(summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _`. Use `Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg c j) (by positivity)) ?_ hgeo` and prove the remaining obligations. Introduce `j`.

Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Simplify using `[wt]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj0 : j ≠ 0` using `by omega`. Simplify using `only [wt, hj0, if_false]`.

Use `set y : ℝ := 4 ^ j with hy`. Establish `hy0 : 0 < y` using `by positivity`. Establish `hx0 : 0 ≤ c * y / 4` using `by positivity`. Establish `hb` using `Real.pow_div_factorial_le_exp (c * y / 4) hx0 (n + 1)`. Establish `hfac : (0 : ℝ) < ((n + 1).factorial : ℝ)` using `by positivity`.

Establish `hxp : 0 < (c * y / 4) ^ (n + 1)` using `by positivity`. Establish `hexp : Real.exp (-(c * y / 4)) ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1)`. Rewrite using `[Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]`. Conclude with `hb`. Establish `hswap : ((4 : ℝ) ^ n) ^ j = y ^ n` using `by rw [hy, ← pow_mul, ← pow_mul, mul_comm]`.

Rewrite using `[hswap]`. Combine the equalities or inequalities in the displayed calculation. Establish `: ((1 : ℝ) / 4) ^ j = y⁻¹` using `by rw [hy, one_div, inv_pow]`. Rewrite using `[this, hK, div_pow, div_pow, mul_pow, pow_succ y n]`. Clear the denominators using the available nonvanishing facts.

Use `_ ≤ (K + 1) * (1 / 4) ^ j := by`. Apply `mul_le_mul_of_nonneg_right (by linarith) (by positivity)` to reduce the goal to its premises.
-/
lemma summable_wt {c : ℝ} (hc : 0 < c) (n : ℕ) :
    Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j := by
  set K : ℝ := ((n + 1).factorial : ℝ) * (4 / c) ^ (n + 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hgeo : Summable fun j : ℕ => (K + 1) * ((1 : ℝ) / 4) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (wt_nonneg c j) (by positivity)) ?_ hgeo
  intro j
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [wt]; linarith
  · have hj0 : j ≠ 0 := by omega
    simp only [wt, hj0, if_false]
    set y : ℝ := 4 ^ j with hy
    have hy0 : 0 < y := by positivity
    have hx0 : 0 ≤ c * y / 4 := by positivity
    have hb := Real.pow_div_factorial_le_exp (c * y / 4) hx0 (n + 1)
    have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by positivity
    have hxp : 0 < (c * y / 4) ^ (n + 1) := by positivity
    have hexp : Real.exp (-(c * y / 4)) ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity), inv_div]
      exact hb
    have hswap : ((4 : ℝ) ^ n) ^ j = y ^ n := by rw [hy, ← pow_mul, ← pow_mul, mul_comm]
    rw [hswap]
    calc Real.exp (-(c * y / 4)) * y ^ n
        ≤ ((n + 1).factorial : ℝ) / (c * y / 4) ^ (n + 1) * y ^ n :=
          mul_le_mul_of_nonneg_right hexp (by positivity)
      _ = K * (1 / 4) ^ j := by
          have : ((1 : ℝ) / 4) ^ j = y⁻¹ := by rw [hy, one_div, inv_pow]
          rw [this, hK, div_pow, div_pow, mul_pow, pow_succ y n]
          field_simp
      _ ≤ (K + 1) * (1 / 4) ^ j := by
          apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/- English proof (translation)
Establish `hs₀ : 0 < Real.sqrt t₀` using `Real.sqrt_pos.mpr ht₀`. Establish `hs : 0 < Real.sqrt t` using `Real.sqrt_pos.mpr (ht₀.trans_le ht)`. Establish `hle : Real.sqrt t₀ ≤ Real.sqrt t` using `Real.sqrt_le_sqrt ht`. Use `set A : ℝ := ((2 : ℝ) ^ j) ^ n with hA`. Use `set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB`.

Use `set B₀ : ℝ := (Real.sqrt t₀ ^ n)⁻¹ with hB₀`. Establish `hA1 : 1 ≤ A` using `one_le_pow₀ (one_le_pow₀ (by norm_num))`. Establish `hBpos : 0 < B` using `by positivity`. Establish `hBB : B ≤ B₀` using `inv_anti₀ (by positivity) (pow_le_pow_left₀ hs₀.le hle n)`. Establish `e1 : (2 ^ j / Real.sqrt t) ^ n = A * B`.

Rewrite using `[div_pow, hA, hB, div_eq_mul_inv]`. Establish `e2 : (2 ^ j / Real.sqrt t) ^ (2 * n) = (A * B) ^ 2`. Rewrite using `[mul_comm 2 n, pow_mul, e1]`. Establish `e3 : ((4 : ℝ) ^ n) ^ j = A ^ 2`. Rewrite using `[hA, ← pow_mul, ← pow_mul, ← pow_mul]`.

Establish `: (4 : ℝ) = 2 ^ 2` using `by norm_num`. Rewrite using `[this, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, e3]`.

Establish `h1 : A * B ≤ A ^ 2 * B`. Apply `mul_le_mul_of_nonneg_right _ hBpos.le` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : (A * B) ^ 2 ≤ A ^ 2 * (B₀ * B)`. Establish `: (A * B) ^ 2 = A ^ 2 * (B * B)` using `by ring`.

Rewrite using `[this]`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_right hBB hBpos.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma radius_bound (n j : ℕ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) ≤
      ((4 : ℝ) ^ n) ^ j * ((1 + (Real.sqrt t₀ ^ n)⁻¹) * (Real.sqrt t ^ n)⁻¹) := by
  have hs₀ : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ht₀.trans_le ht)
  have hle : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  set A : ℝ := ((2 : ℝ) ^ j) ^ n with hA
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set B₀ : ℝ := (Real.sqrt t₀ ^ n)⁻¹ with hB₀
  have hA1 : 1 ≤ A := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hBpos : 0 < B := by positivity
  have hBB : B ≤ B₀ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hs₀.le hle n)
  have e1 : (2 ^ j / Real.sqrt t) ^ n = A * B := by
    rw [div_pow, hA, hB, div_eq_mul_inv]
  have e2 : (2 ^ j / Real.sqrt t) ^ (2 * n) = (A * B) ^ 2 := by
    rw [mul_comm 2 n, pow_mul, e1]
  have e3 : ((4 : ℝ) ^ n) ^ j = A ^ 2 := by
    rw [hA, ← pow_mul, ← pow_mul, ← pow_mul]
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]; congr 1; ring
  rw [e1, e2, e3]
  have h1 : A * B ≤ A ^ 2 * B := by
    apply mul_le_mul_of_nonneg_right _ hBpos.le
    nlinarith
  have h2 : (A * B) ^ 2 ≤ A ^ 2 * (B₀ * B) := by
    have : (A * B) ^ 2 = A ^ 2 * (B * B) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hBB hBpos.le
  nlinarith

/- English proof (translation)
Distinguish the cases in `hp : p x`. Establish `hq : 0 < Real.sqrt t` using `Real.sqrt_pos.mpr ht`. Take `⟨j, hj, hexp⟩` from `exists_dyadic (c := c) (u := Real.sqrt t * s x) hc (mul_nonneg hq.le (hs x))`. Establish `hmem : x ∈ {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t}` using `⟨hp, by rw [le_div_iff₀ hq, mul_comm]; exact hj⟩`. Establish `heq : c * (Real.sqrt t * s x) ^ 2 = c * t * s x ^ 2`.

Rewrite using `[mul_pow, Real.sq_sqrt ht.le]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hexp` using `[heq]`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x | p x} from hp)]`. Use `le_trans ?_ (ENNReal.le_tsum j)` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem hmem, mul_one]`. Conclude with `ENNReal.ofReal_le_ofReal hexp`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x | p x} from hp)]`. Conclude with `zero_le`.
-/
lemma gaussian_le_tsum {X : Type} (c t : ℝ) (hc : 0 < c) (ht : 0 < t) (s : X → ℝ) (p : X → Prop)
    (hs : ∀ x, 0 ≤ s x) (x : X) :
    Set.indicator {x | p x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) *
        Set.indicator {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
  classical
  by_cases hp : p x
  · have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
    obtain ⟨j, hj, hexp⟩ := exists_dyadic (c := c) (u := Real.sqrt t * s x) hc
      (mul_nonneg hq.le (hs x))
    have hmem : x ∈ {x | p x ∧ s x ≤ 2 ^ j / Real.sqrt t} :=
      ⟨hp, by rw [le_div_iff₀ hq, mul_comm]; exact hj⟩
    have heq : c * (Real.sqrt t * s x) ^ 2 = c * t * s x ^ 2 := by
      rw [mul_pow, Real.sq_sqrt ht.le]; ring
    rw [heq] at hexp
    rw [Set.indicator_of_mem (show x ∈ {x | p x} from hp)]
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hmem, mul_one]
    exact ENNReal.ofReal_le_ofReal hexp
  · rw [Set.indicator_of_notMem (show x ∉ {x | p x} from hp)]
    exact zero_le

/- English proof (translation)
Introduce `X Ω _ _ Pr s p hsm hpm hs0 hcount t ht`. Establish `htpos : 0 < t` using `ht₀.trans_le ht`. Establish `hq : 0 < Real.sqrt t` using `Real.sqrt_pos.mpr htpos`. Use `set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB`. Use `set D : ℝ := 1 + (Real.sqrt t₀ ^ n)⁻¹ with hD`.

Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hD0 : 0 ≤ D` using `by positivity`. Use `set E : ℝ := |C| * D * B with hE`. Establish `hE0 : 0 ≤ E` using `by positivity`. Establish `hmeas : ∀ j : ℕ, Measurable fun ω => ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x`.

Introduce `j`. Use `Measurable.ennreal_tsum fun x => ?_` and prove the remaining obligations. Establish `hset : MeasurableSet {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t}` using `(hpm x).inter (measurableSet_le (hsm x) measurable_const)`. Establish `heq : (fun ω => Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x) = Set.indicator {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞))`. Use function extensionality and compare the values at `ω`.

Distinguish the cases in `h : p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t`. Rewrite using `[Set.indicator_of_mem (show x ∈ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h), Set.indicator_of_mem (show ω ∈ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]`. Rewrite using `[Set.indicator_of_notMem (show x ∉ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h), Set.indicator_of_notMem (show ω ∉ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]`. Rewrite using `[heq]`. Conclude with `measurable_const.indicator hset`.

Establish `hpt : ∀ ω, ∑' x, Set.indicator {x | p ω x} (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x`. Introduce `ω`. Combine the equalities or inequalities in the displayed calculation. Establish `hterm : ∀ j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E)`. Introduce `j`.

Establish `hR : (0 : ℝ) < 2 ^ j / Real.sqrt t` using `by positivity`. Establish `hr` using `radius_bound n j ht₀ ht`. Establish `hb : C * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) ≤ ((4 : ℝ) ^ n) ^ j * E`. Establish `h0 : 0 ≤ (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(hcount _ hR).trans (ENNReal.ofReal_le_ofReal hb)`. Use `_ = _ := by`. Rewrite using `[← ENNReal.ofReal_mul (wt_nonneg c j), mul_assoc]`. Establish `hsum : Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j * E` using `(summable_wt hc n).mul_right E`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `lintegral_const_mul _ (hmeas j)`. Use `_ ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) := ENNReal.tsum_le_tsum hterm`.

Use `_ = ENNReal.ofReal (∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j * E) := (ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (mul_nonneg (wt_nonneg c j) (by positivity)) hE0) hsum).symm`. Use `_ = _ := by`. Rewrite using `[tsum_mul_right, hE]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gaussian_sum_le (n : ℕ) (c t₀ C : ℝ) (hc : 0 < c) (ht₀ : 0 < t₀) :
    ∀ (X Ω : Type) [MeasurableSpace Ω] [Countable X] (Pr : Measure Ω)
      (s : Ω → X → ℝ) (p : Ω → X → Prop), (∀ x, Measurable fun ω => s ω x) →
      (∀ x, MeasurableSet {ω | p ω x}) → (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal ((|C| * (1 + (Real.sqrt t₀ ^ n)⁻¹) *
          ∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j) * (Real.sqrt t ^ n)⁻¹) := by
  intro X Ω _ _ Pr s p hsm hpm hs0 hcount t ht
  have htpos : 0 < t := ht₀.trans_le ht
  have hq : 0 < Real.sqrt t := Real.sqrt_pos.mpr htpos
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set D : ℝ := 1 + (Real.sqrt t₀ ^ n)⁻¹ with hD
  have hB0 : 0 ≤ B := by positivity
  have hD0 : 0 ≤ D := by positivity
  set E : ℝ := |C| * D * B with hE
  have hE0 : 0 ≤ E := by positivity
  have hmeas : ∀ j : ℕ, Measurable fun ω => ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro j
    refine Measurable.ennreal_tsum fun x => ?_
    have hset : MeasurableSet {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} :=
      (hpm x).inter (measurableSet_le (hsm x) measurable_const)
    have heq : (fun ω => Set.indicator {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t}
        (fun _ => (1 : ℝ≥0∞)) x) =
        Set.indicator {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) := by
      funext ω
      classical
      by_cases h : p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t
      · rw [Set.indicator_of_mem (show x ∈ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_mem (show ω ∈ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
      · rw [Set.indicator_of_notMem (show x ∉ {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h),
          Set.indicator_of_notMem (show ω ∉ {ω | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} from h)]
    rw [heq]
    exact measurable_const.indicator hset
  have hpt : ∀ ω, ∑' x, Set.indicator {x | p ω x}
      (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ≤
      ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
        {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x := by
    intro ω
    calc _ ≤ ∑' x, ∑' j : ℕ, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_le_tsum fun x =>
            gaussian_le_tsum c t hc htpos (s ω) (p ω) (hs0 ω) x
      _ = ∑' j : ℕ, ∑' x, ENNReal.ofReal (wt c j) * Set.indicator
            {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x :=
          ENNReal.tsum_comm
      _ = _ := by simp_rw [ENNReal.tsum_mul_left]
  have hterm : ∀ j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
      {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤
      ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) := by
    intro j
    have hR : (0 : ℝ) < 2 ^ j / Real.sqrt t := by positivity
    have hr := radius_bound n j ht₀ ht
    have hb : C * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) ≤
        ((4 : ℝ) ^ n) ^ j * E := by
      have h0 : 0 ≤ (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) := by positivity
      calc _ ≤ |C| * ((2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n)) :=
            mul_le_mul_of_nonneg_right (le_abs_self C) h0
        _ ≤ |C| * (((4 : ℝ) ^ n) ^ j * (D * B)) :=
            mul_le_mul_of_nonneg_left hr (abs_nonneg C)
        _ = _ := by rw [hE]; ring
    calc _ ≤ ENNReal.ofReal (wt c j) * ENNReal.ofReal (((4 : ℝ) ^ n) ^ j * E) := by
          gcongr
          exact (hcount _ hR).trans (ENNReal.ofReal_le_ofReal hb)
      _ = _ := by
          rw [← ENNReal.ofReal_mul (wt_nonneg c j), mul_assoc]
  have hsum : Summable fun j : ℕ => wt c j * ((4 : ℝ) ^ n) ^ j * E :=
    (summable_wt hc n).mul_right E
  calc _ ≤ ∫⁻ ω, ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_mono hpt
    _ = ∑' j : ℕ, ∫⁻ ω, ENNReal.ofReal (wt c j) * ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr :=
        lintegral_tsum fun j => ((hmeas j).const_mul _).aemeasurable
    _ = ∑' j : ℕ, ENNReal.ofReal (wt c j) * ∫⁻ ω, ∑' x, Set.indicator
          {x | p ω x ∧ s ω x ≤ 2 ^ j / Real.sqrt t} (fun _ => (1 : ℝ≥0∞)) x ∂Pr := by
        congr 1; funext j
        exact lintegral_const_mul _ (hmeas j)
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' j : ℕ, wt c j * ((4 : ℝ) ^ n) ^ j * E) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun j => mul_nonneg (mul_nonneg (wt_nonneg c j) (by positivity)) hE0) hsum).symm
    _ = _ := by
        rw [tsum_mul_right, hE]
        congr 1
        ring

/- English proof (translation)
Introduce `n c t₀ C hc ht₀` and use `⟨_, gaussian_sum_le n c t₀ C hc ht₀⟩`.
-/
theorem gaussian_sum_of_counting :
    ∀ (n : ℕ) (c t₀ C : ℝ), 0 < c → 0 < t₀ → ∃ C' : ℝ, ∀ (X Ω : Type) [MeasurableSpace Ω]
      [Countable X] (Pr : Measure Ω) (s : Ω → X → ℝ) (p : Ω → X → Prop),
      (∀ x, Measurable fun ω => s ω x) → (∀ x, MeasurableSet {ω | p ω x}) →
      (∀ ω x, 0 ≤ s ω x) →
      (∀ R : ℝ, 0 < R → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x ∧ s ω x ≤ R}
          (fun _ => (1 : ℝ≥0∞)) x ∂Pr ≤ ENNReal.ofReal (C * (R ^ n + R ^ (2 * n)))) →
      ∀ t : ℝ, t₀ ≤ t → ∫⁻ ω, ∑' x, Set.indicator {x | p ω x}
          (fun x => ENNReal.ofReal (Real.exp (-(c * t * s ω x ^ 2)))) x ∂Pr ≤
        ENNReal.ofReal (C' * (Real.sqrt t ^ n)⁻¹) :=
  fun n c t₀ C hc ht₀ => ⟨_, gaussian_sum_le n c t₀ C hc ht₀⟩

end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
