import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

/- English proof (translation)
Unfold `ev`. Check the signs of the components of the expression.
-/
theorem weightFunction_nonneg {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (x : M) :
    0 ≤ ev n g ph r x := by
  unfold ev; positivity

/- English proof (translation)
Establish `h0 : ev n g ph r x = 0` using `le_antisymm h (weightFunction_nonneg n g ph r x)`. Unfold `ev at h0`. Establish `hs : (∑ i, ‖g i x‖ ^ 2) = 0`. Break down `div_eq_zero_iff.1 h0 with h1 | h1` into its components or cases. Break down `mul_eq_zero.1 h1 with h2 | h2` into its components or cases.

Conclude with `h2`. Conclude with `absurd h2 (Real.exp_pos _).ne'`. Conclude with `absurd h1 (pow_ne_zero 2 hr)`. Introduce `i`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖g i x‖)).1 hs i (Finset.mem_univ i)` as an intermediate fact.

Simplify using `using this`.
-/
theorem mem_zeroSet_of_weight_nonpos {M : Type*} (n : ℕ) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hr : r ≠ 0) (x : M) (h : ev n g ph r x ≤ 0) : x ∈ zeroSet n g := by
  have h0 : ev n g ph r x = 0 := le_antisymm h (weightFunction_nonneg n g ph r x)
  unfold ev at h0
  have hs : (∑ i, ‖g i x‖ ^ 2) = 0 := by
    rcases div_eq_zero_iff.1 h0 with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (Real.exp_pos _).ne'
    · exact absurd h1 (pow_ne_zero 2 hr)
  intro i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ‖g i x‖)).1 hs i (Finset.mem_univ i)
  simpa using this

/- English proof (translation)
Establish `hgc : ∀ i, Continuous (g i)` using `fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))`. Establish `hpc : Continuous ph`. Use `Smooth.continuous n z hz _ hph` as an intermediate fact. Conclude with `Complex.continuous_re.comp this |>.congr (fun x => by simp)`. Unfold `ev`.

Use `fun_prop`.
-/
theorem continuous_weightFunction {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ)
    (hg : ∀ i, Holo n z (g i)) (hph : SmoothR n z ph) : Continuous (ev n g ph r) := by
  have hgc : ∀ i, Continuous (g i) := fun i => Smooth.continuous n z hz _ (Holo.smooth n z _ (hg i))
  have hpc : Continuous ph := by
    have := Smooth.continuous n z hz _ hph
    exact Complex.continuous_re.comp this |>.congr (fun x => by simp)
  unfold ev
  fun_prop

/- English proof (translation)
Take `⟨e, he, hp⟩` from `exists_chart n z hz p`. Rewrite using `[vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) {p} (measurableSet_singleton p) (Set.singleton_subset_iff.2 hp), Set.image_singleton]`. Establish `: Nonempty (Fin n)` using `⟨⟨0, hn⟩⟩`. Conclude with `measure_singleton _`.
-/
theorem volume_singleton_eq_zero {M : Type*} [TopologicalSpace M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] (n : ℕ) (hn : 1 ≤ n) (z : M → V n)
    (hz : IsLocalHomeomorph z) (p : M) : vol n z {p} = 0 := by
  obtain ⟨e, he, hp⟩ := exists_chart n z hz p
  rw [vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) {p}
    (measurableSet_singleton p) (Set.singleton_subset_iff.2 hp), Set.image_singleton]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  exact measure_singleton _

/- English proof (translation)
Introduce `hxq` and use `Set.disjoint_left.1 ((hL.2 p hp).2.2.2.2 q hq hpq) (subset_closure hx) (subset_closure hxq)`.
-/
theorem not_mem_neighborhood_of_ne {M : Type*} [TopologicalSpace M] (n : ℕ) (g : Fin n → M → ℂ)
    (ph : M → ℝ) (r : ℝ) (W : M → Set M) (m : ℝ) (hL : IsLocalData n g ph r W m)
    {p q x : M} (hp : p ∈ zeroSet n g) (hq : q ∈ zeroSet n g) (hpq : q ≠ p) (hx : x ∈ W p) :
    x ∉ W q := fun hxq =>
  Set.disjoint_left.1 ((hL.2 p hp).2.2.2.2 q hq hpq) (subset_closure hx) (subset_closure hxq)

/- English proof (translation)
Unfold `gt`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.sum_eq_single p (fun q hq hqp => Set.indicator_of_notMem (not_mem_neighborhood_of_ne n g ph r W m hL hp ((hfin.mem_toFinset).1 hq) hqp hx) _) (fun h => absurd ((hfin.mem_toFinset).2 hp) h), Set.indicator_of_mem hx]`.
-/
theorem localExtension_eq_mul_jacobian {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (ph : M → ℝ) (r : ℝ) (c : M → ℂ) (W : M → Set M) (m : ℝ)
    (hL : IsLocalData n g ph r W m) (hfin : (zeroSet n g).Finite)
    {p x : M} (hp : p ∈ zeroSet n g) (hx : x ∈ W p) :
    gt n z g c W x = c p * jac n z g x := by
  unfold gt
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_eq_single p (fun q hq hqp => Set.indicator_of_notMem
      (not_mem_neighborhood_of_ne n g ph r W m hL hp ((hfin.mem_toFinset).1 hq) hqp hx) _)
      (fun h => absurd ((hfin.mem_toFinset).2 hp) h), Set.indicator_of_mem hx]

/- English proof (translation)
Unfold `gt`. Conclude with `finsum_mem_eq_zero_of_forall_eq_zero (fun p hp => Set.indicator_of_notMem (hx p hp) _)`.
-/
theorem localExtension_eq_zero_off {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) {x : M}
    (hx : ∀ p ∈ zeroSet n g, x ∉ W p) : gt n z g c W x = 0 := by
  unfold gt
  exact finsum_mem_eq_zero_of_forall_eq_zero (fun p hp => Set.indicator_of_notMem (hx p hp) _)

/- English proof (translation)
Establish `hsub : Function.support f ⊆ ⋃ i : s, U i`. Introduce `x hx`. Take `⟨i, hi, hxi⟩` from `hsupp x hx`. Conclude with `Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩`. Rewrite using `[← setLIntegral_eq_of_support_subset hsub]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem lintegral_le_sum_setLIntegral {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (U : ι → Set α) (hU : ∀ i ∈ s, MeasurableSet (U i)) (f : α → ℝ≥0∞) (h : ι → α → ℝ≥0∞)
    (hsupp : ∀ x, f x ≠ 0 → ∃ i ∈ s, x ∈ U i) (hle : ∀ i ∈ s, ∀ x ∈ U i, f x ≤ h i x) :
    ∫⁻ x, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ := by
  have hsub : Function.support f ⊆ ⋃ i : s, U i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hsupp x hx
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  rw [← setLIntegral_eq_of_support_subset hsub]
  calc ∫⁻ x in ⋃ i : s, U i, f x ∂μ ≤ ∑' i : s, ∫⁻ x in U i, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑ i ∈ s, ∫⁻ x in U i, f x ∂μ := Finset.tsum_subtype s (fun i => ∫⁻ x in U i, f x ∂μ)
    _ ≤ ∑ i ∈ s, ∫⁻ x in U i, h i x ∂μ :=
        Finset.sum_le_sum fun i hi => setLIntegral_mono' (hU i hi) (hle i hi)

/- English proof (translation)
Establish `h1 : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X)`. Rewrite using `[Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]`. Conclude with `ENNReal.rpow_le_rpow hx (by norm_num)`. Establish `h2 : y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Y)`. Rewrite using `[Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hY (by norm_num)]`.

Conclude with `ENNReal.rpow_le_rpow hy (by norm_num)`. Establish `h3 : x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y)`. Rewrite using `[ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]`. Conclude with `add_le_add h1 h2`. Combine the equalities or inequalities in the displayed calculation.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Real.rpow_two]`. Use polynomial arithmetic with `[sq_nonneg (Real.sqrt X / 10 - 10 * Real.sqrt Y), Real.sq_sqrt hX, Real.sq_sqrt hY]`.
-/
theorem sqrt_add_sq_le_weighted (x y : ℝ≥0∞) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hx : x ≤ ENNReal.ofReal X) (hy : y ≤ ENNReal.ofReal Y) :
    (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ≤
      ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
  have h1 : x ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hX (by norm_num)]
    exact ENNReal.rpow_le_rpow hx (by norm_num)
  have h2 : y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt Y) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hY (by norm_num)]
    exact ENNReal.rpow_le_rpow hy (by norm_num)
  have h3 : x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) := by
    rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
    exact add_le_add h1 h2
  calc (x ^ (1 / 2 : ℝ) + y ^ (1 / 2 : ℝ)) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h3 (by norm_num)
    _ = ENNReal.ofReal ((Real.sqrt X + Real.sqrt Y) ^ (2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)
    _ ≤ ENNReal.ofReal ((101 / 100) * X + 101 * Y) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Real.rpow_two]
        nlinarith [sq_nonneg (Real.sqrt X / 10 - 10 * Real.sqrt Y), Real.sq_sqrt hX, Real.sq_sqrt hY]

/- English proof (translation)
Use `set t : ℕ → ℝ := fun k => Real.sqrt (ε ^ 2 / 2 ^ k) with ht`. Establish `ht2 : ∀ k, t k ^ 2 = ε ^ 2 / 2 ^ k` using `fun k => Real.sq_sqrt (by positivity)`. Establish `htpos : ∀ k, 0 < t k` using `fun k => Real.sqrt_pos.2 (by positivity)`. Establish `htle : ∀ k, t k ≤ ε` using `fun k => by`. Combine the equalities or inequalities in the displayed calculation.

Use `set A : ℕ → Set α := fun k => U ∩ {x | t k ^ 2 / 2 ≤ e x ∧ e x ≤ t k ^ 2} with hAdef`. Establish `hA : ∀ k, MeasurableSet (A k)` using `fun k => hU.inter ((measurableSet_le measurable_const he).inter (measurableSet_le he measurable_const))`. Establish `hcover : U ∩ {x | e x < ε ^ 2} ⊆ (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k`. Introduce and unpack `x ⟨hxU, hx⟩`. Simplify using `only [Set.mem_setOf_eq] at hx`.

Distinguish the cases in `h0 : e x ≤ 0`. Conclude with `Or.inl ⟨hxU, h0⟩`. Use `push_neg at h0`. Take `⟨k, hk1, hk2⟩` from `exists_nat_pow_near (x := ε ^ 2 / e x) (y := (2 : ℝ)) ((one_le_div h0).2 hx.le) (by norm_num)`. Use `Or.inr (Set.mem_iUnion.2 ⟨k, hxU, ?_⟩)` and prove the remaining obligations.

Establish `h1` using `(le_div_iff₀ h0).1 hk1`. Establish `h2` using `(div_lt_iff₀ h0).1 hk2`. Establish `hp : (0 : ℝ) < 2 ^ k` using `by positivity`. Rewrite using `[ht2 k]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[div_div, div_le_iff₀ (by positivity)]`. Establish `h3 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2` using `pow_succ 2 k`. Rewrite `h2` using `[h3]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[le_div_iff₀ hp]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B`. Introduce `k`. Combine the equalities or inequalities in the displayed calculation. Use `setLIntegral_mono' (hA k) (fun x hx => ?_)` and prove the remaining obligations.

Take `⟨_, hx1, hx2⟩` from `hx`. Establish `hex : 0 < e x` using `lt_of_lt_of_le (by have := htpos k; positivity) hx1`. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Rewrite using `[Real.rpow_neg (he0 x), Real.rpow_natCast]`.

Establish `hpn : 0 < e x ^ n` using `pow_pos hex n`. Establish `hle1 : e x ≤ 1`. Establish `: t k ^ 2 ≤ 1`. Rewrite using `[ht2 k]`. Combine the equalities or inequalities in the displayed calculation.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hen : e x ^ n ≤ ε ^ 2 / 2 ^ k`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show ε ^ 2 / 2 ^ k * (f x * (e x ^ n)⁻¹) = f x * ((ε ^ 2 / 2 ^ k) / e x ^ n) by field_simp]`. Conclude with `le_mul_of_one_le_right (hf x) ((one_le_div hpn).2 hen)`.

Use `_ = ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ∫⁻ x in A k, ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B := by gcongr; exact hsh (t k) (htpos k) (htle k)`. Establish `hgeo : ∀ k : ℕ, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B = ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal B * 2⁻¹ ^ k`. Introduce `k`. Rewrite using `[ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2) k, ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[hgeo]`. Rewrite using `[ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, zero_add, show 2 * B * ε ^ 2 = ε ^ 2 * B * 2 by ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_ofNat]`.
-/
theorem lintegral_dyadic_shell_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) (e : α → ℝ) (he : Measurable e)
    (he0 : ∀ x, 0 ≤ e x) (U : Set α) (hU : MeasurableSet U) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x)
    (n : ℕ) (hn : 1 ≤ n) (ε B : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hB : 0 ≤ B)
    (hZ : μ (U ∩ {x | e x ≤ 0}) = 0)
    (hsh : ∀ t : ℝ, 0 < t → t ≤ ε →
      ∫⁻ x in U ∩ {x | t ^ 2 / 2 ≤ e x ∧ e x ≤ t ^ 2},
        ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ ≤ ENNReal.ofReal B) :
    ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (2 * B * ε ^ 2) := by
  set t : ℕ → ℝ := fun k => Real.sqrt (ε ^ 2 / 2 ^ k) with ht
  have ht2 : ∀ k, t k ^ 2 = ε ^ 2 / 2 ^ k := fun k => Real.sq_sqrt (by positivity)
  have htpos : ∀ k, 0 < t k := fun k => Real.sqrt_pos.2 (by positivity)
  have htle : ∀ k, t k ≤ ε := fun k => by
    calc t k ≤ Real.sqrt (ε ^ 2) :=
          Real.sqrt_le_sqrt (div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two))
      _ = ε := Real.sqrt_sq hε.le
  set A : ℕ → Set α := fun k => U ∩ {x | t k ^ 2 / 2 ≤ e x ∧ e x ≤ t k ^ 2} with hAdef
  have hA : ∀ k, MeasurableSet (A k) := fun k =>
    hU.inter ((measurableSet_le measurable_const he).inter (measurableSet_le he measurable_const))
  have hcover : U ∩ {x | e x < ε ^ 2} ⊆ (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k := by
    rintro x ⟨hxU, hx⟩
    simp only [Set.mem_setOf_eq] at hx
    by_cases h0 : e x ≤ 0
    · exact Or.inl ⟨hxU, h0⟩
    · push_neg at h0
      obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := ε ^ 2 / e x) (y := (2 : ℝ))
        ((one_le_div h0).2 hx.le) (by norm_num)
      refine Or.inr (Set.mem_iUnion.2 ⟨k, hxU, ?_⟩)
      have h1 := (le_div_iff₀ h0).1 hk1
      have h2 := (div_lt_iff₀ h0).1 hk2
      have hp : (0 : ℝ) < 2 ^ k := by positivity
      rw [ht2 k]
      constructor
      · rw [div_div, div_le_iff₀ (by positivity)]
        have h3 : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
        rw [h3] at h2
        linarith
      · rw [le_div_iff₀ hp]; nlinarith
  have hk : ∀ k, ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ ≤
      ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B := by
    intro k
    calc ∫⁻ x in A k, ENNReal.ofReal (f x) ∂μ
        ≤ ∫⁻ x in A k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ := by
          refine setLIntegral_mono' (hA k) (fun x hx => ?_)
          obtain ⟨_, hx1, hx2⟩ := hx
          have hex : 0 < e x := lt_of_lt_of_le (by have := htpos k; positivity) hx1
          rw [← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [Real.rpow_neg (he0 x), Real.rpow_natCast]
          have hpn : 0 < e x ^ n := pow_pos hex n
          have hle1 : e x ≤ 1 := by
            have : t k ^ 2 ≤ 1 := by
              rw [ht2 k]
              calc ε ^ 2 / 2 ^ k ≤ ε ^ 2 := div_le_self (sq_nonneg _) (one_le_pow₀ one_le_two)
                _ ≤ 1 := by nlinarith
            linarith
          have hen : e x ^ n ≤ ε ^ 2 / 2 ^ k := by
            calc e x ^ n ≤ e x := pow_le_of_le_one (he0 x) hle1 (by omega)
              _ ≤ t k ^ 2 := hx2
              _ = ε ^ 2 / 2 ^ k := ht2 k
          rw [show ε ^ 2 / 2 ^ k * (f x * (e x ^ n)⁻¹) = f x * ((ε ^ 2 / 2 ^ k) / e x ^ n) by
            field_simp]
          exact le_mul_of_one_le_right (hf x) ((one_le_div hpn).2 hen)
      _ = ENNReal.ofReal (ε ^ 2 / 2 ^ k) *
            ∫⁻ x in A k, ENNReal.ofReal (f x * e x ^ (-(n : ℝ))) ∂μ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
          by gcongr; exact hsh (t k) (htpos k) (htle k)
  have hgeo : ∀ k : ℕ, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B =
      ENNReal.ofReal (ε ^ 2) * ENNReal.ofReal B * 2⁻¹ ^ k := by
    intro k
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2) k,
      ENNReal.ofReal_ofNat, div_eq_mul_inv, ENNReal.inv_pow]
    ring
  calc ∫⁻ x in U ∩ {x | e x < ε ^ 2}, ENNReal.ofReal (f x) ∂μ
      ≤ ∫⁻ x in (U ∩ {x | e x ≤ 0}) ∪ ⋃ k, A k, ENNReal.ofReal (f x) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U ∩ {x | e x ≤ 0}, ENNReal.ofReal (f x) ∂μ +
          ∫⁻ x in ⋃ k, A k, ENNReal.ofReal (f x) ∂μ := lintegral_union_le _ _ _
    _ ≤ 0 + ∑' k, ENNReal.ofReal (ε ^ 2 / 2 ^ k) * ENNReal.ofReal B :=
        add_le_add (le_of_eq (setLIntegral_measure_zero _ _ hZ))
          ((lintegral_iUnion_le _ _).trans (ENNReal.tsum_le_tsum hk))
    _ = ENNReal.ofReal (2 * B * ε ^ 2) := by
        simp_rw [hgeo]
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          zero_add, show 2 * B * ε ^ 2 = ε ^ 2 * B * 2 by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (sq_nonneg _),
          ENNReal.ofReal_ofNat]

end ReciprocityTheory.L2DbarEstimates.I
