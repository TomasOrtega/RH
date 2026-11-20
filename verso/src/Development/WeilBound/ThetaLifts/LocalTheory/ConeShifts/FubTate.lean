import Mathlib

noncomputable section

namespace PositivityTheory.ThKG.Fub

open MeasureTheory Topology Filter

/- English proof (translation)
Take `⟨C, hC⟩` from `(hK.image hf).bddAbove`. Establish `key : ∀ y : G, (∀ n : ℕ, y ^ n ∈ K) → f y ≤ 1` using `fun y hy => by`. Assume the negation of the conclusion as `h`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt C (not_le.1 h)`. Conclude with `absurd (hC ⟨_, hy n, map_pow f y n⟩) (not_le.2 hn)`.

Establish `h1` using `key x fun n => by simpa using hx n`. Establish `h2` using `key x⁻¹ fun n => by simpa using hx (-n)`. Establish `h3 : f x * f x⁻¹ = 1` using `by rw [← map_mul]; simp`. Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem one_of_compact {G : Type} [Group G] [TopologicalSpace G] (f : G →* NNReal) (hf : Continuous f) {K : Set G} (hK : IsCompact K)
    {x : G} (hx : ∀ n : ℤ, x ^ n ∈ K) : f x = 1 := by
  obtain ⟨C, hC⟩ := (hK.image hf).bddAbove
  have key : ∀ y : G, (∀ n : ℕ, y ^ n ∈ K) → f y ≤ 1 := fun y hy => by
    by_contra h
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 h)
    exact absurd (hC ⟨_, hy n, map_pow f y n⟩) (not_le.2 hn)
  have h1 := key x fun n => by simpa using hx n
  have h2 := key x⁻¹ fun n => by simpa using hx (-n)
  have h3 : f x * f x⁻¹ = 1 := by rw [← map_mul]; simp
  refine le_antisymm h1 ?_
  calc (1 : NNReal) = f x * f x⁻¹ := h3.symm
    _ ≤ f x * 1 := by gcongr
    _ = f x := mul_one _

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Establish `h0 : (z : ℂ) - 1 ≠ 0` using `fun e => hz (Circle.coe_eq_one.1 (sub_eq_zero.1 e))`. Establish `hre : ∀ n : ℕ, 1 / 2 < ((z : ℂ) ^ n).re` using `fun n => by`. Establish `h1` using `h n`. Rewrite `h1` using `[Circle.coe_pow]`.

Establish `h2 : ‖(z : ℂ) ^ n‖ = 1` using `by rw [norm_pow, Circle.norm_coe, one_pow]`. Establish `h3` using `Complex.sq_norm ((z : ℂ) ^ n - 1)`. Establish `h4` using `Complex.sq_norm ((z : ℂ) ^ n)`. Rewrite `h3`, `h4` using `[Complex.normSq_apply]`. Simplify using `only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3`.

Use polynomial arithmetic with `[norm_nonneg ((z : ℂ) ^ n - 1)]`. Take `⟨N, hN⟩` from `exists_nat_gt (4 / ‖(z : ℂ) - 1‖)`. Establish `hp : 0 < ‖(z : ℂ) - 1‖` using `norm_pos_iff.2 h0`. Establish `e : (∑ i ∈ Finset.range N, (z : ℂ) ^ i) * (z - 1) = z ^ N - 1` using `geom_sum_mul _ _`. Establish `h1 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, (z : ℂ) ^ i‖`.

Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations. Rewrite using `[Complex.re_sum]`. Use `Finset.card_nsmul_le_sum (Finset.range N) (fun i => ((z : ℂ) ^ i).re) (1 / 2) fun i _ => (hre i).le` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv]`. Establish `h2 : ‖(z : ℂ) ^ N - 1‖ < 1` using `by simpa using h N`.

Rewrite `h2` using `[← e, norm_mul]`. Rewrite `hN` using `[div_lt_iff₀ hp]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem circle_one {z : Circle} (h : ∀ n : ℕ, ‖((z ^ n : Circle) : ℂ) - 1‖ < 1) : z = 1 := by
  by_contra hz
  have h0 : (z : ℂ) - 1 ≠ 0 := fun e => hz (Circle.coe_eq_one.1 (sub_eq_zero.1 e))
  have hre : ∀ n : ℕ, 1 / 2 < ((z : ℂ) ^ n).re := fun n => by
    have h1 := h n
    rw [Circle.coe_pow] at h1
    have h2 : ‖(z : ℂ) ^ n‖ = 1 := by rw [norm_pow, Circle.norm_coe, one_pow]
    have h3 := Complex.sq_norm ((z : ℂ) ^ n - 1)
    have h4 := Complex.sq_norm ((z : ℂ) ^ n)
    rw [Complex.normSq_apply] at h3 h4
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero] at h3
    nlinarith [norm_nonneg ((z : ℂ) ^ n - 1)]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / ‖(z : ℂ) - 1‖)
  have hp : 0 < ‖(z : ℂ) - 1‖ := norm_pos_iff.2 h0
  have e : (∑ i ∈ Finset.range N, (z : ℂ) ^ i) * (z - 1) = z ^ N - 1 := geom_sum_mul _ _
  have h1 : (N : ℝ) / 2 ≤ ‖∑ i ∈ Finset.range N, (z : ℂ) ^ i‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    rw [Complex.re_sum]
    have := Finset.card_nsmul_le_sum (Finset.range N) (fun i => ((z : ℂ) ^ i).re) (1 / 2) fun i _ => (hre i).le
    simpa [div_eq_mul_inv] using this
  have h2 : ‖(z : ℂ) ^ N - 1‖ < 1 := by simpa using h N
  rw [← e, norm_mul] at h2
  rw [div_lt_iff₀ hp] at hN
  nlinarith

/- English proof (translation)
Use `haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU`. Establish `hf : ((QuotientGroup.mk : G → G ⧸ U) '' K).Finite` using `(hK.image QuotientGroup.continuous_mk).finite_of_discrete`. Take `⟨i, j, hij, e⟩` from `Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => (QuotientGroup.mk (x ^ n) : G ⧸ U)) (fun n => Set.mem_image_of_mem _ (hx n)) hf`. Use `⟨j - i, by omega, ?_⟩` and prove the remaining obligations. Use `QuotientGroup.eq.1 e` as an intermediate fact.

Rewrite `this` using `[show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add]; congr 1; omega, inv_mul_cancel_left]`. Then use the resulting hypothesis.
-/
theorem pow_mem_of_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G))
    {K : Set G} (hK : IsCompact K) {x : G} (hx : ∀ n : ℕ, x ^ n ∈ K) : ∃ k : ℕ, 0 < k ∧ x ^ k ∈ U := by
  haveI : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have hf : ((QuotientGroup.mk : G → G ⧸ U) '' K).Finite := (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  obtain ⟨i, j, hij, e⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem (f := fun n : ℕ => (QuotientGroup.mk (x ^ n) : G ⧸ U))
    (fun n => Set.mem_image_of_mem _ (hx n)) hf
  refine ⟨j - i, by omega, ?_⟩
  have := QuotientGroup.eq.1 e
  rwa [show x ^ j = x ^ i * x ^ (j - i) by rw [← pow_add]; congr 1; omega, inv_mul_cancel_left] at this

/- English proof (translation)
Set `O : H →* Multiplicative ℤ` to `MonoidHom.mk' (fun x => Multiplicative.ofAdd (o x)) fun x y => by rw [ho]; rfl`. Establish `oz : ∀ (k : ℤ) x, o (ϖ ^ k * x) = k + o x` using `fun k x => by`. Use `map_zpow O ϖ k` as an intermediate fact. Establish `h2 : o (ϖ ^ k) = k`. Establish `h3` using `congrArg Multiplicative.toAdd this`.

Simplify `h3` using `[O, hϖ]`. Rewrite using `[ho, h2]`. Establish `h0 : χ ϖ ≠ 0` using `fun e => by`. Use `map_mul χ ϖ ϖ⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, map_one, e, zero_mul]`.

Conclude with `one_ne_zero this`. Set `A : ℕ → Set H` to `fun k => {x | o x = m + k}`. Establish `hA : ∀ k, A k = (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}` using `fun k => Set.ext fun x => by`. Simplify using `only [A, Set.mem_setOf_eq, Set.mem_preimage, oz]`. Use linear arithmetic over natural numbers and integers.

Establish `mA : ∀ k, MeasurableSet (A k)` using `fun k => by`. Rewrite using `[hA]`. Conclude with `(hU.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `vA : ∀ k, γ (A k) = 1` using `fun k => by rw [hA, measure_preimage_mul, h1]`. Establish `cA : ∀ k, ∀ x ∈ A k, χ x = χ ϖ ^ m * χ ϖ ^ k` using `fun k x hx => by`.

Use `hχ _ ((hA k ▸ hx : x ∈ (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}))` as an intermediate fact. Rewrite `this` using `[map_mul, map_zpow, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _ h0)]`. Rewrite using `[← this, zpow_add₀ h0, zpow_natCast]`. Establish `dA : Pairwise (Function.onFun Disjoint A)` using `fun i j hij => Set.disjoint_left.2 fun x h h' => hij (by`. Simplify using `only [A, Set.mem_setOf_eq] at h h'`.

Use the proof step `omega)`. Establish `eU : (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) = (⋃ k, A k).indicator χ` using `funext fun x => by`. Distinguish the cases in `h : m ≤ o x`. Rewrite using `[if_pos h, one_mul, Set.indicator_of_mem (Set.mem_iUnion.2 ⟨(o x - m).toNat, by simp only [A, Set.mem_setOf_eq]; omega⟩)]`. Rewrite using `[if_neg h, zero_mul, Set.indicator_of_notMem fun h' => by`.

Take `⟨k, hk⟩` from `Set.mem_iUnion.1 h'`. Simplify using `only [A, Set.mem_setOf_eq] at hk`. Use the proof step `omega]`. Establish `iA : ∀ k, IntegrableOn χ (A k) γ` using `fun k => (integrableOn_const (C := χ ϖ ^ m * χ ϖ ^ k) (by rw [vA]; simp)).congr_fun (fun x hx => (cA k x hx).symm) (mA k)`. Establish `sA : ∀ k, ∫ x in A k, χ x ∂γ = χ ϖ ^ m * χ ϖ ^ k` using `fun k => by`.

Rewrite using `[setIntegral_congr_fun (mA k) (cA k), setIntegral_const, Measure.real, vA]`. Simplify using the standard rewrite rules. Establish `nA : ∀ k, ∫ x in A k, ‖χ x‖ ∂γ = ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k` using `fun k => by`. Rewrite using `[setIntegral_congr_fun (mA k) (g := fun _ => ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k) fun x hx => by simp only [cA k x hx, norm_mul, norm_pow], setIntegral_const, Measure.real, vA]; simp`. Establish `iU : IntegrableOn χ (⋃ k, A k) γ` using `integrableOn_iUnion_of_summable_integral_norm iA (by`.

Simplify using `only [nA]`. Conclude with `(summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left _)`. Rewrite using `[eU, integrable_indicator_iff (MeasurableSet.iUnion mA), integral_indicator (MeasurableSet.iUnion mA)]`. Use `⟨iU, (hasSum_integral_iUnion mA dA iU).unique ?_⟩` and prove the remaining obligations. Simplify using `only [sA]`.

Conclude with `(hasSum_geometric_of_norm_lt_one ht).mul_left _`.
-/
theorem tate {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (γ : Measure H) [γ.IsMulLeftInvariant] (o : H → ℤ) (ho : ∀ x y, o (x * y) = o x + o y) (hU : IsOpen {x | o x = 0})
    (h1 : γ {x | o x = 0} = 1) (ϖ : H) (hϖ : o ϖ = 1) (χ : H →* ℂ) (hχ : ∀ x, o x = 0 → χ x = 1) (ht : ‖χ ϖ‖ < 1) (m : ℤ) :
    Integrable (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) γ ∧
      ∫ x, (if m ≤ o x then (1 : ℂ) else 0) * χ x ∂γ = χ ϖ ^ m * (1 - χ ϖ)⁻¹ := by
  let O : H →* Multiplicative ℤ := MonoidHom.mk' (fun x => Multiplicative.ofAdd (o x)) fun x y => by rw [ho]; rfl
  have oz : ∀ (k : ℤ) x, o (ϖ ^ k * x) = k + o x := fun k x => by
    have := map_zpow O ϖ k
    have h2 : o (ϖ ^ k) = k := by
      have h3 := congrArg Multiplicative.toAdd this
      simpa [O, hϖ] using h3
    rw [ho, h2]
  have h0 : χ ϖ ≠ 0 := fun e => by
    have := map_mul χ ϖ ϖ⁻¹
    rw [mul_inv_cancel, map_one, e, zero_mul] at this
    exact one_ne_zero this
  let A : ℕ → Set H := fun k => {x | o x = m + k}
  have hA : ∀ k, A k = (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0} := fun k => Set.ext fun x => by
    simp only [A, Set.mem_setOf_eq, Set.mem_preimage, oz]; omega
  have mA : ∀ k, MeasurableSet (A k) := fun k => by
    rw [hA]; exact (hU.preimage (continuous_const.mul continuous_id)).measurableSet
  have vA : ∀ k, γ (A k) = 1 := fun k => by rw [hA, measure_preimage_mul, h1]
  have cA : ∀ k, ∀ x ∈ A k, χ x = χ ϖ ^ m * χ ϖ ^ k := fun k x hx => by
    have := hχ _ ((hA k ▸ hx : x ∈ (fun x => ϖ ^ (-(m + k)) * x) ⁻¹' {x | o x = 0}))
    rw [map_mul, map_zpow, zpow_neg, inv_mul_eq_one₀ (zpow_ne_zero _ h0)] at this
    rw [← this, zpow_add₀ h0, zpow_natCast]
  have dA : Pairwise (Function.onFun Disjoint A) := fun i j hij => Set.disjoint_left.2 fun x h h' => hij (by
    simp only [A, Set.mem_setOf_eq] at h h'; omega)
  have eU : (fun x => (if m ≤ o x then (1 : ℂ) else 0) * χ x) = (⋃ k, A k).indicator χ := funext fun x => by
    by_cases h : m ≤ o x
    · rw [if_pos h, one_mul, Set.indicator_of_mem (Set.mem_iUnion.2 ⟨(o x - m).toNat, by simp only [A, Set.mem_setOf_eq]; omega⟩)]
    · rw [if_neg h, zero_mul, Set.indicator_of_notMem fun h' => by
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 h'
        simp only [A, Set.mem_setOf_eq] at hk; omega]
  have iA : ∀ k, IntegrableOn χ (A k) γ := fun k =>
    (integrableOn_const (C := χ ϖ ^ m * χ ϖ ^ k) (by rw [vA]; simp)).congr_fun (fun x hx => (cA k x hx).symm) (mA k)
  have sA : ∀ k, ∫ x in A k, χ x ∂γ = χ ϖ ^ m * χ ϖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (cA k), setIntegral_const, Measure.real, vA]; simp
  have nA : ∀ k, ∫ x in A k, ‖χ x‖ ∂γ = ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k := fun k => by
    rw [setIntegral_congr_fun (mA k) (g := fun _ => ‖χ ϖ ^ m‖ * ‖χ ϖ‖ ^ k) fun x hx => by simp only [cA k x hx, norm_mul, norm_pow],
      setIntegral_const, Measure.real, vA]; simp
  have iU : IntegrableOn χ (⋃ k, A k) γ := integrableOn_iUnion_of_summable_integral_norm iA (by
    simp only [nA]; exact (summable_geometric_of_lt_one (norm_nonneg _) ht).mul_left _)
  rw [eU, integrable_indicator_iff (MeasurableSet.iUnion mA), integral_indicator (MeasurableSet.iUnion mA)]
  refine ⟨iU, (hasSum_integral_iUnion mA dA iU).unique ?_⟩
  simp only [sA]
  exact (hasSum_geometric_of_norm_lt_one ht).mul_left _

end PositivityTheory.ThKG.Fub

end
