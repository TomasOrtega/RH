import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified

set_option autoImplicit false

noncomputable section

open Polynomial GlobalTheory.Published.AbVarRed IsLocalRing

namespace GlobalTheory.ValAbove

/- English proof (translation)
Establish `hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈ Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)`. Introduce `e he r`. Apply `Submodule.smul_mem` to reduce the goal to its premises. Apply `Submodule.subset_span` to reduce the goal to its premises. Conclude with `Set.mem_image_of_mem _ (Set.mem_Iic.2 he)`.

Distinguish the cases in `htm : t < m`. Rewrite using `[Finset.sum_mul]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_Ico]`. Rewrite using `[smul_mul_assoc, ← pow_add]`.

Conclude with `hmem _ (by omega) _`. Use `push_neg at htm`. Establish `hsplit` using `Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)`. Rewrite `hsplit` using `[h]`. Establish `e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m)`.

Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_Ico]`. Rewrite using `[smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]`. Use `congr 2`.

Use linear arithmetic over natural numbers and integers. Establish `key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m))`. Rewrite using `[e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_mul_assoc, ← pow_add]`. Rewrite using `[key]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)` and prove the remaining obligations. Rewrite `hi` using `[Finset.mem_range]`. Conclude with `hmem _ (by omega) _`.
-/
theorem partialSum_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (c : ℕ → R) (n : ℕ)
    (x : Ω) (h : ∑ i ∈ Finset.range (n + 1), c i • x ^ i = 0) {m t : ℕ} (hm : m ≤ n) (ht : t ≤ n + 1) :
    (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
  have hmem : ∀ e, e ≤ n → ∀ r : R, r • x ^ e ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n) := by
    intro e he r
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact Set.mem_image_of_mem _ (Set.mem_Iic.2 he)
  by_cases htm : t < m
  · rw [Finset.sum_mul]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [smul_mul_assoc, ← pow_add]
    exact hmem _ (by omega) _
  · push_neg at htm
    have hsplit := Finset.sum_range_add_sum_Ico (fun i => c i • x ^ i) (show m ≤ n + 1 by omega)
    rw [h] at hsplit
    have e1 : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ i) * x ^ (t - m) := by
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ico] at hi
      rw [smul_mul_assoc, smul_mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    have key : (∑ i ∈ Finset.Ico m (n + 1), c i • x ^ (i - m)) * x ^ t
        = -∑ i ∈ Finset.range m, c i • x ^ (i + (t - m)) := by
      rw [e1, eq_neg_of_add_eq_zero_right hsplit, neg_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, ← pow_add]
    rw [key]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    rw [Finset.mem_range] at hi
    exact hmem _ (by omega) _

/- English proof (translation)
Use `isIntegral_of_smul_mem_submodule (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_` and prove the remaining obligations. Rewrite using `[Ne, Submodule.span_eq_bot] push_neg`. Use `⟨1, ?_, one_ne_zero⟩` and prove the remaining obligations. Conclude with `⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩`. Introduce `w hw`.

Use `Submodule.span_induction (fun w hw => ?_) (by simp) (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb) (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw` and prove the remaining obligations. Take `⟨t, ht, rfl⟩` from `hw`. Rewrite `ht` using `[Set.mem_Iic]`. Rewrite using `[smul_eq_mul]`. Conclude with `hz t (by omega)`.
-/
theorem isIntegral_of_mul_pow_mem {R Ω : Type} [CommRing R] [Field Ω] [Algebra R Ω] (n : ℕ) (x z : Ω)
    (hz : ∀ t ≤ n, z * x ^ t ∈
      Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) :
    IsIntegral R z := by
  refine isIntegral_of_smul_mem_submodule
    (Submodule.span R ((fun i : ℕ => x ^ i) '' Set.Iic n)) ?_ (Submodule.fg_span ((Set.finite_Iic n).image _)) z ?_
  · rw [Ne, Submodule.span_eq_bot]
    push_neg
    refine ⟨1, ?_, one_ne_zero⟩
    exact ⟨0, Set.mem_Iic.2 (Nat.zero_le n), pow_zero x⟩
  · intro w hw
    refine Submodule.span_induction (fun w hw => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [smul_add]; exact Submodule.add_mem _ ha hb)
      (fun r a _ ha => by rw [smul_eq_mul, mul_smul_comm]; exact Submodule.smul_mem _ r ha) hw
    obtain ⟨t, ht, rfl⟩ := hw
    rw [Set.mem_Iic] at ht
    rw [smul_eq_mul]
    exact hz t (by omega)

/- English proof (translation)
Introduce `R K Ω _ _ _ _ _ _ _ _ _ V hV y hy`. Use `letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra`. Use `haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K))` using `(algebraMap K Ω).injective.comp (IsFractionRing.injective R K)`. Establish `hmemV : ∀ r : R, algebraMap R Ω r ∈ V`.

Introduce `r`. Establish `: algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω)` using `by rw [hV]; exact ⟨r, rfl⟩`. Conclude with `this`. Establish `hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1` using `fun r => (V.valuation_le_one_iff _).2 (hmemV r)`. Establish `hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1`.

Introduce `r hr`. Use `lt_of_le_of_ne (hle r) fun h1 => hr ?_` and prove the remaining obligations. Establish `h0 : algebraMap R Ω r ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, map_zero]`.

Conclude with `zero_ne_one h1`. Establish `hinv : (algebraMap R Ω r)⁻¹ ∈ V` using `(V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])`. Establish `hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω)`. Express the relevant statement in the definitionally equal form `algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V`. Rewrite using `[map_inv₀]`.

Conclude with `hinv`. Rewrite `hK` using `[hV]`. Take `⟨r', hr'⟩` from `hK`. Establish `hrK : algebraMap R K r ≠ 0`. Introduce `h`.

Apply `h0` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap K Ω (algebraMap R K r) = 0`. Rewrite using `[h, map_zero]`. Establish `hrr : r * r' = 1` using `IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])`. Conclude with `⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩`.

Establish `hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1`. Introduce `r hr`. Take `⟨u, rfl⟩` from `hr`. Establish `h` using `congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv`. Simplify using `only [map_mul, map_one] at h`.

Use `le_antisymm (hle _) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt'`. Use `push_neg at hlt'`. Establish `: V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'`. Rewrite `this` using `[h]`.

Conclude with `lt_irrefl _ this`. Use `haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable`. Establish `halgK : IsAlgebraic K y` using `Algebra.IsAlgebraic.isAlgebraic y`. Establish `halgR : IsAlgebraic R y` using `(IsFractionRing.isAlgebraic_iff R K Ω).2 halgK`. Take `⟨f, hf0, hfy⟩` from `halgR`.

Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f)`. Establish `hc : f.leadingCoeff ≠ 0` using `leadingCoeff_ne_zero.2 hf0`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ`. Use `⟨e, fun hd => ?_⟩` and prove the remaining obligations.

Establish `hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R)`. Rewrite using `[← pow_succ, mul_comm]`. Rewrite using `[← hu]`. Conclude with `(C_dvd_iff_dvd_coeff _ _).1 hd _`. Establish `: ϖ ∣ (u : R)` using `(mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'`.

Conclude with `hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)`. Establish `hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f`. Introduce `e he`. Consider the cases of `e with`. Consider the case `zero => simp`.

Consider the case `succ k => exact not_not.1 (he k (Nat.lt_succ_self k))`. Take `⟨g, hg⟩` from `hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)`. Establish `hgunit : ∃ i, IsUnit (g.coeff i)`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`.

Apply `Nat.find_spec hex` to reduce the goal to its premises. Establish `hmax : maximalIdeal R = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `hCg : C ϖ ∣ g` using `(C_dvd_iff_dvd_coeff _ _).2 fun i => by`. Establish `: g.coeff i ∈ maximalIdeal R` using `(mem_maximalIdeal _).2 (hno i)`. Rewrite `this` using `[hmax]`.

Conclude with `Ideal.mem_span_singleton.1 this`. Establish `h2` using `mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg`. Rewrite `h2` using `[← hg, ← C_mul, ← pow_succ]`. Conclude with `h2`. Establish `hgy : aeval y g = 0`.

Rewrite `hfy` using `[hg, map_mul, aeval_C]`. Use `(mul_eq_zero.1 hfy).resolve_left ?_` and prove the remaining obligations. Conclude with `fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))`. Use `set n := g.natDegree with hn`. Use `set c := g.coeff with hc`.

Establish `hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0`. Rewrite using `[← hgy, aeval_eq_sum_range]`. Take `⟨i₀, hi₀⟩` from `hgunit`. Establish `hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty` using `⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩`. Use `set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj`.

Establish `hjmem` using `Finset.max'_mem _ hS`. Rewrite `hjmem` using `[← hj, Finset.mem_filter, Finset.mem_range]`. Establish `hjn : j ≤ n` using `Nat.le_of_lt_succ hjmem.1`. Establish `hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i)`. Introduce `i hji hin hu`.

Use `Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)` as an intermediate fact. Rewrite `this` using `[← hj]`. Use linear arithmetic over natural numbers and integers. Use `set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb`. Establish `hyle : V.valuation y ≤ 1` using `(V.valuation_le_one_iff y).2 hy`.

Establish `hvb : V.valuation b = 1`. Rewrite using `[hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def, mul_one, add_comm]`. Rewrite using `[Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]`. Rewrite using `[hunit _ hjmem.2]`. Use `Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_Ico]`. Rewrite using `[Algebra.smul_def, map_mul, map_pow]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))`. Use `⟨y * b, b, ?_, ?_, hvb, rfl⟩` and prove the remaining obligations. Conclude with `isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by`.

Rewrite using `[show y * b * y ^ t = b * y ^ (t + 1) by ring]`. Conclude with `partialSum_mul_pow_mem c n y hsum hjn (by omega)`. Conclude with `isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)`.
-/
theorem exists_integral_mul_eq_of_isAbove : ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring → ∀ y ∈ V, ∃ a s : Ω,
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem a ∧
      ((algebraMap K Ω).comp (algebraMap R K)).IsIntegralElem s ∧ V.valuation s = 1 ∧ y * s = a := by
  intro R K Ω _ _ _ _ _ _ _ _ _ V hV y hy
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hιinj : Function.Injective ((algebraMap K Ω).comp (algebraMap R K)) :=
    (algebraMap K Ω).injective.comp (IsFractionRing.injective R K)
  have hmemV : ∀ r : R, algebraMap R Ω r ∈ V := by
    intro r
    have : algebraMap R K r ∈ V.toSubring.comap (algebraMap K Ω) := by rw [hV]; exact ⟨r, rfl⟩
    exact this
  have hle : ∀ r : R, V.valuation (algebraMap R Ω r) ≤ 1 := fun r => (V.valuation_le_one_iff _).2 (hmemV r)
  have hlt : ∀ r : R, ¬ IsUnit r → V.valuation (algebraMap R Ω r) < 1 := by
    intro r hr
    refine lt_of_le_of_ne (hle r) fun h1 => hr ?_
    have h0 : algebraMap R Ω r ≠ 0 := by
      intro h; rw [h, map_zero] at h1; exact zero_ne_one h1
    have hinv : (algebraMap R Ω r)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, h1, inv_one])
    have hK : (algebraMap R K r)⁻¹ ∈ V.toSubring.comap (algebraMap K Ω) := by
      change algebraMap K Ω ((algebraMap R K r)⁻¹) ∈ V
      rw [map_inv₀]; exact hinv
    rw [hV] at hK
    obtain ⟨r', hr'⟩ := hK
    have hrK : algebraMap R K r ≠ 0 := by
      intro h; apply h0; change algebraMap K Ω (algebraMap R K r) = 0; rw [h, map_zero]
    have hrr : r * r' = 1 :=
      IsFractionRing.injective R K (by rw [map_mul, hr', mul_inv_cancel₀ hrK, map_one])
    exact ⟨⟨r, r', hrr, by rw [mul_comm, hrr]⟩, rfl⟩
  have hunit : ∀ r : R, IsUnit r → V.valuation (algebraMap R Ω r) = 1 := by
    intro r hr
    obtain ⟨u, rfl⟩ := hr
    have h := congrArg (fun w => V.valuation (algebraMap R Ω w)) u.mul_inv
    simp only [map_mul, map_one] at h
    refine le_antisymm (hle _) ?_
    by_contra hlt'
    push_neg at hlt'
    have : V.valuation (algebraMap R Ω ↑u) * V.valuation (algebraMap R Ω ↑u⁻¹) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' (hle _)) hlt'
    rw [h] at this
    exact lt_irrefl _ this

  classical
  haveI : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have halgK : IsAlgebraic K y := Algebra.IsAlgebraic.isAlgebraic y
  have halgR : IsAlgebraic R y := (IsFractionRing.isAlgebraic_iff R K Ω).2 halgK
  obtain ⟨f, hf0, hfy⟩ := halgR
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∃ e : ℕ, ¬ (C (ϖ ^ (e + 1)) ∣ f) := by
    have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hf0
    obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
    refine ⟨e, fun hd => ?_⟩
    have hd' : ϖ ^ e * ϖ ∣ ϖ ^ e * (u : R) := by
      rw [← pow_succ, mul_comm]; rw [← hu]
      exact (C_dvd_iff_dvd_coeff _ _).1 hd _
    have : ϖ ∣ (u : R) := (mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)).1 hd'
    exact hϖ.not_isUnit (isUnit_of_dvd_unit this u.isUnit)
  have hdiv : ∀ e, (∀ k < e, ¬ ¬ (C (ϖ ^ (k + 1)) ∣ f)) → C (ϖ ^ e) ∣ f := by
    intro e he
    cases e with
    | zero => simp
    | succ k => exact not_not.1 (he k (Nat.lt_succ_self k))
  obtain ⟨g, hg⟩ := hdiv (Nat.find hex) (fun k hk => Nat.find_min hex hk)
  have hgunit : ∃ i, IsUnit (g.coeff i) := by
    by_contra hno
    push_neg at hno
    apply Nat.find_spec hex
    have hmax : maximalIdeal R = Ideal.span {ϖ} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hCg : C ϖ ∣ g := (C_dvd_iff_dvd_coeff _ _).2 fun i => by
      have : g.coeff i ∈ maximalIdeal R := (mem_maximalIdeal _).2 (hno i)
      rw [hmax] at this
      exact Ideal.mem_span_singleton.1 this
    have h2 := mul_dvd_mul_left (C (ϖ ^ Nat.find hex)) hCg
    rw [← hg, ← C_mul, ← pow_succ] at h2
    exact h2
  have hgy : aeval y g = 0 := by
    rw [hg, map_mul, aeval_C] at hfy
    refine (mul_eq_zero.1 hfy).resolve_left ?_
    exact fun h => pow_ne_zero _ hϖ.ne_zero (hιinj (h.trans (map_zero _).symm))
  set n := g.natDegree with hn
  set c := g.coeff with hc
  have hsum : ∑ i ∈ Finset.range (n + 1), c i • y ^ i = 0 := by
    rw [← hgy, aeval_eq_sum_range]
  obtain ⟨i₀, hi₀⟩ := hgunit
  have hS : ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).Nonempty :=
    ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi₀.ne_zero)), hi₀⟩⟩
  set j := ((Finset.range (n + 1)).filter fun i => IsUnit (c i)).max' hS with hj
  have hjmem := Finset.max'_mem _ hS
  rw [← hj, Finset.mem_filter, Finset.mem_range] at hjmem
  have hjn : j ≤ n := Nat.le_of_lt_succ hjmem.1
  have hbig : ∀ i, j < i → i ≤ n → ¬ IsUnit (c i) := by
    intro i hji hin hu
    have := Finset.le_max' ((Finset.range (n + 1)).filter fun i => IsUnit (c i)) i
      (by simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hu⟩)
    rw [← hj] at this
    omega
  set b := ∑ i ∈ Finset.Ico j (n + 1), c i • y ^ (i - j) with hb
  have hyle : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
  have hvb : V.valuation b = 1 := by
    rw [hb, Finset.sum_eq_sum_Ico_succ_bot (Nat.lt_succ_of_le hjn), Nat.sub_self, pow_zero, Algebra.smul_def,
      mul_one, add_comm]
    rw [Valuation.map_add_eq_of_lt_right, hunit _ hjmem.2]
    rw [hunit _ hjmem.2]
    refine Valuation.map_sum_lt _ one_ne_zero fun i hi => ?_
    rw [Finset.mem_Ico] at hi
    rw [Algebra.smul_def, map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (pow_le_one' hyle _)) (hlt _ (hbig i (by omega) (by omega)))
  refine ⟨y * b, b, ?_, ?_, hvb, rfl⟩
  · exact isIntegral_of_mul_pow_mem n y (y * b) fun t ht => by
      rw [show y * b * y ^ t = b * y ^ (t + 1) by ring]
      exact partialSum_mul_pow_mem c n y hsum hjn (by omega)
  · exact isIntegral_of_mul_pow_mem n y b fun t ht => partialSum_mul_pow_mem c n y hsum hjn (by omega)

end GlobalTheory.ValAbove
