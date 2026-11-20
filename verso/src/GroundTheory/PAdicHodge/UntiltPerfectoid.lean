import Mathlib
import GroundTheory.PAdicHodge.UntiltDegree
import GroundTheory.PAdicHodge.PerfectoidCriterion
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "𝒪K♭" => PreTilt (normInteger K) p
local notation "𝒪C♭" => PreTilt (normInteger C) p

/- English proof (translation)
Take `⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, -, horth, -, -, hsub⟩` from `exists_untiltField_basis (K := K) (C := C) (p := p) N`. Use `set ρ' := (1 + ρ) / 2 with hρ'`. Establish `hρρ' : ρ < ρ'` using `by rw [hρ']; linarith`. Establish `hρ'1 : ρ' < 1` using `by rw [hρ']; linarith`. Establish `hρ'0 : 0 < ρ'` using `hρ0.trans hρρ'`.

Establish `htr : 0 < t * r` using `mul_pos ht0 hr0`. Establish `hp' : ‖(p : K)‖ ≤ t * r * ρ'` using `hp.trans (by gcongr)`. Establish `hpstrict : ‖(p : K)‖ < t * r * ρ'` using `hp.trans_lt (mul_lt_mul_of_pos_left hρρ' htr)`. Establish `hest` using `fun l i => mul_norm_le_norm_sum_smul_tiltSharp (K := K) (C := C) (p := p) horth (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0.le hρ'0 hρ'1 hp' l i`. Use `set b := t * r * ρ' with hbdef`.

Establish `hb0 : 0 < b` using `mul_pos htr hρ'0`. Establish `hb1 : b ≤ 1`. Establish `: t * r ≤ 1` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Take `⟨ε, hε1, hε2⟩` from `exists_norm_mem_Ioc (K := K♭) p (lt_max_of_lt_right (half_pos hb0)) (max_lt hpstrict (half_lt_self hb0))`.

Take `⟨γ, rfl⟩` from `norm_le_one_iff_exists_algebraMap.1 (hε2.trans hb1)`. Rewrite `hε1`, `hε2` using `[norm_algebraMap_preTilt]`. Establish `hpγ : ‖(p : K)‖ < ‖γ‖` using `(le_max_left _ _).trans_lt hε1`. Use `set γ' := (frobeniusEquiv 𝒪K♭ p).symm γ`. Use `set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he`.

Use `set e' : K := ((PreTilt.untilt γ' : normInteger K) : K) with he'`. Establish `hee' : e' ^ p = e`. Rewrite using `[he', he, ← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]`. Establish `hen : ‖e‖ = ‖γ‖` using `(preTilt_norm_def γ).symm`. Establish `he0 : 0 < ‖e‖` using `hen ▸ (norm_nonneg _).trans_lt hpγ`.

Establish `he'0 : e' ≠ 0`. Introduce `h`. Rewrite `hee'` using `[h, zero_pow (Fact.out : p.Prime).ne_zero]`. Rewrite `he0` using `[← hee', norm_zero]`. Conclude with `lt_irrefl _ he0`.

Use `set base := ‖(p : K)‖ / ‖e‖ with hbase`. Establish `hbase0 : 0 ≤ base` using `div_nonneg (norm_nonneg _) he0.le`. Establish `hbase1 : base < 1` using `by rw [hbase, div_lt_one he0, hen]; exact hpγ`. Establish `hpn : (p : ℝ) ≠ 0` using `by exact_mod_cast (Fact.out : p.Prime).ne_zero`. Use `set r0 := base ^ ((p : ℝ)⁻¹) with hr0def`.

Establish `hr01 : r0 < 1` using `Real.rpow_lt_one hbase0 hbase1 (inv_pos.2 (by positivity))`. Take `⟨πK, hπ1, hπ2⟩` from `IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r0 hr01`. Use `⟨πK, hπ2, fun y hyF hy1 => ?_⟩` and prove the remaining obligations. Establish `hbaseπ : base ≤ ‖πK‖ ^ p`. Establish `h1 : r0 ^ p = base` using `Real.rpow_inv_natCast_pow hbase0 (Fact.out : p.Prime).ne_zero`.

Rewrite using `[← h1]`. Conclude with `pow_le_pow_left₀ (Real.rpow_nonneg hbase0 _) hπ1.le p`. Take `⟨l, hl⟩` from `(Submodule.mem_span_range_iff_exists_fun K).1 (hsub y hyF)`. Establish `hlb : ∀ i, ‖e * l i‖ ≤ 1`. Introduce `i`.

Establish `h1` using `hest l i`. Rewrite `h1` using `[hl]`. Rewrite using `[norm_mul, hen]`. Combine the equalities or inequalities in the displayed calculation. Use `choose a ha using fun i => exists_mk_untilt_eq (p := p) (⟨e * l i, mem_normInteger.2 (hlb i)⟩ : normInteger K)`.

Establish `ha' : ∀ i, ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ ≤ ‖(p : K)‖` using `fun i => mk_eq_mk_iff_norm_sub_le.1 (ha i)`. Use `choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hnorm i).1`. Use `set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)`. Establish `hφmem : ∀ c : 𝒪K♭, φ c ∈ integerTilt K C p N` using `fun c => by`. Rewrite using `[mem_integerTilt]`.

Establish `: algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ c) = algebraMap 𝒪C♭ C♭ (φ c)` using `tiltMap_algebraMap _ _ c`. Rewrite using `[← this]`. Conclude with `N.algebraMap_mem _`. Establish `hωmem : ∀ i, ω i ∈ integerTilt K C p N` using `fun i => by`. Rewrite using `[mem_integerTilt, hω]`.

Conclude with `hwN i`. Use `set X : 𝒪C♭ := ∑ i, φ (a i) * ω i`. Establish `hXmem : X ∈ integerTilt K C p N` using `Subring.sum_mem _ fun i _ => mul_mem (hφmem _) (hωmem i)`. Use `set X' := (frobeniusEquiv 𝒪C♭ p).symm X`. Establish `hX'mem : X' ∈ integerTilt K C p N` using `frobeniusEquiv_symm_mem_integerTilt hXmem`.

Establish `hX'p : ((PreTilt.untilt X' : normInteger C) : C) ^ p = ((PreTilt.untilt X : normInteger C) : C)`. Rewrite using `[← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]`. Use `set q : C := ((PreTilt.untilt X' : normInteger C) : C) / algebraMap K C e'`. Establish `hqF : q ∈ untiltField K C p N` using `div_mem (coe_mem_untiltField (untilt_mem_untiltInteger hX'mem)) (IntermediateField.algebraMap_mem _ _)`. Establish `hqp : q ^ p = ((PreTilt.untilt X : normInteger C) : C) / algebraMap K C e`.

Rewrite using `[div_pow, hX'p, ← map_pow, hee']`. Establish `hterm : ∀ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) = ((PreTilt.untilt (a i) : normInteger K) : K) • tiltSharp C p (w i)`. Introduce `i`. Rewrite using `[map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω, tiltSharp_algebraMap]`. Establish `h1 : ‖algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤ ‖(p : K)‖`.

Establish `: algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) = ∑ i, (e * l i - ((PreTilt.untilt (a i) : normInteger K) : K)) • tiltSharp C p (w i)`. Rewrite using `[← hl, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hterm]`. Simplify using `only [Algebra.smul_def, map_mul, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, norm_tiltSharp, norm_sub_rev]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : ‖((PreTilt.untilt X : normInteger C) : C) - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤ ‖(p : K)‖`. Rewrite using `[← norm_natCast_algebra (K := K) (C := C)]`. Conclude with `norm_untilt_sum_sub_le Finset.univ fun i => φ (a i) * ω i`. Establish `h3 : ‖algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)‖ ≤ ‖(p : K)‖`. Establish `: algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C) = (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) - (((PreTilt.untilt X : normInteger C) : C) - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C))` using `by ring`.

Rewrite using `[this]`. Use `IsUltrametricDist.norm_add_le_max (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) (-(((PreTilt.untilt X : normInteger C) : C) - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)))` as an intermediate fact. Rewrite `this` using `[norm_neg, ← sub_eq_add_neg]`. Conclude with `this.trans (max_le h1 h2)`. Establish `hae : algebraMap K C e ≠ 0` using `(map_ne_zero _).2 (fun h => by rw [h, norm_zero] at he0; exact lt_irrefl _ he0)`.

Establish `hyq : ‖y - q ^ p‖ ≤ base`. Establish `: y - q ^ p = (algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)) / algebraMap K C e`. Rewrite using `[hqp]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, norm_div, norm_algebraMap', hbase]`.

Conclude with `div_le_div_of_nonneg_right h3 he0.le`. Use `⟨q, hqF, ?_, hyq.trans hbaseπ⟩` and prove the remaining obligations. Establish `hqp1 : ‖q‖ ^ p ≤ 1`. Rewrite using `[← norm_pow]`. Establish `: q ^ p = y - (y - q ^ p)` using `by ring`.

Rewrite using `[this]`. Use `IsUltrametricDist.norm_add_le_max y (-(y - q ^ p))` as an intermediate fact. Rewrite `this` using `[norm_neg, ← sub_eq_add_neg]`. Conclude with `this.trans (max_le hy1 (hyq.trans hbase1.le))`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).1 hqp1`.
-/
theorem exists_norm_sub_pow_le_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    ∃ πK : K, ‖πK‖ < 1 ∧ ∀ y ∈ untiltField K C p N, ‖y‖ ≤ 1 →
      ∃ q ∈ untiltField K C p N, ‖q‖ ≤ 1 ∧ ‖y - q ^ p‖ ≤ ‖πK‖ ^ p := by
  classical
  obtain ⟨w, t, r, ρ, ht0, ht1, hr0, hr1, hρ0, hρ1, hp, hwN, hnorm, -, horth, -, -, hsub⟩ :=
    exists_untiltField_basis (K := K) (C := C) (p := p) N
  set ρ' := (1 + ρ) / 2 with hρ'
  have hρρ' : ρ < ρ' := by rw [hρ']; linarith
  have hρ'1 : ρ' < 1 := by rw [hρ']; linarith
  have hρ'0 : 0 < ρ' := hρ0.trans hρρ'
  have htr : 0 < t * r := mul_pos ht0 hr0
  have hp' : ‖(p : K)‖ ≤ t * r * ρ' := hp.trans (by gcongr)
  have hpstrict : ‖(p : K)‖ < t * r * ρ' :=
    hp.trans_lt (mul_lt_mul_of_pos_left hρρ' htr)
  have hest := fun l i => mul_norm_le_norm_sum_smul_tiltSharp (K := K) (C := C) (p := p) horth
    (fun i => (hnorm i).1) (fun i => (hnorm i).2) ht0 hr0.le hρ'0 hρ'1 hp' l i
  set b := t * r * ρ' with hbdef
  have hb0 : 0 < b := mul_pos htr hρ'0
  have hb1 : b ≤ 1 := by
    have : t * r ≤ 1 := by nlinarith
    calc b = t * r * ρ' := rfl
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := one_mul 1

  obtain ⟨ε, hε1, hε2⟩ := exists_norm_mem_Ioc (K := K♭) p
    (lt_max_of_lt_right (half_pos hb0)) (max_lt hpstrict (half_lt_self hb0))
  obtain ⟨γ, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 (hε2.trans hb1)
  rw [norm_algebraMap_preTilt] at hε1 hε2
  have hpγ : ‖(p : K)‖ < ‖γ‖ := (le_max_left _ _).trans_lt hε1
  set γ' := (frobeniusEquiv 𝒪K♭ p).symm γ
  set e : K := ((PreTilt.untilt γ : normInteger K) : K) with he
  set e' : K := ((PreTilt.untilt γ' : normInteger K) : K) with he'
  have hee' : e' ^ p = e := by
    rw [he', he, ← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  have hen : ‖e‖ = ‖γ‖ := (preTilt_norm_def γ).symm
  have he0 : 0 < ‖e‖ := hen ▸ (norm_nonneg _).trans_lt hpγ
  have he'0 : e' ≠ 0 := by
    intro h; rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at hee'
    rw [← hee', norm_zero] at he0; exact lt_irrefl _ he0
  set base := ‖(p : K)‖ / ‖e‖ with hbase
  have hbase0 : 0 ≤ base := div_nonneg (norm_nonneg _) he0.le
  have hbase1 : base < 1 := by rw [hbase, div_lt_one he0, hen]; exact hpγ
  have hpn : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  set r0 := base ^ ((p : ℝ)⁻¹) with hr0def
  have hr01 : r0 < 1 := Real.rpow_lt_one hbase0 hbase1 (inv_pos.2 (by positivity))
  obtain ⟨πK, hπ1, hπ2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r0 hr01
  refine ⟨πK, hπ2, fun y hyF hy1 => ?_⟩
  have hbaseπ : base ≤ ‖πK‖ ^ p := by
    have h1 : r0 ^ p = base := Real.rpow_inv_natCast_pow hbase0 (Fact.out : p.Prime).ne_zero
    rw [← h1]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hbase0 _) hπ1.le p

  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hsub y hyF)
  have hlb : ∀ i, ‖e * l i‖ ≤ 1 := by
    intro i
    have h1 := hest l i
    rw [hl] at h1
    rw [norm_mul, hen]
    calc ‖γ‖ * ‖l i‖ ≤ b * ‖l i‖ := by gcongr
      _ ≤ ‖y‖ := h1
      _ ≤ 1 := hy1
  choose a ha using fun i => exists_mk_untilt_eq (p := p)
    (⟨e * l i, mem_normInteger.2 (hlb i)⟩ : normInteger K)
  have ha' : ∀ i, ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ ≤ ‖(p : K)‖ :=
    fun i => mk_eq_mk_iff_norm_sub_le.1 (ha i)
  choose ω hω using fun i => (norm_le_one_iff_exists_algebraMap (K := C) (p := p)).1 (hnorm i).1
  set φ := preTiltMap p (algebraMap K C) (norm_algebraMap' C)
  have hφmem : ∀ c : 𝒪K♭, φ c ∈ integerTilt K C p N := fun c => by
    rw [mem_integerTilt]
    have : algebraMap K♭ C♭ (algebraMap 𝒪K♭ K♭ c) = algebraMap 𝒪C♭ C♭ (φ c) :=
      tiltMap_algebraMap _ _ c
    rw [← this]; exact N.algebraMap_mem _
  have hωmem : ∀ i, ω i ∈ integerTilt K C p N := fun i => by
    rw [mem_integerTilt, hω]; exact hwN i
  set X : 𝒪C♭ := ∑ i, φ (a i) * ω i
  have hXmem : X ∈ integerTilt K C p N :=
    Subring.sum_mem _ fun i _ => mul_mem (hφmem _) (hωmem i)
  set X' := (frobeniusEquiv 𝒪C♭ p).symm X
  have hX'mem : X' ∈ integerTilt K C p N := frobeniusEquiv_symm_mem_integerTilt hXmem
  have hX'p : ((PreTilt.untilt X' : normInteger C) : C) ^ p = ((PreTilt.untilt X : normInteger C) : C) := by
    rw [← SubmonoidClass.coe_pow, ← map_pow, frobeniusEquiv_symm_pow_p]
  set q : C := ((PreTilt.untilt X' : normInteger C) : C) / algebraMap K C e'
  have hqF : q ∈ untiltField K C p N :=
    div_mem (coe_mem_untiltField (untilt_mem_untiltInteger hX'mem))
      (IntermediateField.algebraMap_mem _ _)
  have hqp : q ^ p = ((PreTilt.untilt X : normInteger C) : C) / algebraMap K C e := by
    rw [div_pow, hX'p, ← map_pow, hee']

  have hterm : ∀ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
      ((PreTilt.untilt (a i) : normInteger K) : K) • tiltSharp C p (w i) := by
    intro i
    rw [map_mul, Subring.coe_mul, coe_untilt_preTiltMap, Algebra.smul_def, ← hω,
      tiltSharp_algebraMap]
  have h1 : ‖algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤
      ‖(p : K)‖ := by
    have : algebraMap K C e * y -
        ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C) =
        ∑ i, (e * l i - ((PreTilt.untilt (a i) : normInteger K) : K)) • tiltSharp C p (w i) := by
      rw [← hl, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm]
      simp only [Algebra.smul_def, map_mul, map_sub]
      ring
    rw [this]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_smul, norm_tiltSharp, norm_sub_rev]
    calc ‖((PreTilt.untilt (a i) : normInteger K) : K) - e * l i‖ * ‖w i‖
        ≤ ‖(p : K)‖ * 1 := mul_le_mul (ha' i) (hnorm i).1 (norm_nonneg _) (norm_nonneg _)
      _ = _ := mul_one _
  have h2 : ‖((PreTilt.untilt X : normInteger C) : C) -
      ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    rw [← norm_natCast_algebra (K := K) (C := C)]
    exact norm_untilt_sum_sub_le Finset.univ fun i => φ (a i) * ω i
  have h3 : ‖algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
    have : algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C) =
        (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) -
        (((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max
      (algebraMap K C e * y - ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C))
      (-(((PreTilt.untilt X : normInteger C) : C) -
          ∑ i, ((PreTilt.untilt (φ (a i) * ω i) : normInteger C) : C)))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le h1 h2)
  have hae : algebraMap K C e ≠ 0 :=
    (map_ne_zero _).2 (fun h => by rw [h, norm_zero] at he0; exact lt_irrefl _ he0)
  have hyq : ‖y - q ^ p‖ ≤ base := by
    have : y - q ^ p = (algebraMap K C e * y - ((PreTilt.untilt X : normInteger C) : C)) /
        algebraMap K C e := by
      rw [hqp]; field_simp
    rw [this, norm_div, norm_algebraMap', hbase]
    exact div_le_div_of_nonneg_right h3 he0.le
  refine ⟨q, hqF, ?_, hyq.trans hbaseπ⟩
  have hqp1 : ‖q‖ ^ p ≤ 1 := by
    rw [← norm_pow]
    have : q ^ p = y - (y - q ^ p) := by ring
    rw [this]
    have := IsUltrametricDist.norm_add_le_max y (-(y - q ^ p))
    rw [norm_neg, ← sub_eq_add_neg] at this
    exact this.trans (max_le hy1 (hyq.trans hbase1.le))
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).1 hqp1

instance isPerfectoidField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    IsPerfectoidField (untiltField K C p N) p := by
  have := IsPerfectoidField.completeSpace (K := K) p
  have : CompleteSpace (untiltField K C p N) := FiniteDimensional.complete K _
  obtain ⟨πK, hπ, h⟩ := exists_norm_sub_pow_le_untiltField (K := K) (C := C) (p := p) N
  refine IsPerfectoidField.of_norm_sub_pow_le p ?_ ?_ (π := algebraMap K _ πK) ?_ ?_
  · change ‖((p : untiltField K C p N) : C)‖ < 1
    rw [show ((p : untiltField K C p N) : C) = (p : C) from map_natCast (untiltField K C p N).val p,
      norm_natCast_algebra (K := K)]
    exact IsPerfectoidField.norm_natCast_lt_one
  · intro r hr
    obtain ⟨x, hx1, hx2⟩ := IsPerfectoidField.exists_norm_mem_Ioo (K := K) (p := p) r hr
    refine ⟨algebraMap K _ x, ?_, ?_⟩ <;> rw [norm_algebraMap'] <;> assumption
  · rw [norm_algebraMap']; exact hπ
  · intro x hx
    obtain ⟨q, hqF, hq1, hq⟩ := h x x.2 hx
    refine ⟨⟨q, hqF⟩, hq1, ?_⟩
    rw [norm_algebraMap']
    exact hq

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact ha`. Consider the case `succ n ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `frobeniusEquiv_symm_mem_integerTilt ih`.
-/
theorem iterate_frobeniusEquiv_symm_mem_integerTilt {N : IntermediateField K♭ C♭}
    [FiniteDimensional K♭ N] {a : 𝒪C♭} (ha : a ∈ integerTilt K C p N) (n : ℕ) :
    (frobeniusEquiv 𝒪C♭ p).symm^[n] a ∈ integerTilt K C p N := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact frobeniusEquiv_symm_mem_integerTilt ih

/- English proof (translation)
Establish `key : ∀ z ∈ N, ‖z‖ ≤ 1 → z ∈ tiltIntermediateField p (untiltField K C p N)`. Introduce `z hz hz1`. Take `⟨a, rfl⟩` from `norm_le_one_iff_exists_algebraMap.1 hz1`. Establish `ha : a ∈ integerTilt K C p N` using `(mem_integerTilt N).2 hz`. Conclude with `algebraMap_mem_tiltIntermediateField _ fun n => coe_mem_untiltField (untilt_mem_untiltInteger (iterate_frobeniusEquiv_symm_mem_integerTilt ha n))`.

Introduce `z hz`. Break down `le_or_gt ‖z‖ 1 with h | h` into its components or cases. Conclude with `key z hz h`. Establish `h0 : z ≠ 0` using `by rintro rfl; rw [norm_zero] at h; linarith`. Use `key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)` as an intermediate fact.

Simplify using `using inv_mem this`.
-/
theorem le_tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ N] : N ≤ tiltIntermediateField p (untiltField K C p N) := by
  have key : ∀ z ∈ N, ‖z‖ ≤ 1 → z ∈ tiltIntermediateField p (untiltField K C p N) := by
    intro z hz hz1
    obtain ⟨a, rfl⟩ := norm_le_one_iff_exists_algebraMap.1 hz1
    have ha : a ∈ integerTilt K C p N := (mem_integerTilt N).2 hz
    exact algebraMap_mem_tiltIntermediateField _ fun n =>
      coe_mem_untiltField (untilt_mem_untiltInteger (iterate_frobeniusEquiv_symm_mem_integerTilt ha n))
  intro z hz
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact key z hz h
  · have h0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at h; linarith
    have := key z⁻¹ (inv_mem hz) (by rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le)
    simpa using inv_mem this

/- English proof (translation)
Use `set T := tiltIntermediateField p (untiltField K C p N)`. Establish `hle` using `le_tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N`. Establish `hbound : ∀ s : Finset T, LinearIndependent K♭ (fun i : s => (i : T)) → s.card ≤ Module.finrank K (untiltField K C p N)`. Introduce `s hs`. Establish `hv : LinearIndependent K♭ (fun i : s => ((i : T) : C♭))` using `hs.map' T.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)`.

Take `⟨w, hw, -, -, hli⟩` from `exists_tiltSharp_linearIndependent (K := K) (C := C) hv`. Establish `hwT : ∀ i, w i ∈ T` using `fun i => by`. Establish `hsp : Submodule.span K♭ (Set.range fun i : s => ((i : T) : C♭)) ≤ Subalgebra.toSubmodule T.toSubalgebra` using `Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ((j : T)).2)`. Conclude with `hsp (hw i)`. Set `u : s → untiltField K C p N` to `fun i => ⟨tiltSharp C p (w i), tiltSharp_mem_of_mem_tiltIntermediateField _ (hwT i)⟩`.

Establish `hu : LinearIndependent K u` using `LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli`. Simplify using `using hu.fintype_card_le_finrank`. Establish `hrank : Module.rank K♭ T ≤ Module.finrank K (untiltField K C p N)` using `rank_le hbound`. Establish `hfin : FiniteDimensional K♭ T` using `Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)`. Establish `hfr : Module.finrank K♭ T ≤ Module.finrank K♭ N`.

Rewrite using `[← finrank_untiltField (K := K) (C := C) (p := p) N]`. Conclude with `Module.finrank_le_of_rank_le hrank`. Conclude with `(IntermediateField.eq_of_le_of_finrank_le hle hfr).symm`.
-/
theorem tiltIntermediateField_untiltField (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] :
    tiltIntermediateField p (untiltField K C p N) = N := by
  classical
  set T := tiltIntermediateField p (untiltField K C p N)
  have hle := le_tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N

  have hbound : ∀ s : Finset T, LinearIndependent K♭ (fun i : s => (i : T)) →
      s.card ≤ Module.finrank K (untiltField K C p N) := by
    intro s hs
    have hv : LinearIndependent K♭ (fun i : s => ((i : T) : C♭)) :=
      hs.map' T.val.toLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    obtain ⟨w, hw, -, -, hli⟩ := exists_tiltSharp_linearIndependent (K := K) (C := C) hv
    have hwT : ∀ i, w i ∈ T := fun i => by
      have hsp : Submodule.span K♭ (Set.range fun i : s => ((i : T) : C♭)) ≤
          Subalgebra.toSubmodule T.toSubalgebra :=
        Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact ((j : T)).2)
      exact hsp (hw i)
    let u : s → untiltField K C p N := fun i =>
      ⟨tiltSharp C p (w i), tiltSharp_mem_of_mem_tiltIntermediateField _ (hwT i)⟩
    have hu : LinearIndependent K u :=
      LinearIndependent.of_comp (IntermediateField.val _).toLinearMap hli
    simpa using hu.fintype_card_le_finrank
  have hrank : Module.rank K♭ T ≤ Module.finrank K (untiltField K C p N) := rank_le hbound
  have hfin : FiniteDimensional K♭ T :=
    Module.rank_lt_aleph0_iff.1 (hrank.trans_lt Cardinal.natCast_lt_aleph0)
  have hfr : Module.finrank K♭ T ≤ Module.finrank K♭ N := by
    rw [← finrank_untiltField (K := K) (C := C) (p := p) N]
    exact Module.finrank_le_of_rank_le hrank
  exact (IntermediateField.eq_of_le_of_finrank_le hle hfr).symm

/- English proof (translation)
Use `set F := untiltField K C p N`. Take `⟨b, hb⟩` from `exists_mk_untilt_eq (K := F) (p := p) ⟨⟨y, hy⟩, mem_normInteger.2 hy1⟩`. Rewrite `hb` using `[mk_eq_mk_iff_norm_sub_le]`. Use `set a := preTiltMap p (F.val : F →+* C) (norm_val F) b`. Establish `hacoe : ((PreTilt.untilt a : normInteger C) : C) = (((PreTilt.untilt b : normInteger F) : F) : C)` using `coe_untilt_preTiltMap _ _ b`.

Establish `haN : a ∈ integerTilt K C p N`. Rewrite using `[mem_integerTilt, ← tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N]`. Use `⟨algebraMap _ _ b, ?_⟩` and prove the remaining obligations. Rewrite using `[tiltInclusion, tiltMap_algebraMap]`. Use `⟨a, haN, ?_⟩` and prove the remaining obligations.

Rewrite using `[hacoe, norm_sub_rev]`. Establish `hpF : ‖(p : F)‖ = ‖(p : K)‖`. Express the relevant statement in the definitionally equal form `‖((p : F) : C)‖ = _`. Rewrite using `[show ((p : F) : C) = (p : C) from map_natCast F.val p, norm_natCast_algebra (K := K)]`. Rewrite using `[← hpF]`.

Conclude with `hb`.
-/
theorem exists_norm_sub_untilt_le (N : IntermediateField K♭ C♭) [FiniteDimensional K♭ N] {y : C}
    (hy : y ∈ untiltField K C p N) (hy1 : ‖y‖ ≤ 1) :
    ∃ a ∈ integerTilt K C p N, ‖y - ((PreTilt.untilt a : normInteger C) : C)‖ ≤ ‖(p : K)‖ := by
  set F := untiltField K C p N
  obtain ⟨b, hb⟩ := exists_mk_untilt_eq (K := F) (p := p) ⟨⟨y, hy⟩, mem_normInteger.2 hy1⟩
  rw [mk_eq_mk_iff_norm_sub_le] at hb
  set a := preTiltMap p (F.val : F →+* C) (norm_val F) b
  have hacoe : ((PreTilt.untilt a : normInteger C) : C) =
      (((PreTilt.untilt b : normInteger F) : F) : C) :=
    coe_untilt_preTiltMap _ _ b
  have haN : a ∈ integerTilt K C p N := by
    rw [mem_integerTilt, ← tiltIntermediateField_untiltField (K := K) (C := C) (p := p) N]
    refine ⟨algebraMap _ _ b, ?_⟩
    rw [tiltInclusion, tiltMap_algebraMap]
  refine ⟨a, haN, ?_⟩
  rw [hacoe, norm_sub_rev]
  have hpF : ‖(p : F)‖ = ‖(p : K)‖ := by
    change ‖((p : F) : C)‖ = _
    rw [show ((p : F) : C) = (p : C) from map_natCast F.val p, norm_natCast_algebra (K := K)]
  rw [← hpF]
  exact hb

end GroundTheory.PAdicHodge
