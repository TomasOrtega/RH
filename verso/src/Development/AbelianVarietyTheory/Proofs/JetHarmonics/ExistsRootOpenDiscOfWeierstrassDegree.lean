import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerSeriesEvalTsumUnitDiscPropertiesStatement
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.DiscRoot

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def ball (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_setOf_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := fun {a} ha => by simpa using ha

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Establish `ha : ‖(a : K)‖ ≤ 1` using `a.2`. Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]`.

Conclude with `mul_le_of_le_one_left (by positivity) ha`. Introduce `h`. Distinguish the cases in `hp : (p : K) ^ n = 0`. Rewrite `h` using `[← norm_pow, hp, norm_zero, norm_le_zero_iff]`. Conclude with `⟨0, Subtype.ext (by simp [h])⟩`.

Use `⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖(x : K) / p ^ n‖ ≤ 1`. Rewrite using `[norm_div, norm_pow]`. Conclude with `div_le_one_of_le₀ h (by positivity)`. Simplify using `only [Subring.coe_mul, SubmonoidClass.coe_pow]`.

Conclude with `div_mul_cancel₀ _ hp`.
-/
theorem mem_span_pow (p x : ball K) (n : ℕ) :
    x ∈ Ideal.span {p} ^ n ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩
    have ha : ‖(a : K)‖ ≤ 1 := a.2
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) ha
  · intro h
    by_cases hp : (p : K) ^ n = 0
    · rw [← norm_pow, hp, norm_zero, norm_le_zero_iff] at h
      exact ⟨0, Subtype.ext (by simp [h])⟩
    · refine ⟨⟨x / p ^ n, ?_⟩, Subtype.ext ?_⟩
      · change ‖(x : K) / p ^ n‖ ≤ 1
        rw [norm_div, norm_pow]
        exact div_le_one_of_le₀ h (by positivity)
      · simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
        exact div_mul_cancel₀ _ hp

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]`. Both sides reduce to the same expression.
-/
theorem smod_iff (p x y : ball K) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule (ball K) (ball K))] ↔
      ‖(x : K) - y‖ ≤ ‖(p : K)‖ ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_pow]
  rfl

/- English proof (translation)
Establish `ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp`. Establish `hH : IsHausdorff (Ideal.span {p}) (ball K)` using `⟨fun x hx => by`. Establish `: ‖(x : K)‖ ≤ 0` using `ge_of_tendsto' ht fun n => by`. Simplify using `using (smod_iff p x 0 n).1 (hx n)`. Conclude with `Subtype.ext (by simpa using this)⟩`.

Establish `hP : IsPrecomplete (Ideal.span {p}) (ball K)` using `⟨fun f hf => by`. Establish `hc : CauchySeq fun n => (f n : K)`. Use `cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht` and prove the remaining obligations. Rewrite using `[dist_eq_norm]`. Conclude with `(smod_iff p _ _ n).1 (hf hnm)`.

Take `⟨L, hL⟩` from `cauchySeq_tendsto_of_complete hc`. Establish `hL1 : ‖L‖ ≤ 1` using `le_of_tendsto' hL.norm fun n => (f n).2`. Use `⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩` and prove the remaining obligations. Use `le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop n] with m hm`.

Conclude with `(smod_iff p _ _ n).1 (hf hm)⟩`. Conclude with `{ toIsHausdorff := hH, toIsPrecomplete := hP }`.
-/
theorem adicComplete [CompleteSpace K] (p : ball K) (hp : ‖(p : K)‖ < 1) :
    IsAdicComplete (Ideal.span {p}) (ball K) := by
  have ht : Filter.Tendsto (fun n : ℕ => ‖(p : K)‖ ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hp
  have hH : IsHausdorff (Ideal.span {p}) (ball K) := ⟨fun x hx => by
    have : ‖(x : K)‖ ≤ 0 := ge_of_tendsto' ht fun n => by
      simpa using (smod_iff p x 0 n).1 (hx n)
    exact Subtype.ext (by simpa using this)⟩
  have hP : IsPrecomplete (Ideal.span {p}) (ball K) := ⟨fun f hf => by
    have hc : CauchySeq fun n => (f n : K) := by
      refine cauchySeq_of_le_tendsto_0' (fun n => ‖(p : K)‖ ^ n) (fun n m hnm => ?_) ht
      rw [dist_eq_norm]
      exact (smod_iff p _ _ n).1 (hf hnm)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => (f n).2
    refine ⟨⟨L, hL1⟩, fun n => (smod_iff p _ _ n).2 ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds (x := (f n : K))).sub hL).norm ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    exact (smod_iff p _ _ n).1 (hf hm)⟩
  exact { toIsHausdorff := hH, toIsPrecomplete := hP }

/- English proof (translation)
Take `⟨k, hk, hmax⟩` from `Finset.exists_max_image (Finset.range d) (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩`. Set `g : PowerSeries (ball K)` to `PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩`. Establish `hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h` using `fun n => by`. Simplify using `[g]`. Set `p : ball K` to `PowerSeries.coeff k g`.

Establish `hp : ‖(p : K)‖ < 1` using `by rw [hg]; exact hl k (Finset.mem_range.1 hk)`. Use `set I : Ideal (ball K) := Ideal.span {p} with hI`. Establish `hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖` using `fun x => by`. Simplify using `using mem_span_pow p x 1`. Establish `hlow : ∀ j < d, PowerSeries.coeff j g ∈ I` using `fun j hj => by`.

Rewrite using `[hmem, hg, hg]`. Conclude with `hmax j (Finset.mem_range.2 hj)`. Establish `hord : (g.map (Ideal.Quotient.mk I)).order = d`. Rewrite using `[PowerSeries.order_eq_nat]`. Use `⟨?_, fun i hi => ?_⟩` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]`. Conclude with `not_le.2 hp`. Rewrite using `[PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hlow i hi`. Establish `hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d` using `by rw [hord]; rfl`.

Establish `H : g.IsWeierstrassDivisorAt I`. Rewrite using `[PowerSeries.IsWeierstrassDivisorAt, hord']`. Establish `h0 : PowerSeries.coeff d h ≠ 0`. Introduce `h0`. Rewrite `h1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one h1`. Use `IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1`. Rewrite using `[norm_inv, h1, inv_one]`. Rewrite using `[Subring.coe_mul, hg]`.

Conclude with `mul_inv_cancel₀ h0`. Use `haveI := adicComplete p hp`. Establish `HD` using `H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)`. Use `set q := H.div (PowerSeries.X ^ d)`. Use `set r := H.mod (PowerSeries.X ^ d)`.

Establish `hdeg : r.degree < d` using `hord' ▸ HD.degree_lt`. Establish `hgh : g.map (ball K).subtype = h`. Use extensionality with `n`. Simplify using `[hg]`. Use `⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_, lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_map]`. Conclude with `(PowerSeries.coeff n q).2`. Establish `e` using `congrArg (PowerSeries.coeff d) HD.eq_mul_add`. Rewrite `e` using `[g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add, map_add, PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul]`. Rewrite `e` using `[Finset.Nat.antidiagonal_zero, Finset.sum_singleton]`.

Establish `e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I`. Use `PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_coe, PowerSeries.coeff_trunc]`. Use `split_ifs with hh`. Conclude with `hlow i hh`.

Conclude with `zero_mem _`. Establish `e3` using `((hmem _).1 e2).trans_lt hp`. Establish `e4` using `congrArg (fun z : ball K => (z : K)) e`. Simplify using `only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4`. Rewrite using `[PowerSeries.coeff_map]`.

Use `le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)` and prove the remaining obligations. Establish `e5` using `congrArg norm e4`. Rewrite `e5` using `[norm_one]`. Use `absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))` and prove the remaining obligations. Rewrite using `[norm_mul, h1, one_mul]`.

Conclude with `hlt`. Rewrite using `[Polynomial.coeff_map]`. Distinguish the cases in `hn : n < d`. Use `HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)` as an intermediate fact. Rewrite `this` using `[map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff, Polynomial.coeff_coe]`.

Conclude with `((hmem _).1 this).trans_lt hp`. Rewrite using `[Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]`. Simplify using the standard rewrite rules. Use `congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add` as an intermediate fact. Rewrite `this` using `[map_pow, PowerSeries.map_X, map_add, map_mul, hgh]`.

Rewrite using `[this, Polynomial.polynomial_map_coe]`.
-/
theorem division [CompleteSpace K] (h : PowerSeries K) (d : ℕ) (hd : 0 < d)
    (hi : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff d h‖ = 1)
    (hl : ∀ k < d, ‖PowerSeries.coeff k h‖ < 1) :
    ∃ (q : PowerSeries K) (r : Polynomial K), (∀ n, ‖PowerSeries.coeff n q‖ ≤ 1) ∧
      ‖PowerSeries.coeff 0 q‖ = 1 ∧ r.degree < d ∧ (∀ n, ‖r.coeff n‖ < 1) ∧
      PowerSeries.X ^ d = h * q + (r : PowerSeries K) := by
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.range d)
    (fun k => ‖PowerSeries.coeff k h‖) ⟨0, Finset.mem_range.2 hd⟩
  let g : PowerSeries (ball K) := PowerSeries.mk fun n => ⟨PowerSeries.coeff n h, hi n⟩
  have hg : ∀ n, ((PowerSeries.coeff n g : ball K) : K) = PowerSeries.coeff n h := fun n => by
    simp [g]
  let p : ball K := PowerSeries.coeff k g
  have hp : ‖(p : K)‖ < 1 := by rw [hg]; exact hl k (Finset.mem_range.1 hk)
  set I : Ideal (ball K) := Ideal.span {p} with hI
  have hmem : ∀ x : ball K, x ∈ I ↔ ‖(x : K)‖ ≤ ‖(p : K)‖ := fun x => by
    simpa using mem_span_pow p x 1
  have hlow : ∀ j < d, PowerSeries.coeff j g ∈ I := fun j hj => by
    rw [hmem, hg, hg]; exact hmax j (Finset.mem_range.2 hj)
  have hord : (g.map (Ideal.Quotient.mk I)).order = d := by
    rw [PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi => ?_⟩
    · rw [PowerSeries.coeff_map, Ne, Ideal.Quotient.eq_zero_iff_mem, hmem, hg, h1]
      exact not_le.2 hp
    · rw [PowerSeries.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
      exact hlow i hi
  have hord' : (g.map (Ideal.Quotient.mk I)).order.toNat = d := by rw [hord]; rfl
  have H : g.IsWeierstrassDivisorAt I := by
    rw [PowerSeries.IsWeierstrassDivisorAt, hord']
    have h0 : PowerSeries.coeff d h ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h1; exact zero_ne_one h1
    refine IsUnit.of_mul_eq_one ⟨(PowerSeries.coeff d h)⁻¹, ?_⟩ (Subtype.ext ?_)
    · change ‖(PowerSeries.coeff d h)⁻¹‖ ≤ 1
      rw [norm_inv, h1, inv_one]
    · rw [Subring.coe_mul, hg]
      exact mul_inv_cancel₀ h0
  haveI := adicComplete p hp
  have HD := H.isWeierstrassDivisionAt_div_mod (PowerSeries.X ^ d)
  set q := H.div (PowerSeries.X ^ d)
  set r := H.mod (PowerSeries.X ^ d)
  have hdeg : r.degree < d := hord' ▸ HD.degree_lt
  have hgh : g.map (ball K).subtype = h := by
    ext n; simp [hg]
  refine ⟨q.map (ball K).subtype, r.map (ball K).subtype, fun n => ?_, ?_,
    lt_of_le_of_lt (Polynomial.degree_map_le) hdeg, fun n => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff n q).2
  · have e := congrArg (PowerSeries.coeff d) HD.eq_mul_add
    rw [g.eq_X_pow_mul_shift_add_trunc d, add_mul, mul_assoc, map_add, map_add,
      PowerSeries.coeff_X_pow_self, Polynomial.coeff_coe,
      Polynomial.coeff_eq_zero_of_degree_lt hdeg, add_zero, PowerSeries.coeff_X_pow_mul',
      if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_mul] at e
    rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton] at e
    have e2 : PowerSeries.coeff d (((g.trunc d : Polynomial (ball K)) : PowerSeries (ball K)) * q) ∈ I := by
      refine PowerSeries.coeff_mul_mem_ideal_of_coeff_left_mem_ideal' (fun i => ?_) d
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hh
      · exact hlow i hh
      · exact zero_mem _
    have e3 := ((hmem _).1 e2).trans_lt hp
    have e4 := congrArg (fun z : ball K => (z : K)) e
    simp only [PowerSeries.coeff_mk, zero_add, Subring.coe_add, Subring.coe_mul, hg, OneMemClass.coe_one] at e4
    rw [PowerSeries.coeff_map]
    refine le_antisymm (PowerSeries.coeff 0 q).2 (not_lt.1 fun hlt => ?_)
    have e5 := congrArg norm e4
    rw [norm_one] at e5
    refine absurd (e5.le.trans (IsUltrametricDist.norm_add_le_max _ _)) (not_le.2 (max_lt ?_ e3))
    rw [norm_mul, h1, one_mul]
    exact hlt
  · rw [Polynomial.coeff_map]
    by_cases hn : n < d
    · have := HD.coeff_f_sub_r_mem (i := n) (hord'.symm ▸ hn)
      rw [map_sub, PowerSeries.coeff_X_pow, if_neg hn.ne, zero_sub, neg_mem_iff,
        Polynomial.coeff_coe] at this
      exact ((hmem _).1 this).trans_lt hp
    · rw [Polynomial.coeff_eq_zero_of_degree_lt (hdeg.trans_le (by exact_mod_cast not_lt.1 hn))]
      simp
  · have := congrArg (PowerSeries.map (ball K).subtype) HD.eq_mul_add
    rw [map_pow, PowerSeries.map_X, map_add, map_mul, hgh] at this
    rw [this, Polynomial.polynomial_map_coe]

/- English proof (translation)
Establish `hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ)`. Rewrite using `[Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]), Polynomial.degree_X_pow]`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root (Polynomial.X ^ d - r) (by rw [hdeg]; exact_mod_cast hd.ne')`. Use `⟨x, not_le.1 fun h1 => ?_, hx⟩` and prove the remaining obligations. Establish `e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i`.

Use `hx.eq_zero` as an intermediate fact. Rewrite `this` using `[Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X]`. Rewrite using `[this]`. Distinguish the cases in `h0 : r = 0`. Simplify using `[h0]`.

Conclude with `Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x`. Take `⟨i, hi, hle⟩` from `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)`. Rewrite `hle` using `[← e, norm_mul, norm_pow, norm_pow]`. Establish `h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d` using `pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le`. Establish `h3 : 0 < ‖x‖ ^ i` using `by positivity`.

Establish `h4` using `hc i`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem root_small [IsAlgClosed K] (r : Polynomial K) (d : ℕ) (hd : 0 < d) (hr : r.degree < d)
    (hc : ∀ n, ‖r.coeff n‖ < 1) : ∃ x : K, ‖x‖ < 1 ∧ (Polynomial.X ^ d - r).eval x = 0 := by
  have hdeg : (Polynomial.X ^ d - r).degree = (d : WithBot ℕ) := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow]),
      Polynomial.degree_X_pow]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (Polynomial.X ^ d - r)
    (by rw [hdeg]; exact_mod_cast hd.ne')
  refine ⟨x, not_le.1 fun h1 => ?_, hx⟩
  have e : x ^ d = ∑ i ∈ Finset.range d, r.coeff i * x ^ i := by
    have := hx.eq_zero
    rw [Polynomial.eval_sub, sub_eq_zero, Polynomial.eval_pow, Polynomial.eval_X] at this
    rw [this]
    by_cases h0 : r = 0
    · simp [h0]
    exact Polynomial.eval_eq_sum_range' ((Polynomial.natDegree_lt_iff_degree_lt h0).2 hr) x
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
    (t := Finset.range d) ⟨0, Finset.mem_range.2 hd⟩ (fun i => r.coeff i * x ^ i)
  rw [← e, norm_mul, norm_pow, norm_pow] at hle
  have h2 : ‖x‖ ^ i ≤ ‖x‖ ^ d := pow_le_pow_right₀ h1 (Finset.mem_range.1 hi).le
  have h3 : 0 < ‖x‖ ^ i := by positivity
  have h4 := hc i
  nlinarith

end GlobalTheory.ConvSer.DiscRoot

/- English proof (translation)
Introduce `K _ _ _ _ h d hd hi h1 hl`. Take `⟨-, -, hA, -, -, -, -, -, -, hB⟩` from `GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit`. Take `⟨q, r, hq, hq0, hr, hrc, e⟩` from `DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl`. Take `⟨x, hx, hx0⟩` from `DiscRoot.root_small r d hd hr hrc`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Take `⟨-, hmul, -, -, hP, -, hI, -⟩` from `GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx`. Establish `hq' : Intg q` using `(hB q).1.2 hq`. Establish `e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q`. Rewrite using `[Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]`. Expand and normalize the polynomial expressions, which then agree.

Establish `e3` using `(hP (Polynomial.X ^ d - r)).2`. Rewrite `e3` using `[hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2]`. Use `(mul_eq_zero.1 e3).resolve_right fun h0 => ?_` and prove the remaining obligations. Use `(hI q hq').2.1` as an intermediate fact. Rewrite `this` using `[h0, zero_sub, norm_neg, hq0]`.

Conclude with `absurd hx (not_lt.2 this)`.
-/
theorem GlobalTheory.ConvSer.exists_root_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  intro K _ _ _ _ h d hd hi h1 hl
  obtain ⟨-, -, hA, -, -, -, -, -, -, hB⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit
  obtain ⟨q, r, hq, hq0, hr, hrc, e⟩ := DiscRoot.division h d hd ((hB h).1.1 hi) h1 hl
  obtain ⟨x, hx, hx0⟩ := DiscRoot.root_small r d hd hr hrc
  refine ⟨x, hx, ?_⟩
  obtain ⟨-, hmul, -, -, hP, -, hI, -⟩ := GlobalTheory.T.powerSeriesEvalTsum_unitDisc_properties_alt K x hx
  have hq' : Intg q := (hB q).1.2 hq
  have e2 : ((Polynomial.X ^ d - r : Polynomial K) : PowerSeries K) = h * q := by
    rw [Polynomial.coe_sub, Polynomial.coe_pow, Polynomial.coe_X, e]; ring
  have e3 := (hP (Polynomial.X ^ d - r)).2
  rw [hx0, e2, (hmul h q ((hA h 0).2.2 hi) ((hA q 0).2.2 hq')).2.2] at e3
  refine (mul_eq_zero.1 e3).resolve_right fun h0 => ?_
  have := (hI q hq').2.1
  rw [h0, zero_sub, norm_neg, hq0] at this
  exact absurd hx (not_lt.2 this)
