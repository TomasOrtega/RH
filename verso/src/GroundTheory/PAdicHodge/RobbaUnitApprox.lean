import Mathlib
import GroundTheory.PAdicHodge.RobbaSeries
import GroundTheory.PAdicHodge.HighIndexSingleZeroOne
import GroundTheory.PAdicHodge.RobbaBounded
import GroundTheory.PAdicHodge.RobbaNewton
import GroundTheory.PAdicHodge.RobbaClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace Laurent

variable {a : ℤ → K} {ρ : ℝ}

/- English proof (translation)
Establish `hαβ : α ≤ β` using `hρ.1.trans hρ.2`. Establish `hρ0 : 0 < ρ` using `hα.trans_le hρ.1`. Establish `hcα` using `hconv α ⟨le_rfl, hαβ⟩`. Establish `hcβ` using `hconv β ⟨hαβ, le_rfl⟩`. Establish `hc` using `hconv ρ hρ`.

Establish `h1` using `lowIndex_mono hα hρ.1 hcα hc ha`. Establish `h2` using `highIndex_mono hρ0 hρ.2 hc hcβ ha`. Establish `h3` using `lowIndex_le_highIndex hρ0 hc ha`. Establish `e1 : lowIndex a ρ = lowIndex a α` using `by omega`. Establish `e2 : lowIndex a ρ = highIndex a ρ` using `by omega`.

Introduce `m hm`. Use `weight_lt_of_lowIndex_eq_highIndex hρ0 hc ha e2 m (by rw [e1]; exact hm)` as an intermediate fact. Rewrite `this` using `[e1]`. Then use the resulting hypothesis.
-/
theorem unique_dominant_of_lowIndex_eq_highIndex {α β : ℝ} (hα : 0 < α)
    (hconv : ∀ ρ ∈ Set.Icc α β, ConvergesAt a ρ) (ha : a ≠ 0)
    (h : lowIndex a α = highIndex a β) {ρ : ℝ} (hρ : ρ ∈ Set.Icc α β) :
    ∀ m, m ≠ lowIndex a α → ‖a m‖ * ρ ^ m < ‖a (lowIndex a α)‖ * ρ ^ (lowIndex a α) := by
  have hαβ : α ≤ β := hρ.1.trans hρ.2
  have hρ0 : 0 < ρ := hα.trans_le hρ.1
  have hcα := hconv α ⟨le_rfl, hαβ⟩
  have hcβ := hconv β ⟨hαβ, le_rfl⟩
  have hc := hconv ρ hρ
  have h1 := lowIndex_mono hα hρ.1 hcα hc ha
  have h2 := highIndex_mono hρ0 hρ.2 hc hcβ ha
  have h3 := lowIndex_le_highIndex hρ0 hc ha
  have e1 : lowIndex a ρ = lowIndex a α := by omega
  have e2 : lowIndex a ρ = highIndex a ρ := by omega
  intro m hm
  have := weight_lt_of_lowIndex_eq_highIndex hρ0 hc ha e2 m (by rw [e1]; exact hm)
  rwa [e1] at this

/- English proof (translation)
Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Establish `hρn : 0 < ρ ^ n` using `zpow_pos hρ n`. Rewrite using `[← le_div_iff₀ hρn]`. Use `IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_` and prove the remaining obligations. Use `(norm_geom_term_le hρ hx k n).trans ?_` and prove the remaining obligations.

Conclude with `div_le_div_of_nonneg_right (pow_le_one₀ (gaussNorm_nonneg hρ) hq.le) hρn.le`.
-/
theorem gaussNorm_geomInv_le (hρ : 0 < ρ) (hx : ConvergesAt a ρ) (hq : gaussNorm a ρ < 1) :
    gaussNorm (geomInv a) ρ ≤ 1 := by
  refine gaussNorm_le fun n => ?_
  have hρn : 0 < ρ ^ n := zpow_pos hρ n
  rw [← le_div_iff₀ hρn]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun k => ?_
  refine (norm_geom_term_le hρ hx k n).trans ?_
  exact div_le_div_of_nonneg_right (pow_le_one₀ (gaussNorm_nonneg hρ) hq.le) hρn.le

end Laurent

namespace AnnulusRing

variable {I : Set ℝ} [Fact (∃ ρ ∈ I, 0 < ρ)]

/- English proof (translation)
Take `⟨u, rfl⟩` from `hf`. Use `set g := ((u⁻¹ : (AnnulusRing K (Set.Icc α β))ˣ) : AnnulusRing K (Set.Icc α β))`. Establish `hfg : cmul (u : AnnulusRing K (Set.Icc α β)).coeff g.coeff = Pi.single 0 1` using `congrArg AnnulusRing.coeff u.mul_inv`. Take `⟨ρ₀, hρ₀, -⟩` from `(Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)`. Establish `hαβ : α ≤ β` using `hρ₀.1.trans hρ₀.2`.

Establish `hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0` using `fun h0 => by simpa using congrFun h0 0`. Establish `hf0 : (u : AnnulusRing K (Set.Icc α β)).coeff ≠ 0` using `fun h0 => hne (by rw [← hfg, h0, zero_cmul])`. Establish `hg0 : g.coeff ≠ 0` using `fun h0 => hne (by rw [← hfg, h0, cmul_zero])`. Establish `key : ∀ ρ ∈ Set.Icc α β, lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ = highIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ ∧ lowIndex g.coeff ρ = -lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ ∧ highIndex g.coeff ρ = -lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ`. Introduce `ρ hρ`.

Establish `hρ0 : 0 < ρ` using `hα.trans_le hρ.1`. Establish `cf` using `(u : AnnulusRing K (Set.Icc α β)).convergesAt hρ hρ0`. Establish `cg` using `g.convergesAt hρ hρ0`. Establish `e1` using `lowIndex_cmul hρ0 cf cg hf0 hg0`. Establish `e2` using `highIndex_cmul hρ0 cf cg hf0 hg0`.

Rewrite `e1` using `[hfg, lowIndex_single_zero_one hρ0]`. Rewrite `e2` using `[hfg, highIndex_single_zero_one hρ0]`. Establish `l1` using `lowIndex_le_highIndex hρ0 cf hf0`. Establish `l2` using `lowIndex_le_highIndex hρ0 cg hg0`. Use `⟨by omega, by omega, by omega⟩` and prove the remaining obligations.

Break down `hαβ.lt_or_eq with hlt | heq` into its components or cases. Establish `a1` using `highIndex_le_lowIndex hα hlt ((u : AnnulusRing K (Set.Icc α β)).convergesAt ⟨le_rfl, hαβ⟩ hα) ((u : AnnulusRing K (Set.Icc α β)).convergesAt ⟨hαβ, le_rfl⟩ (hα.trans hlt)) hf0`. Establish `a2` using `highIndex_le_lowIndex hα hlt (g.convergesAt ⟨le_rfl, hαβ⟩ hα) (g.convergesAt ⟨hαβ, le_rfl⟩ (hα.trans hlt)) hg0`. Take `⟨k1, k2, k3⟩` from `key α ⟨le_rfl, hαβ⟩`. Take `⟨k1', k2', k3'⟩` from `key β ⟨hαβ, le_rfl⟩`.

Use linear arithmetic over natural numbers and integers. Substitute `heq` using the available equality. Conclude with `(key α ⟨le_rfl, le_rfl⟩).1`.
-/
theorem lowIndex_eq_highIndex_of_isUnit {α β : ℝ} [Fact (∃ ρ ∈ Set.Icc α β, 0 < ρ)]
    (hα : 0 < α) {f : AnnulusRing K (Set.Icc α β)} (hf : IsUnit f) :
    lowIndex f.coeff α = highIndex f.coeff β := by
  obtain ⟨u, rfl⟩ := hf
  set g := ((u⁻¹ : (AnnulusRing K (Set.Icc α β))ˣ) : AnnulusRing K (Set.Icc α β))
  have hfg : cmul (u : AnnulusRing K (Set.Icc α β)).coeff g.coeff = Pi.single 0 1 :=
    congrArg AnnulusRing.coeff u.mul_inv
  obtain ⟨ρ₀, hρ₀, -⟩ := (Fact.out : ∃ ρ ∈ Set.Icc α β, 0 < ρ)
  have hαβ : α ≤ β := hρ₀.1.trans hρ₀.2
  have hne : (Pi.single 0 (1 : K) : ℤ → K) ≠ 0 := fun h0 => by simpa using congrFun h0 0
  have hf0 : (u : AnnulusRing K (Set.Icc α β)).coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, zero_cmul])
  have hg0 : g.coeff ≠ 0 := fun h0 => hne (by rw [← hfg, h0, cmul_zero])
  have key : ∀ ρ ∈ Set.Icc α β, lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ =
      highIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ ∧
      lowIndex g.coeff ρ = -lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ ∧
      highIndex g.coeff ρ = -lowIndex (u : AnnulusRing K (Set.Icc α β)).coeff ρ := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hα.trans_le hρ.1
    have cf := (u : AnnulusRing K (Set.Icc α β)).convergesAt hρ hρ0
    have cg := g.convergesAt hρ hρ0
    have e1 := lowIndex_cmul hρ0 cf cg hf0 hg0
    have e2 := highIndex_cmul hρ0 cf cg hf0 hg0
    rw [hfg, lowIndex_single_zero_one hρ0] at e1
    rw [hfg, highIndex_single_zero_one hρ0] at e2
    have l1 := lowIndex_le_highIndex hρ0 cf hf0
    have l2 := lowIndex_le_highIndex hρ0 cg hg0
    refine ⟨by omega, by omega, by omega⟩
  rcases hαβ.lt_or_eq with hlt | heq
  · have a1 := highIndex_le_lowIndex hα hlt
      ((u : AnnulusRing K (Set.Icc α β)).convergesAt ⟨le_rfl, hαβ⟩ hα)
      ((u : AnnulusRing K (Set.Icc α β)).convergesAt ⟨hαβ, le_rfl⟩ (hα.trans hlt)) hf0
    have a2 := highIndex_le_lowIndex hα hlt (g.convergesAt ⟨le_rfl, hαβ⟩ hα)
      (g.convergesAt ⟨hαβ, le_rfl⟩ (hα.trans hlt)) hg0
    obtain ⟨k1, k2, k3⟩ := key α ⟨le_rfl, hαβ⟩
    obtain ⟨k1', k2', k3'⟩ := key β ⟨hαβ, le_rfl⟩
    omega
  · subst heq
    exact (key α ⟨le_rfl, le_rfl⟩).1

end AnnulusRing

namespace Laurent

def tNeg (t : ℤ → K) : ℤ → K := trunc t (Set.Iio 0)

def tSmall (t : ℤ → K) : ℤ → K := trunc t {n | 0 ≤ n ∧ ‖t n‖ ≤ 1}

def tBig (t : ℤ → K) : ℤ → K := trunc t {n | 0 ≤ n ∧ 1 < ‖t n‖}

/- English proof (translation)
Use function extensionality and compare the values at `n`. Simplify using `only [tNeg, tSmall, tBig, trunc, Pi.add_apply, Set.indicator_apply, Set.mem_Iio, Set.mem_setOf_eq]`. Distinguish the cases in `h0 : n < 0`. Simplify using `[h0, not_le.2 h0]`. Establish `h0' : 0 ≤ n` using `not_lt.1 h0`.

Distinguish the cases in `h1 : ‖t n‖ ≤ 1`. Simplify using `[h0, h0', h1, not_lt.2 h1]`. Simplify using `[h0, h0', h1, not_le.1 h1]`.
-/
theorem tNeg_add_tSmall_add_tBig (t : ℤ → K) : tNeg t + tSmall t + tBig t = t := by
  funext n
  simp only [tNeg, tSmall, tBig, trunc, Pi.add_apply, Set.indicator_apply, Set.mem_Iio,
    Set.mem_setOf_eq]
  by_cases h0 : n < 0
  · simp [h0, not_le.2 h0]
  · have h0' : 0 ≤ n := not_lt.1 h0
    by_cases h1 : ‖t n‖ ≤ 1
    · simp [h0, h0', h1, not_lt.2 h1]
    · simp [h0, h0', h1, not_le.1 h1]

/- English proof (translation)
Simplify using `[tNeg, trunc, Set.indicator_apply, show ¬ n < 0 by omega]`.
-/
theorem tNeg_eq_zero (t : ℤ → K) {n : ℤ} (hn : -1 < n) : tNeg t n = 0 := by
  simp [tNeg, trunc, Set.indicator_apply, show ¬ n < 0 by omega]

/- English proof (translation)
Simplify using `[tSmall, trunc, Set.indicator_apply, show ¬ 0 ≤ n by omega]`.
-/
theorem tSmall_eq_zero (t : ℤ → K) {n : ℤ} (hn : n < 0) : tSmall t n = 0 := by
  simp [tSmall, trunc, Set.indicator_apply, show ¬ 0 ≤ n by omega]

/- English proof (translation)
Simplify using `only [tSmall, trunc, Set.indicator_apply, Set.mem_setOf_eq]`. Use `split_ifs with h`. Conclude with `h.2`. Simplify using the standard rewrite rules.
-/
theorem norm_tSmall_le (t : ℤ → K) (n : ℤ) : ‖tSmall t n‖ ≤ 1 := by
  simp only [tSmall, trunc, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with h
  · exact h.2
  · simp

/- English proof (translation)
Use `tendsto_order.2 ⟨fun e he => Eventually.of_forall fun n => lt_of_lt_of_le he (by positivity), fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨N₀, hN₀⟩` from `exists_pow_lt_of_lt_one hε hρ1`. Use `Filter.eventually_cofinite.2 ((Set.finite_Ico (0 : ℤ) N₀).subset fun n hn => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq, not_lt] at hn`. Assume the negation of the conclusion as `hcon`.

Simplify using `only [Set.mem_Ico, not_and_or, not_le, not_lt] at hcon`. Break down `hcon with h | h` into its components or cases. Rewrite `hn` using `[hsupp n h, norm_zero, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : ρ ^ n ≤ ρ ^ (N₀ : ℤ)` using `zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le h`.

Rewrite `h1` using `[zpow_natCast]`. Establish `h2 : ‖b n‖ * ρ ^ n ≤ ρ ^ n`. Use `zpow_pos hρ0 n` as an intermediate fact. Use polynomial arithmetic with `[hb n, norm_nonneg (b n)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem convergesAt_of_norm_le_one {b : ℤ → K} {ρ : ℝ} (hsupp : ∀ n, n < 0 → b n = 0)
    (hb : ∀ n, ‖b n‖ ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : ConvergesAt b ρ := by
  refine tendsto_order.2 ⟨fun e he => Eventually.of_forall fun n => lt_of_lt_of_le he
    (by positivity), fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := exists_pow_lt_of_lt_one hε hρ1
  refine Filter.eventually_cofinite.2 ((Set.finite_Ico (0 : ℤ) N₀).subset fun n hn => ?_)
  simp only [Set.mem_setOf_eq, not_lt] at hn
  by_contra hcon
  simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at hcon
  rcases hcon with h | h
  · rw [hsupp n h, norm_zero, zero_mul] at hn; linarith
  · have h1 : ρ ^ n ≤ ρ ^ (N₀ : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le h
    rw [zpow_natCast] at h1
    have h2 : ‖b n‖ * ρ ^ n ≤ ρ ^ n := by
      have := zpow_pos hρ0 n
      nlinarith [hb n, norm_nonneg (b n)]
    linarith

section Step

variable {r s s' μ q' : ℝ} {n₀ : ℕ} {t : ℤ → K}

/- English proof (translation)
Establish `hsupp : ∀ n, (-1 : ℤ) < n → tNeg t n = 0` using `fun n hn => tNeg_eq_zero t hn`. Establish `hcr : ConvergesAt (tNeg t) r` using `hc.trunc hr _`. Use `⟨hcr.of_support_le hsupp hr hρ, ?_⟩` and prove the remaining obligations. Use `(gaussNorm_le_of_support_le hsupp hcr hr hρ).trans ?_` and prove the remaining obligations. Establish `h1 : 1 ≤ ρ / r` using `by rw [le_div_iff₀ hr]; linarith`.

Establish `h2 : (ρ / r) ^ (-1 : ℤ) ≤ 1`. Rewrite using `[zpow_neg_one]`. Conclude with `inv_le_one_of_one_le₀ h1`. Establish `h3 : gaussNorm (tNeg t) r ≤ μ` using `(gaussNorm_trunc_le hr hc _).trans hμ`. Establish `h4 : 0 ≤ gaussNorm (tNeg t) r` using `gaussNorm_nonneg hr`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem tNeg_spec (hr : 0 < r) (hc : ConvergesAt t r) (hμ : gaussNorm t r ≤ μ) {ρ : ℝ}
    (hρ : r ≤ ρ) : ConvergesAt (tNeg t) ρ ∧ gaussNorm (tNeg t) ρ ≤ μ := by
  have hsupp : ∀ n, (-1 : ℤ) < n → tNeg t n = 0 := fun n hn => tNeg_eq_zero t hn
  have hcr : ConvergesAt (tNeg t) r := hc.trunc hr _
  refine ⟨hcr.of_support_le hsupp hr hρ, ?_⟩
  refine (gaussNorm_le_of_support_le hsupp hcr hr hρ).trans ?_
  have h1 : 1 ≤ ρ / r := by rw [le_div_iff₀ hr]; linarith
  have h2 : (ρ / r) ^ (-1 : ℤ) ≤ 1 := by
    rw [zpow_neg_one]; exact inv_le_one_of_one_le₀ h1
  have h3 : gaussNorm (tNeg t) r ≤ μ := (gaussNorm_trunc_le hr hc _).trans hμ
  have h4 : 0 ≤ gaussNorm (tNeg t) r := gaussNorm_nonneg hr
  calc gaussNorm (tNeg t) r * (ρ / r) ^ (-1 : ℤ) ≤ gaussNorm (tNeg t) r * 1 :=
        mul_le_mul_of_nonneg_left h2 h4
    _ ≤ μ := by rw [mul_one]; exact h3

/- English proof (translation)
Establish `hρ0 : 0 < ρ` using `hr.trans_le hρ`. Use `⟨convergesAt_of_norm_le_one (fun n hn => tSmall_eq_zero t hn) (norm_tSmall_le t) hρ0 hρ1, gaussNorm_le fun n => ?_⟩` and prove the remaining obligations. Break down `lt_trichotomy n 0 with hn | rfl | hn` into its components or cases. Rewrite using `[tSmall_eq_zero t hn, norm_zero, zero_mul]`. Check the signs of the components of the expression.

Use `hc.le_gaussNorm 0` as an intermediate fact. Simplify using `only [zpow_zero, mul_one] at this ⊢`. Conclude with `le_max_of_le_left ((norm_trunc_le _ 0).trans (this.trans hμ))`. Use `le_max_of_le_right ?_` and prove the remaining obligations. Establish `h1 : ρ ^ n ≤ ρ ^ (1 : ℤ)` using `zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (by omega)`.

Rewrite `h1` using `[zpow_one]`. Use `zpow_pos hρ0 n` as an intermediate fact. Use polynomial arithmetic with `[norm_tSmall_le t n, norm_nonneg (tSmall t n)]`.
-/
theorem tSmall_spec (hr : 0 < r) (hc : ConvergesAt t r) (hμ : gaussNorm t r ≤ μ) {ρ : ℝ}
    (hρ : r ≤ ρ) (hρ1 : ρ < 1) : ConvergesAt (tSmall t) ρ ∧ gaussNorm (tSmall t) ρ ≤ max μ ρ := by
  have hρ0 : 0 < ρ := hr.trans_le hρ
  refine ⟨convergesAt_of_norm_le_one (fun n hn => tSmall_eq_zero t hn) (norm_tSmall_le t) hρ0 hρ1,
    gaussNorm_le fun n => ?_⟩
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · rw [tSmall_eq_zero t hn, norm_zero, zero_mul]; positivity
  · have := hc.le_gaussNorm 0
    simp only [zpow_zero, mul_one] at this ⊢
    exact le_max_of_le_left ((norm_trunc_le _ 0).trans (this.trans hμ))
  · refine le_max_of_le_right ?_
    have h1 : ρ ^ n ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ0 hρ1.le (by omega)
    rw [zpow_one] at h1
    have := zpow_pos hρ0 n
    nlinarith [norm_tSmall_le t n, norm_nonneg (tSmall t n)]

/- English proof (translation)
Establish `hs' : 0 < s'` using `hρ0.trans_le hρ`. Use `gaussNorm_le fun n => ?_` and prove the remaining obligations. Simplify using `only [tBig, trunc, Set.indicator_apply, Set.mem_setOf_eq]`. Use `split_ifs with hn`. Take `⟨hn0, hn1⟩` from `hn`.

Establish `hts : ‖t n‖ * s ^ n < 1` using `lt_of_le_of_lt ((hc.le_gaussNorm n).trans hμ) hμ1`. Establish `h1` using `hbig _ hn1`. Establish `hsn : s ^ n < q'`. Use `zpow_pos hs0 n` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hnn : (n₀ : ℤ) < n`. Assume the negation of the conclusion as `hle`. Establish `: s ^ (n₀ : ℤ) ≤ s ^ n` using `zpow_le_zpow_right_of_le_one₀ hs0 hs1.le (not_lt.1 hle)`. Rewrite `this` using `[zpow_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hratio0 : 0 < s' / s` using `div_pos hs' hs0`. Establish `hratio1 : s' / s ≤ 1` using `by rw [div_le_one hs0]; exact hs's`. Establish `e1 : ρ ^ n ≤ s' ^ n` using `zpow_le_zpow_left₀ hn0 hρ0.le hρ`. Establish `e2 : s' ^ n = s ^ n * (s' / s) ^ n`. Rewrite using `[div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ hs0.ne')]`.

Establish `e3 : (s' / s) ^ n ≤ (s' / s) ^ (n₀ : ℤ)` using `zpow_le_zpow_right_of_le_one₀ hratio0 hratio1 hnn.le`. Rewrite `e3` using `[zpow_natCast]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [norm_zero, zero_mul]`. Check the signs of the components of the expression.
-/
theorem gaussNorm_tBig_le (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖)
    (hs0 : 0 < s) (hs1 : s < 1) (hs's : s' ≤ s) (hn₀ : q' ≤ s ^ n₀) (hc : ConvergesAt t s)
    (hμ : gaussNorm t s ≤ μ) (hμ1 : μ < 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ s') :
    gaussNorm (tBig t) ρ ≤ (s' / s) ^ n₀ := by
  have hs' : 0 < s' := hρ0.trans_le hρ
  refine gaussNorm_le fun n => ?_
  simp only [tBig, trunc, Set.indicator_apply, Set.mem_setOf_eq]
  split_ifs with hn
  · obtain ⟨hn0, hn1⟩ := hn
    have hts : ‖t n‖ * s ^ n < 1 := lt_of_le_of_lt ((hc.le_gaussNorm n).trans hμ) hμ1
    have h1 := hbig _ hn1
    have hsn : s ^ n < q' := by
      have := zpow_pos hs0 n
      nlinarith
    have hnn : (n₀ : ℤ) < n := by
      by_contra hle
      have : s ^ (n₀ : ℤ) ≤ s ^ n :=
        zpow_le_zpow_right_of_le_one₀ hs0 hs1.le (not_lt.1 hle)
      rw [zpow_natCast] at this
      linarith
    have hratio0 : 0 < s' / s := div_pos hs' hs0
    have hratio1 : s' / s ≤ 1 := by rw [div_le_one hs0]; exact hs's
    have e1 : ρ ^ n ≤ s' ^ n := zpow_le_zpow_left₀ hn0 hρ0.le hρ
    have e2 : s' ^ n = s ^ n * (s' / s) ^ n := by
      rw [div_zpow, mul_div_cancel₀ _ (zpow_ne_zero _ hs0.ne')]
    have e3 : (s' / s) ^ n ≤ (s' / s) ^ (n₀ : ℤ) :=
      zpow_le_zpow_right_of_le_one₀ hratio0 hratio1 hnn.le
    rw [zpow_natCast] at e3
    calc ‖t n‖ * ρ ^ n ≤ ‖t n‖ * s' ^ n := mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
      _ = (‖t n‖ * s ^ n) * (s' / s) ^ n := by rw [e2]; ring
      _ ≤ 1 * (s' / s) ^ n :=
          mul_le_mul_of_nonneg_right hts.le (zpow_pos hratio0 n).le
      _ ≤ (s' / s) ^ n₀ := by rw [one_mul]; exact e3
  · simp only [norm_zero, zero_mul]; positivity

end Step

end Laurent

namespace Laurent

section Iteration

variable {r s s' μ q' : ℝ} {n₀ : ℕ} {t : ℤ → K}

/- English proof (translation)
Establish `hrs : r ≤ s` using `hrs'.trans hs's`. Establish `hs0 : 0 < s` using `hr.trans_le hrs`. Establish `hcr` using `hconv r ⟨le_rfl, hrs⟩`. Establish `hμr` using `hμ r ⟨le_rfl, hrs⟩`. Establish `hμ0 : 0 ≤ μ` using `(gaussNorm_nonneg hr).trans hμr`.

Use `set tn := tNeg t`. Use `set ts := tSmall t`. Use `set tb := tBig t`. Establish `Ntn : ∀ ρ, r ≤ ρ → ConvergesAt tn ρ ∧ gaussNorm tn ρ ≤ μ` using `fun ρ h => tNeg_spec hr hcr hμr h`. Establish `Nts : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt ts ρ ∧ gaussNorm ts ρ ≤ max μ ρ` using `fun ρ h h1 => tSmall_spec hr hcr hμr h h1`.

Establish `d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ` using `fun ρ => convergesAt_single 0 1 ρ`. Establish `Cgn : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (geomInv tn) ρ ∧ gaussNorm (geomInv tn) ρ ≤ 1`. Introduce `ρ h h1`. Establish `hρ` using `hr.trans_le h`. Establish `hq : gaussNorm tn ρ < 1` using `(Ntn ρ h).2.trans_lt hμ1`.

Conclude with `⟨(Ntn ρ h).1.geomInv hρ hq, gaussNorm_geomInv_le hρ (Ntn ρ h).1 hq⟩`. Establish `Cgs : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (geomInv ts) ρ ∧ gaussNorm (geomInv ts) ρ ≤ 1`. Introduce `ρ h h1`. Establish `hρ` using `hr.trans_le h`. Establish `hq : gaussNorm ts ρ < 1` using `(Nts ρ h h1).2.trans_lt (max_lt hμ1 h1)`.

Conclude with `⟨(Nts ρ h h1).1.geomInv hρ hq, gaussNorm_geomInv_le hρ (Nts ρ h h1).1 hq⟩`. Use `set G := cmul (Pi.single 0 1 + tn) (Pi.single 0 1 + ts) with hG`. Use `set Gi := cmul (geomInv tn) (geomInv ts) with hGi`. Establish `hGc : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt G ρ ∧ ConvergesAt Gi ρ`. Introduce `ρ h h1`.

Establish `hρ` using `hr.trans_le h`. Conclude with `⟨((d0 ρ).add hρ (Ntn ρ h).1).cmul hρ ((d0 ρ).add hρ (Nts ρ h h1).1), (Cgn ρ h h1).1.cmul hρ (Cgs ρ h h1).1⟩`. Establish `hr1 : r < 1` using `hrs.trans_lt hs1`. Establish `hGG : cmul G Gi = Pi.single 0 1`. Rewrite using `[hG, hGi, cmul_rearrange hr ((d0 r).add hr (Ntn r le_rfl).1) ((d0 r).add hr (Nts r le_rfl hr1).1) (Cgn r le_rfl hr1).1 (Cgs r le_rfl hr1).1, cmul_one_add_geomInv hr (Ntn r le_rfl).1 ((Ntn r le_rfl).2.trans_lt hμ1), cmul_one_add_geomInv hr (Nts r le_rfl hr1).1 ((Nts r le_rfl hr1). …`.

Use `set X := tb - cmul tn ts with hX`. Use `set t' := cmul X Gi with ht'`. Establish `CX : ∀ ρ ∈ Set.Icc r s, ConvergesAt X ρ`. Introduce `ρ hρ`. Establish `hρ0` using `hr.trans_le hρ.1`.

Conclude with `((hconv ρ hρ).trunc hρ0 _).sub hρ0 ((Ntn ρ hρ.1).1.cmul hρ0 (Nts ρ hρ.1 (hρ.2.trans_lt hs1)).1)`. Establish `Ct' : ∀ ρ ∈ Set.Icc r s, ConvergesAt t' ρ` using `fun ρ hρ => (CX ρ hρ).cmul (hr.trans_le hρ.1) (hGc ρ hρ.1 (hρ.2.trans_lt hs1)).2`. Establish `bound : ∀ ρ ∈ Set.Icc r s, gaussNorm t' ρ ≤ max (gaussNorm tb ρ) (gaussNorm tn ρ * gaussNorm ts ρ)`. Introduce `ρ hρ`. Establish `hρ0` using `hr.trans_le hρ.1`.

Establish `hρ1` using `hρ.2.trans_lt hs1`. Establish `cb : ConvergesAt tb ρ` using `(hconv ρ hρ).trunc hρ0 _`. Establish `cn` using `(Ntn ρ hρ.1).1`. Establish `cs` using `(Nts ρ hρ.1 hρ1).1`. Establish `hGi1 : gaussNorm Gi ρ ≤ 1` using `(gaussNorm_cmul_le hρ0 (Cgn ρ hρ.1 hρ1).1 (Cgs ρ hρ.1 hρ1).1).trans (mul_le_one₀ (Cgn ρ hρ.1 hρ1).2 (gaussNorm_nonneg hρ0) (Cgs ρ hρ.1 hρ1).2)`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨G, Gi, t', hGc, hGG, fun ρ hρ => ⟨Ct' ρ hρ, ?_⟩, fun ρ hρ => ?_, ?_⟩` and prove the remaining obligations. Establish `hρ0` using `hr.trans_le hρ.1`. Establish `ht` using `hμ ρ hρ`. Establish `e1 : gaussNorm tb ρ ≤ μ` using `(gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht`.

Establish `e2 : gaussNorm tn ρ ≤ μ` using `(gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht`. Establish `e3 : gaussNorm ts ρ ≤ μ` using `(gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht`. Establish `e4 : gaussNorm tn ρ * gaussNorm ts ρ ≤ μ` using `(mul_le_mul e2 e3 (gaussNorm_nonneg hρ0) hμ0).trans (by nlinarith)`. Conclude with `(bound ρ hρ).trans (max_le e1 e4)`. Establish `hρs : ρ ∈ Set.Icc r s` using `⟨hρ.1, hρ.2.trans hs's⟩`.

Establish `hρ0` using `hr.trans_le hρ.1`. Establish `e1 : gaussNorm tb ρ ≤ (s' / s) ^ n₀` using `gaussNorm_tBig_le hq' hbig hs0 hs1 hs's hn₀ (hconv s ⟨hrs, le_rfl⟩) (hμ s ⟨hrs, le_rfl⟩) hμ1 hρ0 hρ.2`. Establish `e2 : gaussNorm tn ρ ≤ gaussNorm t ρ` using `gaussNorm_trunc_le hρ0 (hconv ρ hρs) _`. Establish `e3 : gaussNorm ts ρ ≤ gaussNorm t ρ` using `gaussNorm_trunc_le hρ0 (hconv ρ hρs) _`. Establish `e4 : gaussNorm tn ρ * gaussNorm ts ρ ≤ gaussNorm t ρ ^ 2`.

Rewrite using `[sq]`. Conclude with `mul_le_mul e2 e3 (gaussNorm_nonneg hρ0) (gaussNorm_nonneg hρ0)`. Conclude with `(bound ρ hρs).trans (max_le_max e1 e4)`. Use `haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩`. Set `A` to `AnnulusRing K (Set.Icc r s)`.

Establish `hρ1 : ∀ ρ ∈ Set.Icc r s, ρ < 1` using `fun ρ hρ => hρ.2.trans_lt hs1`. Set `eT : A` to `⟨t, fun ρ hρ _ => hconv ρ hρ⟩`. Set `eTn : A` to `⟨tn, fun ρ hρ _ => (Ntn ρ hρ.1).1⟩`. Set `eTs : A` to `⟨ts, fun ρ hρ _ => (Nts ρ hρ.1 (hρ1 ρ hρ)).1⟩`. Set `eTb : A` to `⟨tb, fun ρ hρ h0 => (hconv ρ hρ).trunc h0 _⟩`.

Set `eGn : A` to `⟨geomInv tn, fun ρ hρ _ => (Cgn ρ hρ.1 (hρ1 ρ hρ)).1⟩`. Set `eGs : A` to `⟨geomInv ts, fun ρ hρ _ => (Cgs ρ hρ.1 (hρ1 ρ hρ)).1⟩`. Establish `hsum : eTn + eTs + eTb = eT` using `AnnulusRing.ext (tNeg_add_tSmall_add_tBig t)`. Establish `hGG' : (1 + eTn) * (1 + eTs) * (eGn * eGs) = 1` using `AnnulusRing.ext hGG`. Establish `key : 1 + eT = (1 + eTn) * (1 + eTs) * (1 + (eTb - eTn * eTs) * (eGn * eGs))`.

Take the linear combination `-hsum - (eTb - eTn * eTs) * hGG'`. Conclude with `congrArg AnnulusRing.coeff key`.
-/
theorem unitApprox_step (hr : 0 < r) (hrs' : r ≤ s') (hs's : s' ≤ s) (hs1 : s < 1)
    (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖) (hn₀ : q' ≤ s ^ n₀)
    (hconv : ∀ ρ ∈ Set.Icc r s, ConvergesAt t ρ) (hμ : ∀ ρ ∈ Set.Icc r s, gaussNorm t ρ ≤ μ)
    (hμ1 : μ < 1) :
    ∃ G Gi t' : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt G ρ ∧ ConvergesAt Gi ρ) ∧
      cmul G Gi = Pi.single 0 1 ∧
      (∀ ρ ∈ Set.Icc r s, ConvergesAt t' ρ ∧ gaussNorm t' ρ ≤ μ) ∧
      (∀ ρ ∈ Set.Icc r s', gaussNorm t' ρ ≤ max ((s' / s) ^ n₀) (gaussNorm t ρ ^ 2)) ∧
      Pi.single 0 1 + t = cmul G (Pi.single 0 1 + t') := by
  have hrs : r ≤ s := hrs'.trans hs's
  have hs0 : 0 < s := hr.trans_le hrs
  have hcr := hconv r ⟨le_rfl, hrs⟩
  have hμr := hμ r ⟨le_rfl, hrs⟩
  have hμ0 : 0 ≤ μ := (gaussNorm_nonneg hr).trans hμr
  set tn := tNeg t
  set ts := tSmall t
  set tb := tBig t
  have Ntn : ∀ ρ, r ≤ ρ → ConvergesAt tn ρ ∧ gaussNorm tn ρ ≤ μ := fun ρ h => tNeg_spec hr hcr hμr h
  have Nts : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt ts ρ ∧ gaussNorm ts ρ ≤ max μ ρ :=
    fun ρ h h1 => tSmall_spec hr hcr hμr h h1
  have d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ := fun ρ => convergesAt_single 0 1 ρ

  have Cgn : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (geomInv tn) ρ ∧ gaussNorm (geomInv tn) ρ ≤ 1 := by
    intro ρ h h1
    have hρ := hr.trans_le h
    have hq : gaussNorm tn ρ < 1 := (Ntn ρ h).2.trans_lt hμ1
    exact ⟨(Ntn ρ h).1.geomInv hρ hq, gaussNorm_geomInv_le hρ (Ntn ρ h).1 hq⟩
  have Cgs : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt (geomInv ts) ρ ∧ gaussNorm (geomInv ts) ρ ≤ 1 := by
    intro ρ h h1
    have hρ := hr.trans_le h
    have hq : gaussNorm ts ρ < 1 := (Nts ρ h h1).2.trans_lt (max_lt hμ1 h1)
    exact ⟨(Nts ρ h h1).1.geomInv hρ hq, gaussNorm_geomInv_le hρ (Nts ρ h h1).1 hq⟩
  set G := cmul (Pi.single 0 1 + tn) (Pi.single 0 1 + ts) with hG
  set Gi := cmul (geomInv tn) (geomInv ts) with hGi
  have hGc : ∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt G ρ ∧ ConvergesAt Gi ρ := by
    intro ρ h h1
    have hρ := hr.trans_le h
    exact ⟨((d0 ρ).add hρ (Ntn ρ h).1).cmul hρ ((d0 ρ).add hρ (Nts ρ h h1).1),
      (Cgn ρ h h1).1.cmul hρ (Cgs ρ h h1).1⟩
  have hr1 : r < 1 := hrs.trans_lt hs1
  have hGG : cmul G Gi = Pi.single 0 1 := by
    rw [hG, hGi, cmul_rearrange hr ((d0 r).add hr (Ntn r le_rfl).1)
      ((d0 r).add hr (Nts r le_rfl hr1).1) (Cgn r le_rfl hr1).1 (Cgs r le_rfl hr1).1,
      cmul_one_add_geomInv hr (Ntn r le_rfl).1 ((Ntn r le_rfl).2.trans_lt hμ1),
      cmul_one_add_geomInv hr (Nts r le_rfl hr1).1 ((Nts r le_rfl hr1).2.trans_lt
        (max_lt hμ1 hr1)), cmul_single_zero_one]
  set X := tb - cmul tn ts with hX
  set t' := cmul X Gi with ht'

  have CX : ∀ ρ ∈ Set.Icc r s, ConvergesAt X ρ := by
    intro ρ hρ
    have hρ0 := hr.trans_le hρ.1
    exact ((hconv ρ hρ).trunc hρ0 _).sub hρ0 ((Ntn ρ hρ.1).1.cmul hρ0 (Nts ρ hρ.1
      (hρ.2.trans_lt hs1)).1)
  have Ct' : ∀ ρ ∈ Set.Icc r s, ConvergesAt t' ρ := fun ρ hρ =>
    (CX ρ hρ).cmul (hr.trans_le hρ.1) (hGc ρ hρ.1 (hρ.2.trans_lt hs1)).2

  have bound : ∀ ρ ∈ Set.Icc r s, gaussNorm t' ρ ≤
      max (gaussNorm tb ρ) (gaussNorm tn ρ * gaussNorm ts ρ) := by
    intro ρ hρ
    have hρ0 := hr.trans_le hρ.1
    have hρ1 := hρ.2.trans_lt hs1
    have cb : ConvergesAt tb ρ := (hconv ρ hρ).trunc hρ0 _
    have cn := (Ntn ρ hρ.1).1
    have cs := (Nts ρ hρ.1 hρ1).1
    have hGi1 : gaussNorm Gi ρ ≤ 1 :=
      (gaussNorm_cmul_le hρ0 (Cgn ρ hρ.1 hρ1).1 (Cgs ρ hρ.1 hρ1).1).trans
        (mul_le_one₀ (Cgn ρ hρ.1 hρ1).2 (gaussNorm_nonneg hρ0) (Cgs ρ hρ.1 hρ1).2)
    calc gaussNorm t' ρ ≤ gaussNorm X ρ * gaussNorm Gi ρ :=
          gaussNorm_cmul_le hρ0 (CX ρ hρ) (hGc ρ hρ.1 hρ1).2
      _ ≤ gaussNorm X ρ * 1 :=
          mul_le_mul_of_nonneg_left hGi1 (gaussNorm_nonneg hρ0)
      _ = gaussNorm X ρ := mul_one _
      _ ≤ max (gaussNorm tb ρ) (gaussNorm (cmul tn ts) ρ) :=
          gaussNorm_sub_le hρ0 cb (cn.cmul hρ0 cs)
      _ ≤ _ := max_le_max le_rfl (gaussNorm_cmul_le hρ0 cn cs)
  refine ⟨G, Gi, t', hGc, hGG, fun ρ hρ => ⟨Ct' ρ hρ, ?_⟩, fun ρ hρ => ?_, ?_⟩
  · have hρ0 := hr.trans_le hρ.1
    have ht := hμ ρ hρ
    have e1 : gaussNorm tb ρ ≤ μ := (gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht
    have e2 : gaussNorm tn ρ ≤ μ := (gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht
    have e3 : gaussNorm ts ρ ≤ μ := (gaussNorm_trunc_le hρ0 (hconv ρ hρ) _).trans ht
    have e4 : gaussNorm tn ρ * gaussNorm ts ρ ≤ μ :=
      (mul_le_mul e2 e3 (gaussNorm_nonneg hρ0) hμ0).trans
        (by nlinarith)
    exact (bound ρ hρ).trans (max_le e1 e4)
  · have hρs : ρ ∈ Set.Icc r s := ⟨hρ.1, hρ.2.trans hs's⟩
    have hρ0 := hr.trans_le hρ.1
    have e1 : gaussNorm tb ρ ≤ (s' / s) ^ n₀ :=
      gaussNorm_tBig_le hq' hbig hs0 hs1 hs's hn₀ (hconv s ⟨hrs, le_rfl⟩) (hμ s ⟨hrs, le_rfl⟩)
        hμ1 hρ0 hρ.2
    have e2 : gaussNorm tn ρ ≤ gaussNorm t ρ := gaussNorm_trunc_le hρ0 (hconv ρ hρs) _
    have e3 : gaussNorm ts ρ ≤ gaussNorm t ρ := gaussNorm_trunc_le hρ0 (hconv ρ hρs) _
    have e4 : gaussNorm tn ρ * gaussNorm ts ρ ≤ gaussNorm t ρ ^ 2 := by
      rw [sq]; exact mul_le_mul e2 e3 (gaussNorm_nonneg hρ0) (gaussNorm_nonneg hρ0)
    exact (bound ρ hρs).trans (max_le_max e1 e4)
  ·
    haveI : Fact (∃ ρ ∈ Set.Icc r s, 0 < ρ) := ⟨⟨r, ⟨le_rfl, hrs⟩, hr⟩⟩
    let A := AnnulusRing K (Set.Icc r s)
    have hρ1 : ∀ ρ ∈ Set.Icc r s, ρ < 1 := fun ρ hρ => hρ.2.trans_lt hs1
    let eT : A := ⟨t, fun ρ hρ _ => hconv ρ hρ⟩
    let eTn : A := ⟨tn, fun ρ hρ _ => (Ntn ρ hρ.1).1⟩
    let eTs : A := ⟨ts, fun ρ hρ _ => (Nts ρ hρ.1 (hρ1 ρ hρ)).1⟩
    let eTb : A := ⟨tb, fun ρ hρ h0 => (hconv ρ hρ).trunc h0 _⟩
    let eGn : A := ⟨geomInv tn, fun ρ hρ _ => (Cgn ρ hρ.1 (hρ1 ρ hρ)).1⟩
    let eGs : A := ⟨geomInv ts, fun ρ hρ _ => (Cgs ρ hρ.1 (hρ1 ρ hρ)).1⟩
    have hsum : eTn + eTs + eTb = eT := AnnulusRing.ext (tNeg_add_tSmall_add_tBig t)
    have hGG' : (1 + eTn) * (1 + eTs) * (eGn * eGs) = 1 := AnnulusRing.ext hGG
    have key : 1 + eT = (1 + eTn) * (1 + eTs) * (1 + (eTb - eTn * eTs) * (eGn * eGs)) := by
      linear_combination -hsum - (eTb - eTn * eTs) * hGG'
    exact congrArg AnnulusRing.coeff key

/- English proof (translation)
Establish `hrs : r ≤ s` using `hrs'.trans hs's`. Establish `hr1 : r < 1` using `hrs.trans_lt hs1`. Establish `hμ0 : 0 ≤ μ` using `(gaussNorm_nonneg hr).trans (hμ r ⟨le_rfl, hrs⟩)`. Establish `hs0 : 0 < s` using `hr.trans_le hrs`. Establish `hβ0 : 0 ≤ (s' / s) ^ n₀` using `pow_nonneg (div_nonneg (hr.le.trans hrs') hs0.le) _`.

Establish `hβ1 : (s' / s) ^ n₀ ≤ 1` using `pow_le_one₀ (div_nonneg (hr.le.trans hrs') hs0.le) (by rw [div_le_one hs0]; exact hs's)`. Establish `d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ` using `fun ρ => convergesAt_single 0 1 ρ`. Proceed by induction on `j with`. Consider the case `zero`. Use `⟨Pi.single 0 1, Pi.single 0 1, t, fun ρ _ _ => ⟨d0 ρ, d0 ρ⟩, cmul_single_zero_one _, fun ρ hρ => ⟨hconv ρ hρ, hμ ρ hρ⟩, fun ρ hρ => ?_, (single_zero_one_cmul _).symm⟩` and prove the remaining obligations.

Simplify using `only [pow_zero, pow_one]`. Conclude with `le_max_of_le_right (hμ ρ ⟨hρ.1, hρ.2.trans hs's⟩)`. Consider the case `succ j ih`. Take `⟨W, V, tj, hWV, hWV1, htj, htj', hid⟩` from `ih`. Take `⟨G, Gi, t'', hGc, hGG, ht'', ht''', hid'⟩` from `unitApprox_step hr hrs' hs's hs1 hq' hbig hn₀ (fun ρ hρ => (htj ρ hρ).1) (fun ρ hρ => (htj ρ hρ).2) hμ1`.

Use `⟨cmul W G, cmul V Gi, t'', fun ρ h h1 => ⟨(hWV ρ h h1).1.cmul (hr.trans_le h) (hGc ρ h h1).1, (hWV ρ h h1).2.cmul (hr.trans_le h) (hGc ρ h h1).2⟩, ?_, ht'', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[cmul_rearrange hr (hWV r le_rfl hr1).1 (hGc r le_rfl hr1).1 (hWV r le_rfl hr1).2 (hGc r le_rfl hr1).2, hWV1, hGG, cmul_single_zero_one]`. Introduce `ρ hρ`. Establish `hρ0` using `hr.trans_le hρ.1`. Establish `hρs : ρ ∈ Set.Icc r s` using `⟨hρ.1, hρ.2.trans hs's⟩`.

Use `set β := (s' / s) ^ n₀`. Establish `hx0` using `gaussNorm_nonneg (a := tj) hρ0`. Establish `hm : gaussNorm tj ρ ≤ max β (μ ^ 2 ^ j)` using `htj' ρ hρ`. Establish `hsq : gaussNorm tj ρ ^ 2 ≤ max β (μ ^ 2 ^ (j + 1))`. Break down `le_total β (μ ^ 2 ^ j) with h | h` into its components or cases.

Rewrite `hm` using `[max_eq_right h]`. Use `le_max_of_le_right ?_` and prove the remaining obligations. Rewrite using `[show μ ^ 2 ^ (j + 1) = (μ ^ 2 ^ j) ^ 2 by rw [pow_succ, pow_mul]]`. Conclude with `pow_le_pow_left₀ hx0 hm 2`. Rewrite `hm` using `[max_eq_left h]`.

Use `le_max_of_le_left ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Conclude with `(ht''' ρ hρ).trans (max_le (le_max_left _ _) hsq)`. Establish `c1` using `(hWV r le_rfl hr1).1`. Establish `c2` using `(hGc r le_rfl hr1).1`.

Establish `c3 : ConvergesAt (Pi.single 0 1 + t'') r` using `(d0 r).add hr (ht'' r ⟨le_rfl, hrs⟩).1`. Rewrite using `[hid, hid', cmul_assoc hr c1 c2 c3]`.
-/
theorem unitApprox_iter (hr : 0 < r) (hrs' : r ≤ s') (hs's : s' ≤ s) (hs1 : s < 1)
    (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖) (hn₀ : q' ≤ s ^ n₀)
    (hconv : ∀ ρ ∈ Set.Icc r s, ConvergesAt t ρ) (hμ : ∀ ρ ∈ Set.Icc r s, gaussNorm t ρ ≤ μ)
    (hμ1 : μ < 1) (j : ℕ) :
    ∃ W V t' : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt W ρ ∧ ConvergesAt V ρ) ∧
      cmul W V = Pi.single 0 1 ∧
      (∀ ρ ∈ Set.Icc r s, ConvergesAt t' ρ ∧ gaussNorm t' ρ ≤ μ) ∧
      (∀ ρ ∈ Set.Icc r s', gaussNorm t' ρ ≤ max ((s' / s) ^ n₀) (μ ^ (2 ^ j))) ∧
      Pi.single 0 1 + t = cmul W (Pi.single 0 1 + t') := by
  have hrs : r ≤ s := hrs'.trans hs's
  have hr1 : r < 1 := hrs.trans_lt hs1
  have hμ0 : 0 ≤ μ := (gaussNorm_nonneg hr).trans (hμ r ⟨le_rfl, hrs⟩)
  have hs0 : 0 < s := hr.trans_le hrs
  have hβ0 : 0 ≤ (s' / s) ^ n₀ := pow_nonneg (div_nonneg (hr.le.trans hrs') hs0.le) _
  have hβ1 : (s' / s) ^ n₀ ≤ 1 := pow_le_one₀ (div_nonneg (hr.le.trans hrs') hs0.le)
    (by rw [div_le_one hs0]; exact hs's)
  have d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ := fun ρ => convergesAt_single 0 1 ρ
  induction j with
  | zero =>
    refine ⟨Pi.single 0 1, Pi.single 0 1, t, fun ρ _ _ => ⟨d0 ρ, d0 ρ⟩,
      cmul_single_zero_one _, fun ρ hρ => ⟨hconv ρ hρ, hμ ρ hρ⟩, fun ρ hρ => ?_,
      (single_zero_one_cmul _).symm⟩
    simp only [pow_zero, pow_one]
    exact le_max_of_le_right (hμ ρ ⟨hρ.1, hρ.2.trans hs's⟩)
  | succ j ih =>
    obtain ⟨W, V, tj, hWV, hWV1, htj, htj', hid⟩ := ih
    obtain ⟨G, Gi, t'', hGc, hGG, ht'', ht''', hid'⟩ := unitApprox_step hr hrs' hs's hs1 hq' hbig
      hn₀ (fun ρ hρ => (htj ρ hρ).1) (fun ρ hρ => (htj ρ hρ).2) hμ1
    refine ⟨cmul W G, cmul V Gi, t'', fun ρ h h1 => ⟨(hWV ρ h h1).1.cmul (hr.trans_le h)
      (hGc ρ h h1).1, (hWV ρ h h1).2.cmul (hr.trans_le h) (hGc ρ h h1).2⟩, ?_, ht'', ?_, ?_⟩
    · rw [cmul_rearrange hr (hWV r le_rfl hr1).1 (hGc r le_rfl hr1).1 (hWV r le_rfl hr1).2
        (hGc r le_rfl hr1).2, hWV1, hGG, cmul_single_zero_one]
    · intro ρ hρ
      have hρ0 := hr.trans_le hρ.1
      have hρs : ρ ∈ Set.Icc r s := ⟨hρ.1, hρ.2.trans hs's⟩
      set β := (s' / s) ^ n₀
      have hx0 := gaussNorm_nonneg (a := tj) hρ0
      have hm : gaussNorm tj ρ ≤ max β (μ ^ 2 ^ j) := htj' ρ hρ
      have hsq : gaussNorm tj ρ ^ 2 ≤ max β (μ ^ 2 ^ (j + 1)) := by
        rcases le_total β (μ ^ 2 ^ j) with h | h
        · rw [max_eq_right h] at hm
          refine le_max_of_le_right ?_
          rw [show μ ^ 2 ^ (j + 1) = (μ ^ 2 ^ j) ^ 2 by rw [pow_succ, pow_mul]]
          exact pow_le_pow_left₀ hx0 hm 2
        · rw [max_eq_left h] at hm
          refine le_max_of_le_left ?_
          calc gaussNorm tj ρ ^ 2 ≤ β ^ 2 := pow_le_pow_left₀ hx0 hm 2
            _ ≤ β := by rw [sq]; exact mul_le_of_le_one_left hβ0 hβ1
      exact (ht''' ρ hρ).trans (max_le (le_max_left _ _) hsq)
    · have c1 := (hWV r le_rfl hr1).1
      have c2 := (hGc r le_rfl hr1).1
      have c3 : ConvergesAt (Pi.single 0 1 + t'') r := (d0 r).add hr (ht'' r ⟨le_rfl, hrs⟩).1
      rw [hid, hid', cmul_assoc hr c1 c2 c3]

/- English proof (translation)
Establish `hrs : r ≤ s` using `hrs'.trans hs's`. Establish `hr1 : r < 1` using `hrs.trans_lt hs1`. Establish `hs0 : 0 < s` using `hr.trans_le hrs`. Use `set N := lowIndex y r`. Establish `hdomρ` using `fun ρ (hρ : ρ ∈ Set.Icc r s) => unique_dominant_of_lowIndex_eq_highIndex hr hconv hy hdom hρ`.

Establish `hyN : y N ≠ 0` using `ne_zero_of_mem_domSet hr (hconv r ⟨le_rfl, hrs⟩) hy (lowIndex_mem hr (hconv r ⟨le_rfl, hrs⟩) hy)`. Use `set t := domTail y N`. Establish `ht : ∀ ρ ∈ Set.Icc r s, ConvergesAt t ρ ∧ gaussNorm t ρ < 1` using `fun ρ hρ => domTail_spec (hr.trans_le hρ.1) (hconv ρ hρ) hy (hdomρ ρ hρ)`. Use `set μ := max (gaussNorm t r) (gaussNorm t s)`. Establish `hμ1 : μ < 1` using `max_lt (ht r ⟨le_rfl, hrs⟩).2 (ht s ⟨hrs, le_rfl⟩).2`.

Establish `hμ : ∀ ρ ∈ Set.Icc r s, gaussNorm t ρ ≤ μ` using `fun ρ hρ => gaussNorm_le_max hr hρ.1 hρ.2 (ht r ⟨le_rfl, hrs⟩).1 (ht s ⟨hrs, le_rfl⟩).1`. Establish `hμ0 : 0 ≤ μ` using `(gaussNorm_nonneg hr).trans (le_max_left _ _)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hδ hμ1`. Establish `hj : μ ^ 2 ^ n ≤ δ` using `(pow_le_pow_of_le_one hμ0 hμ1.le (Nat.lt_two_pow_self).le).trans hn.le`. Take `⟨W, V, tj, hWV, hWV1, htj, htj', hid⟩` from `unitApprox_iter hr hrs' hs's hs1 hq' hbig hn₀ (fun ρ hρ => (ht ρ hρ).1) hμ hμ1 n`.

Establish `d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ` using `fun ρ => convergesAt_single 0 1 ρ`. Establish `hsN : ∀ ρ, ConvergesAt (Pi.single N (y N)) ρ` using `fun ρ => convergesAt_single N (y N) ρ`. Establish `hsN' : ∀ ρ, ConvergesAt (Pi.single (-N) (y N)⁻¹) ρ` using `fun ρ => convergesAt_single (-N) (y N)⁻¹ ρ`. Establish `hmono : cmul (Pi.single N (y N)) (Pi.single (-N) (y N)⁻¹) = Pi.single 0 1`. Rewrite using `[cmul_single_left]`.

Use function extensionality and compare the values at `m`. Simplify using `only [Pi.single_apply, sub_eq_iff_eq_add]`. Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using `[hyN]`.

Simplify using `[hm, show m ≠ -N + N by omega]`. Use `⟨cmul (Pi.single N (y N)) W, cmul (Pi.single (-N) (y N)⁻¹) V, fun ρ h h1 => ⟨(hsN ρ).cmul (hr.trans_le h) (hWV ρ h h1).1, (hsN' ρ).cmul (hr.trans_le h) (hWV ρ h h1).2⟩, ?_, fun ρ hρ => ?_⟩` and prove the remaining obligations. Rewrite using `[cmul_rearrange hr (hsN r) (hWV r le_rfl hr1).1 (hsN' r) (hWV r le_rfl hr1).2, hmono, hWV1, cmul_single_zero_one]`. Establish `cW` using `(hWV r le_rfl hr1).1`. Establish `cV` using `(hWV r le_rfl hr1).2`.

Establish `cj : ConvergesAt (Pi.single 0 1 + tj) r` using `(d0 r).add hr (htj r ⟨le_rfl, hrs⟩).1`. Establish `ct : ConvergesAt (Pi.single 0 1 + t) r` using `(d0 r).add hr (ht r ⟨le_rfl, hrs⟩).1`. Establish `e : cmul y (cmul (Pi.single (-N) (y N)⁻¹) V) = Pi.single 0 1 + tj`. Establish `ey` using `eq_single_cmul_domTail hyN`. Rewrite using `[show cmul y (cmul (Pi.single (-N) (y N)⁻¹) V) = cmul (cmul (Pi.single N (y N)) (Pi.single 0 1 + t)) (cmul (Pi.single (-N) (y N)⁻¹) V) from congrArg (fun x => cmul x (cmul (Pi.single (-N) (y N)⁻¹) V)) ey, cmul_rearrange hr (hsN r) ct (hsN' r) cV, hmono, single_zero_one_cmul, hid, …`.

Rewrite using `[e, add_sub_cancel_left]`. Conclude with `htj' ρ hρ |>.trans (max_le_max le_rfl hj)`.
-/
theorem exists_unit_approx (hr : 0 < r) (hrs' : r ≤ s') (hs's : s' ≤ s) (hs1 : s < 1)
    (hq' : 0 < q') (hbig : ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖) (hn₀ : q' ≤ s ^ n₀) {y : ℤ → K}
    (hconv : ∀ ρ ∈ Set.Icc r s, ConvergesAt y ρ) (hy : y ≠ 0)
    (hdom : lowIndex y r = highIndex y s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W V : ℤ → K, (∀ ρ, r ≤ ρ → ρ < 1 → ConvergesAt W ρ ∧ ConvergesAt V ρ) ∧
      cmul W V = Pi.single 0 1 ∧
      ∀ ρ ∈ Set.Icc r s', gaussNorm (cmul y V - Pi.single 0 1) ρ ≤ max ((s' / s) ^ n₀) δ := by
  have hrs : r ≤ s := hrs'.trans hs's
  have hr1 : r < 1 := hrs.trans_lt hs1
  have hs0 : 0 < s := hr.trans_le hrs
  set N := lowIndex y r
  have hdomρ := fun ρ (hρ : ρ ∈ Set.Icc r s) =>
    unique_dominant_of_lowIndex_eq_highIndex hr hconv hy hdom hρ
  have hyN : y N ≠ 0 := ne_zero_of_mem_domSet hr (hconv r ⟨le_rfl, hrs⟩) hy
    (lowIndex_mem hr (hconv r ⟨le_rfl, hrs⟩) hy)
  set t := domTail y N
  have ht : ∀ ρ ∈ Set.Icc r s, ConvergesAt t ρ ∧ gaussNorm t ρ < 1 := fun ρ hρ =>
    domTail_spec (hr.trans_le hρ.1) (hconv ρ hρ) hy (hdomρ ρ hρ)
  set μ := max (gaussNorm t r) (gaussNorm t s)
  have hμ1 : μ < 1 := max_lt (ht r ⟨le_rfl, hrs⟩).2 (ht s ⟨hrs, le_rfl⟩).2
  have hμ : ∀ ρ ∈ Set.Icc r s, gaussNorm t ρ ≤ μ := fun ρ hρ =>
    gaussNorm_le_max hr hρ.1 hρ.2 (ht r ⟨le_rfl, hrs⟩).1 (ht s ⟨hrs, le_rfl⟩).1
  have hμ0 : 0 ≤ μ := (gaussNorm_nonneg hr).trans (le_max_left _ _)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ hμ1
  have hj : μ ^ 2 ^ n ≤ δ :=
    (pow_le_pow_of_le_one hμ0 hμ1.le (Nat.lt_two_pow_self).le).trans hn.le
  obtain ⟨W, V, tj, hWV, hWV1, htj, htj', hid⟩ := unitApprox_iter hr hrs' hs's hs1 hq' hbig hn₀
    (fun ρ hρ => (ht ρ hρ).1) hμ hμ1 n
  have d0 : ∀ ρ, ConvergesAt (Pi.single 0 (1 : K)) ρ := fun ρ => convergesAt_single 0 1 ρ
  have hsN : ∀ ρ, ConvergesAt (Pi.single N (y N)) ρ := fun ρ => convergesAt_single N (y N) ρ
  have hsN' : ∀ ρ, ConvergesAt (Pi.single (-N) (y N)⁻¹) ρ :=
    fun ρ => convergesAt_single (-N) (y N)⁻¹ ρ
  have hmono : cmul (Pi.single N (y N)) (Pi.single (-N) (y N)⁻¹) = Pi.single 0 1 := by
    rw [cmul_single_left]
    funext m
    simp only [Pi.single_apply, sub_eq_iff_eq_add]
    by_cases hm : m = 0
    · subst hm; simp [hyN]
    · simp [hm, show m ≠ -N + N by omega]
  refine ⟨cmul (Pi.single N (y N)) W, cmul (Pi.single (-N) (y N)⁻¹) V, fun ρ h h1 =>
    ⟨(hsN ρ).cmul (hr.trans_le h) (hWV ρ h h1).1, (hsN' ρ).cmul (hr.trans_le h) (hWV ρ h h1).2⟩,
    ?_, fun ρ hρ => ?_⟩
  · rw [cmul_rearrange hr (hsN r) (hWV r le_rfl hr1).1 (hsN' r) (hWV r le_rfl hr1).2, hmono,
      hWV1, cmul_single_zero_one]
  · have cW := (hWV r le_rfl hr1).1
    have cV := (hWV r le_rfl hr1).2
    have cj : ConvergesAt (Pi.single 0 1 + tj) r := (d0 r).add hr (htj r ⟨le_rfl, hrs⟩).1
    have ct : ConvergesAt (Pi.single 0 1 + t) r := (d0 r).add hr (ht r ⟨le_rfl, hrs⟩).1
    have e : cmul y (cmul (Pi.single (-N) (y N)⁻¹) V) = Pi.single 0 1 + tj := by
      have ey := eq_single_cmul_domTail hyN
      rw [show cmul y (cmul (Pi.single (-N) (y N)⁻¹) V) = cmul (cmul (Pi.single N (y N))
          (Pi.single 0 1 + t)) (cmul (Pi.single (-N) (y N)⁻¹) V) from
          congrArg (fun x => cmul x (cmul (Pi.single (-N) (y N)⁻¹) V)) ey,
        cmul_rearrange hr (hsN r) ct (hsN' r) cV, hmono, single_zero_one_cmul, hid,
        cmul_assoc hr cW cj cV, cmul_comm (Pi.single 0 1 + tj) V,
        ← cmul_assoc hr cW cV cj, hWV1, single_zero_one_cmul]
    rw [e, add_sub_cancel_left]
    exact htj' ρ hρ |>.trans (max_le_max le_rfl hj)

end Iteration

end Laurent

/- English proof (translation)
Take `⟨q, hq0, hq1, hq⟩` from `exists_norm_le_mul_of_lt (K := K)`. Use `⟨max q (1 / 2), by positivity, max_lt hq1 (by norm_num), fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `hq x 1 (by simpa using hx)`. Rewrite `h1` using `[norm_one]`. Conclude with `h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))`.
-/
theorem exists_q_of_isDiscreteValuationRing [IsDiscreteValuationRing (normInteger K)] :
    ∃ q' : ℝ, 0 < q' ∧ q' < 1 ∧ ∀ x : K, 1 < ‖x‖ → 1 ≤ q' * ‖x‖ := by
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_le_mul_of_lt (K := K)
  refine ⟨max q (1 / 2), by positivity, max_lt hq1 (by norm_num), fun x hx => ?_⟩
  have h1 := hq x 1 (by simpa using hx)
  rw [norm_one] at h1
  exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))

end GroundTheory.PAdicHodge
