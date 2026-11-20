import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassPartialZetaContinuationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLNonvanishingAtOneStatement

open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open Filter Topology Asymptotics Set

namespace GlobalTheory.Mem.RayPrimes

/- English proof (translation)
Establish `hc : Continuous (fun s : ℝ => L s / L 1 - 1)` using `by fun_prop (disch := exact h1)`. Establish `ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2`. Use `(hc.norm.tendsto 1)` as an intermediate fact. Simplify using `only [ofReal_one, div_self h1, sub_self, norm_zero] at this`. Conclude with `this.eventually (gt_mem_nhds (by norm_num))`.

Take `⟨δ, hδ, hb⟩` from `Metric.eventually_nhds_iff.1 ht`. Establish `hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2` using `fun s hs => hb (by`. Apply the tactic sequence `rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])`. Establish `hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane` using `fun s hs => mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])`. Use `set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk`.

Establish `hkc : ContinuousOn k (Ioo 1 (1 + δ))` using `(hg.mono Ioo_subset_Ioi_self).sub (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)`. Establish `hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1` using `fun s hs => by`. Establish `hne : L s ≠ 0` using `by rw [← he s hs.1]; exact exp_ne_zero _`. Simplify using `only [hk]`. Rewrite using `[exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]`.

Clear the denominators using the available nonvanishing facts. Establish `hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2)` using `fun s hs => Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs ⟨by linarith, by linarith⟩`. Use `IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs`. Establish `h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1))`.

Rewrite using `[← hconst s hs]`. Simplify using `[hk]`. Establish `h3` using `norm_log_one_add_half_le_self (hb' s hs).le`. Rewrite using `[h2, norm_one, mul_one]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations.

Combine the linear relations using `[hb' s hs]`.
-/
theorem log_bounded (g : ℝ → ℂ) (L : ℂ → ℂ) (hL : Continuous L) (h1 : L 1 ≠ 0)
    (hg : ContinuousOn g (Ioi 1)) (he : ∀ s : ℝ, 1 < s → cexp (g s) = L s) :
    g =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  have hc : Continuous (fun s : ℝ => L s / L 1 - 1) := by fun_prop (disch := exact h1)
  have ht : ∀ᶠ s : ℝ in 𝓝 1, ‖L s / L 1 - 1‖ < 1 / 2 := by
    have := (hc.norm.tendsto 1)
    simp only [ofReal_one, div_self h1, sub_self, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ht
  have hb' : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), ‖L s / L 1 - 1‖ < 1 / 2 := fun s hs => hb (by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hs.1, hs.2])
  have hslit : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), 1 + (L s / L 1 - 1) ∈ slitPlane := fun s hs =>
    mem_slitPlane_of_norm_lt_one (by linarith [hb' s hs])
  set k : ℝ → ℂ := fun s => g s - log (1 + (L s / L 1 - 1)) with hk
  have hkc : ContinuousOn k (Ioo 1 (1 + δ)) :=
    (hg.mono Ioo_subset_Ioi_self).sub
      (ContinuousOn.clog (continuous_const.add hc).continuousOn hslit)
  have hke : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), cexp (k s) = L 1 := fun s hs => by
    have hne : L s ≠ 0 := by rw [← he s hs.1]; exact exp_ne_zero _
    simp only [hk]
    rw [exp_sub, exp_log (slitPlane_ne_zero (hslit s hs)), he s hs.1, add_sub_cancel]
    field_simp
  have hconst : ∀ s ∈ Ioo (1 : ℝ) (1 + δ), k s = k (1 + δ / 2) := fun s hs =>
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_Ioo hkc
      (fun a ha b hb => Subtype.ext (by simp only; rw [hke a ha, hke b hb])) hs
      ⟨by linarith, by linarith⟩
  refine IsBigO.of_bound (‖k (1 + δ / 2)‖ + 1) ?_
  filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 1 + δ by linarith)] with s hs
  have h2 : g s = k (1 + δ / 2) + log (1 + (L s / L 1 - 1)) := by
    rw [← hconst s hs]; simp [hk]
  have h3 := norm_log_one_add_half_le_self (hb' s hs).le
  rw [h2, norm_one, mul_one]
  refine (norm_add_le _ _).trans ?_
  linarith [hb' s hs]

section series

variable {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (a : ι → ℂ) (ha : ∀ v, ‖a v‖ ≤ 1)
include hn ha

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ n v` using `by exact_mod_cast hn v`. Rewrite using `[norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]`. Simplify using `only [neg_re, ofReal_re]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `ha v`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := one_mul _`.
-/
theorem norm_term_le (v : ι) {s t : ℝ} (hst : t ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-t) := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  rw [norm_mul, norm_natCast_cpow_of_pos (by linarith [hn v])]
  simp only [neg_re, ofReal_re]
  calc ‖a v‖ * (n v : ℝ) ^ (-s) ≤ 1 * (n v : ℝ) ^ (-t) := by
        gcongr
        · exact ha v
        · linarith
    _ = _ := one_mul _

/- English proof (translation)
Use `norm_term_le n hn a ha v hs` as an intermediate fact. Rewrite `this` using `[Real.rpow_neg_one]`. Then use the resulting hypothesis.
-/
theorem norm_term_le_inv (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ)⁻¹ := by
  have := norm_term_le n hn a ha v hs
  rwa [Real.rpow_neg_one] at this

/- English proof (translation)
Establish `h2 : (2 : ℝ) ≤ n v` using `by exact_mod_cast hn v`. Use `(norm_term_le_inv n hn a ha v hs).trans ?_` and prove the remaining obligations. Rewrite using `[one_div]`. Use `gcongr`.
-/
theorem norm_term_le_half (v : ι) {s : ℝ} (hs : 1 ≤ s) :
    ‖a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ n v := by exact_mod_cast hn v
  refine (norm_term_le_inv n hn a ha v hs).trans ?_
  rw [one_div]; gcongr

/- English proof (translation)
Introduce `s hs1`. Take `⟨t, ht1, hts⟩` from `exists_between (show (1 : ℝ) < s from hs1)`. Establish `: ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t)`. Use `continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_` and prove the remaining obligations. Introduce `v`.

Use `ContinuousOn.neg (ContinuousOn.clog ?_ ?_)` and prove the remaining obligations. Establish `h0 : (n v : ℂ) ≠ 0`. Use `hn v` as an intermediate fact. Conclude with `(by omega : n v ≠ 0)` after adjusting the coercions. Use `(continuous_const.sub (continuous_const.mul ?_)).continuousOn` and prove the remaining obligations.

Conclude with `Continuous.const_cpow (by fun_prop) (Or.inl h0)`. Introduce `x hx`. Rewrite using `[sub_eq_add_neg]`. Use `mem_slitPlane_of_norm_lt_one ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`.

Combine the linear relations using `[norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]`. Introduce `v x hx`. Rewrite using `[norm_neg, sub_eq_add_neg]`. Establish `h` using `norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ)))) (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))`. Rewrite `h` using `[norm_neg]`.

Combine the linear relations using `[norm_term_le n hn a ha v (le_of_lt hx)]`. Conclude with `(this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt`.
-/
theorem continuousOn_logSum (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi 1) := by
  intro s hs1
  obtain ⟨t, ht1, hts⟩ := exists_between (show (1 : ℝ) < s from hs1)
  have : ContinuousOn (fun s : ℝ => ∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) (Ioi t) := by
    refine continuousOn_tsum (u := fun v => 3 / 2 * (n v : ℝ) ^ (-t)) ?_ ((hs t ht1).mul_left _) ?_
    · intro v
      refine ContinuousOn.neg (ContinuousOn.clog ?_ ?_)
      · have h0 : (n v : ℂ) ≠ 0 := by
          have := hn v
          exact_mod_cast (by omega : n v ≠ 0)
        refine (continuous_const.sub (continuous_const.mul ?_)).continuousOn
        exact Continuous.const_cpow (by fun_prop) (Or.inl h0)
      · intro x hx
        rw [sub_eq_add_neg]
        refine mem_slitPlane_of_norm_lt_one ?_
        rw [norm_neg]
        linarith [norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx))]
    · intro v x hx
      rw [norm_neg, sub_eq_add_neg]
      have h := norm_log_one_add_half_le_self (z := -(a v * (n v : ℂ) ^ (-(x : ℂ))))
        (by rw [norm_neg]; exact norm_term_le_half n hn a ha v (ht1.le.trans (le_of_lt hx)))
      rw [norm_neg] at h
      linarith [norm_term_le n hn a ha v (le_of_lt hx)]
  exact (this.continuousAt (Ioi_mem_nhds hts)).continuousWithinAt

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl`.
-/
theorem summable_term (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) {s : ℝ} (h : 1 < s) :
    Summable fun v => a v * (n v : ℂ) ^ (-(s : ℂ)) :=
  Summable.of_norm_bounded (hs s h) fun v => norm_term_le n hn a ha v le_rfl

/- English proof (translation)
Use `IsBigO.of_bound (∑' v, (n v : ℝ) ^ (-(2 : ℝ))) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs1`. Establish `hs1 : 1 < s` using `hs1`. Establish `hb : ∀ v, ‖-log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) - a v * (n v : ℂ) ^ (-(s : ℂ))‖ ≤ (n v : ℝ) ^ (-(2 : ℝ))`. Introduce `v`.

Use `set z := a v * (n v : ℂ) ^ (-(s : ℂ)) with hz`. Establish `h1 : ‖z‖ ≤ 1 / 2` using `norm_term_le_half n hn a ha v hs1.le`. Establish `h2 : ‖z‖ ≤ (n v : ℝ)⁻¹` using `norm_term_le_inv n hn a ha v hs1.le`. Establish `h3` using `norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)`. Establish `h4 : -log (1 - z) - z = -(log (1 + -z) - -z)` using `by rw [← sub_eq_add_neg 1 z]; ring`.

Rewrite using `[h4, norm_neg]`. Use `h3.trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← inv_pow]`. Establish `h5 : (1 - ‖z‖)⁻¹ ≤ 2`. Rewrite using `[inv_le_comm₀ (by linarith) (by norm_num)]; linarith`.

Establish `h6 : ‖z‖ ^ 2 ≤ ((n v : ℝ)⁻¹) ^ 2` using `by gcongr`. Establish `h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `summable_term n hn a ha hs hs1`. Establish `hd` using `Summable.of_norm_bounded (hs 2 (by norm_num)) hb`.

Establish `hl : Summable fun v => -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))`. Simplify using `using hd.add hsum`. Rewrite using `[← hl.tsum_sub hsum, norm_one, mul_one]`. Conclude with `tsum_of_norm_bounded (hs 2 (by norm_num)).hasSum hb`.
-/
theorem logSum_sub_bounded (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s)) :
    (fun s : ℝ => (∑' v, -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ)))) - ∑' v, a v * (n v : ℂ) ^ (-(s : ℂ)))
      =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (∑' v, (n v : ℝ) ^ (-(2 : ℝ))) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs1
  have hs1 : 1 < s := hs1
  have hb : ∀ v, ‖-log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) - a v * (n v : ℂ) ^ (-(s : ℂ))‖
      ≤ (n v : ℝ) ^ (-(2 : ℝ)) := by
    intro v
    set z := a v * (n v : ℂ) ^ (-(s : ℂ)) with hz
    have h1 : ‖z‖ ≤ 1 / 2 := norm_term_le_half n hn a ha v hs1.le
    have h2 : ‖z‖ ≤ (n v : ℝ)⁻¹ := norm_term_le_inv n hn a ha v hs1.le
    have h3 := norm_log_one_add_sub_self_le (z := -z) (by rw [norm_neg]; linarith)
    have h4 : -log (1 - z) - z = -(log (1 + -z) - -z) := by rw [← sub_eq_add_neg 1 z]; ring
    rw [h4, norm_neg]
    refine h3.trans ?_
    rw [norm_neg, Real.rpow_neg (Nat.cast_nonneg _), Real.rpow_two, ← inv_pow]
    have h5 : (1 - ‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h6 : ‖z‖ ^ 2 ≤ ((n v : ℝ)⁻¹) ^ 2 := by gcongr
    have h7 : ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ ≤ ‖z‖ ^ 2 * 2 := by gcongr
    linarith
  have hsum := summable_term n hn a ha hs hs1
  have hd := Summable.of_norm_bounded (hs 2 (by norm_num)) hb
  have hl : Summable fun v => -log (1 - a v * (n v : ℂ) ^ (-(s : ℂ))) := by
    simpa using hd.add hsum
  rw [← hl.tsum_sub hsum, norm_one, mul_one]
  exact tsum_of_norm_bounded (hs 2 (by norm_num)).hasSum hb

end series

section orth

variable {G : Type} [CommGroup G] [Fintype G]

/- English proof (translation)
Use `Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) ?_ Fintype.card_ne_zero` and prove the remaining obligations. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]`.
-/
theorem norm_char (χ : G →* ℂˣ) (x : G) : ‖(χ x : ℂ)‖ = 1 := by
  refine Complex.norm_eq_one_of_pow_eq_one (n := Fintype.card G) ?_ Fintype.card_ne_zero
  rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]

/- English proof (translation)
Take `⟨φ, hφ⟩` from `CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx`. Set `f : (G →* ℂˣ) →* ℂ` to `{ toFun := fun χ => (χ x : ℂ), map_one' := by simp, map_mul' := by simp }`. Use `sum_hom_units_eq_zero f ?_` and prove the remaining obligations. Introduce `h`. Apply `hφ` to reduce the goal to its premises.

Use `DFunLike.congr_fun h φ` as an intermediate fact. Simplify `this` using `[f]`.
-/
theorem sum_char_eq_zero [Fintype (G →* ℂˣ)] {x : G} (hx : x ≠ 1) :
    ∑ χ : G →* ℂˣ, (χ x : ℂ) = 0 := by
  obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hx
  let f : (G →* ℂˣ) →* ℂ :=
    { toFun := fun χ => (χ x : ℂ), map_one' := by simp, map_mul' := by simp }
  refine sum_hom_units_eq_zero f ?_
  intro h
  apply hφ
  have := DFunLike.congr_fun h φ
  simpa [f] using this

/- English proof (translation)
Introduce `hc`. Establish `: Fintype (G →* ℂˣ)` using `Fintype.ofFinite _`. Set `g : (G →* ℂˣ) → ℝ → ℂ` to `fun χ s => ∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))`. Set `P : (G →* ℂˣ) → ℝ → ℂ` to `fun χ s => ∑' v, (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))`. Establish `hgP : ∀ χ, (fun s => g χ s - P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ))` using `fun χ => logSum_sub_bounded n hn _ (fun v => (norm_char χ _).le) hs`.

Establish `hP : ∀ χ, χ ≠ 1 → P χ =O[𝓝[>] 1] (fun _ => (1 : ℝ))`. Introduce `χ h`. Take `⟨L, hL, hL1, hL2⟩` from `hχ χ h`. Use `log_bounded (g χ) L hL hL1 (continuousOn_logSum n hn _ (fun v => (norm_char χ _).le) hs) hL2` as an intermediate fact. Simplify using `using this.sub (hgP χ)`.

Establish `hS : (fun s => ∑ χ, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ))`. Establish `hc'` using `(summable_subtype_iff_indicator (f := fun v => (n v : ℝ)⁻¹) (s := {v | cl v = c})).1 hc`. Establish `hc''` using `hc'.mul_left (Fintype.card (G →* ℂˣ) : ℝ)`. Use `IsBigO.of_bound (∑' v, (Fintype.card (G →* ℂˣ) : ℝ) * ({v | cl v = c}).indicator (fun v => (n v : ℝ)⁻¹) v) ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with s hs1`.

Establish `hs1 : 1 < s` using `hs1`. Establish `hsum : ∀ χ : G →* ℂˣ, Summable fun v => (χ c⁻¹ : ℂ) * ((χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))` using `fun χ => (summable_term n hn _ (fun v => (norm_char χ _).le) hs hs1).mul_left _`. Simplify using `only [P, ← tsum_mul_left]`. Rewrite using `[← Summable.tsum_finsetSum (fun χ _ => hsum χ), norm_one, mul_one]`. Use `tsum_of_norm_bounded hc''.hasSum fun v => ?_` and prove the remaining obligations.

Distinguish the cases in `hv : cl v = c`. Rewrite using `[indicator_of_mem (by exact hv)]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul, ← Finset.card_univ]`. Use `Finset.sum_le_card_nsmul _ _ _ fun χ _ => ?_` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_char, one_mul]`. Conclude with `norm_term_le_inv n hn (fun v => (χ (cl v) : ℂ)) (fun v => (norm_char χ _).le) v hs1.le`. Rewrite using `[indicator_of_notMem (by exact hv)]`. Establish `: c⁻¹ * cl v ≠ 1` using `fun h => hv (inv_mul_eq_one.1 h).symm`. Establish `h0` using `sum_char_eq_zero this`.

Simplify using `only [map_mul, Units.val_mul] at h0`. Simplify using `only [← mul_assoc, ← Finset.sum_mul, h0]`. Simplify using the standard rewrite rules. Establish `hP1 : P 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ))`. Establish `h2 : (fun s => ∑ χ ∈ Finset.univ.erase 1, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ))` using `(IsBigO.sum fun χ hχ => (hP χ (Finset.ne_of_mem_erase hχ)).const_mul_left (χ c⁻¹ : ℂ)).congr_left fun s => Finset.sum_apply _ _ _`.

Use `(hS.sub h2).congr_left fun s => ?_` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G →* ℂˣ))]`. Simplify using the standard rewrite rules. Establish `hg1 : g 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ))`. Simplify using `using (hgP 1).add hP1`.

Take `⟨B, hB⟩` from `hg1.bound`. Establish `hlim : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1))`. Establish `: Continuous fun s : ℝ => Z s` using `by fun_prop`. Simplify using `using (this.tendsto 1).mono_left nhdsWithin_le_nhds`. Establish `hlim0 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 0)`.

Use `squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B) ?_ ?_` and prove the remaining obligations. Use `filter_upwards [hB, self_mem_nhdsWithin] with s h hs1`. Rewrite using `[h1 s hs1, norm_mul, norm_exp]`. Use `gcongr`. Rewrite `h` using `[norm_one, mul_one]`.

Conclude with `(re_le_norm _).trans h`. Establish `: Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B` using `by fun_prop`. Simplify using `using (this.tendsto 1).mono_left nhdsWithin_le_nhds`. Conclude with `hZ1 (tendsto_nhds_unique hlim hlim0)`.
-/
theorem not_summable_class {ι : Type} (n : ι → ℕ) (hn : ∀ v, 2 ≤ n v) (cl : ι → G)
    (hs : ∀ s : ℝ, 1 < s → Summable fun v => (n v : ℝ) ^ (-s))
    (hχ : ∀ χ : G →* ℂˣ, χ ≠ 1 → ∃ L : ℂ → ℂ, Continuous L ∧ L 1 ≠ 0 ∧ ∀ s : ℝ, 1 < s →
      cexp (∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))) = L s)
    (Z : ℂ → ℂ) (hZ : Continuous Z) (hZ1 : Z 1 ≠ 0)
    (h1 : ∀ s : ℝ, 1 < s → Z s = (s - 1) *
      cexp (∑' v, -log (1 - ((1 : G →* ℂˣ) (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))))
    (c : G) : ¬ Summable fun v : {v // cl v = c} => (n v : ℝ)⁻¹ := by
  classical
  intro hc
  have : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  let g : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, -log (1 - (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ)))
  let P : (G →* ℂˣ) → ℝ → ℂ := fun χ s => ∑' v, (χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))
  have hgP : ∀ χ, (fun s => g χ s - P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := fun χ =>
    logSum_sub_bounded n hn _ (fun v => (norm_char χ _).le) hs
  have hP : ∀ χ, χ ≠ 1 → P χ =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    intro χ h
    obtain ⟨L, hL, hL1, hL2⟩ := hχ χ h
    have := log_bounded (g χ) L hL hL1
      (continuousOn_logSum n hn _ (fun v => (norm_char χ _).le) hs) hL2
    simpa using this.sub (hgP χ)
  have hS : (fun s => ∑ χ, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have hc' := (summable_subtype_iff_indicator (f := fun v => (n v : ℝ)⁻¹)
      (s := {v | cl v = c})).1 hc
    have hc'' := hc'.mul_left (Fintype.card (G →* ℂˣ) : ℝ)
    refine IsBigO.of_bound (∑' v, (Fintype.card (G →* ℂˣ) : ℝ) *
      ({v | cl v = c}).indicator (fun v => (n v : ℝ)⁻¹) v) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs1
    have hs1 : 1 < s := hs1
    have hsum : ∀ χ : G →* ℂˣ, Summable fun v =>
        (χ c⁻¹ : ℂ) * ((χ (cl v) : ℂ) * (n v : ℂ) ^ (-(s : ℂ))) := fun χ =>
      (summable_term n hn _ (fun v => (norm_char χ _).le) hs hs1).mul_left _
    simp only [P, ← tsum_mul_left]
    rw [← Summable.tsum_finsetSum (fun χ _ => hsum χ), norm_one, mul_one]
    refine tsum_of_norm_bounded hc''.hasSum fun v => ?_
    by_cases hv : cl v = c
    · rw [indicator_of_mem (by exact hv)]
      refine (norm_sum_le _ _).trans ?_
      rw [← nsmul_eq_mul, ← Finset.card_univ]
      refine Finset.sum_le_card_nsmul _ _ _ fun χ _ => ?_
      rw [norm_mul, norm_char, one_mul]
      exact norm_term_le_inv n hn (fun v => (χ (cl v) : ℂ)) (fun v => (norm_char χ _).le) v hs1.le
    · rw [indicator_of_notMem (by exact hv)]
      have : c⁻¹ * cl v ≠ 1 := fun h => hv (inv_mul_eq_one.1 h).symm
      have h0 := sum_char_eq_zero this
      simp only [map_mul, Units.val_mul] at h0
      simp only [← mul_assoc, ← Finset.sum_mul, h0]
      simp
  have hP1 : P 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    have h2 : (fun s => ∑ χ ∈ Finset.univ.erase 1, (χ c⁻¹ : ℂ) * P χ s) =O[𝓝[>] 1]
        (fun _ => (1 : ℝ)) :=
      (IsBigO.sum fun χ hχ => (hP χ (Finset.ne_of_mem_erase hχ)).const_mul_left
        (χ c⁻¹ : ℂ)).congr_left fun s => Finset.sum_apply _ _ _
    refine (hS.sub h2).congr_left fun s => ?_
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : G →* ℂˣ))]
    simp
  have hg1 : g 1 =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by
    simpa using (hgP 1).add hP1
  obtain ⟨B, hB⟩ := hg1.bound
  have hlim : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have : Continuous fun s : ℝ => Z s := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim0 : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B) ?_ ?_
    · filter_upwards [hB, self_mem_nhdsWithin] with s h hs1
      rw [h1 s hs1, norm_mul, norm_exp]
      gcongr
      rw [norm_one, mul_one] at h
      exact (re_le_norm _).trans h
    · have : Continuous fun s : ℝ => ‖(s : ℂ) - 1‖ * Real.exp B := by fun_prop
      simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  exact hZ1 (tendsto_nhds_unique hlim hlim0)

end orth

section field

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`.

Conclude with `v.isPrime.ne_top`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_le_absNorm (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

/- English proof (translation)
Establish `hP` using `v.isPrime`. Establish `h2'` using `two_le_absNorm v`. Establish `hm` using `Ideal.absNorm_mem v.asIdeal`. Choose the witnesses or unpack the hypotheses as in `⟨p, hp, hpv⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by`. Rewrite `hm` using `[← Nat.prod_primeFactorsList (n := Ideal.absNorm v.asIdeal) (by omega), Nat.cast_list_prod]`.

Take `⟨x, hx, hxv⟩` from `(Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hP (((Ideal.absNorm v.asIdeal).primeFactorsList.map Nat.cast : List (𝓞 K)) : Multiset (𝓞 K))).1 (by simpa using hm)`. Simplify using `only [Multiset.mem_coe, List.mem_map] at hx`. Take `⟨p, hp, rfl⟩` from `hx`. Conclude with `⟨p, Nat.prime_of_mem_primeFactorsList hp, hxv⟩`. Establish `hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2`.

Rewrite using `[Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]`. Choose the witnesses or unpack the hypotheses as in `⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := by`. Rewrite using `[Ideal.dvd_span_singleton]`. Conclude with `hpv`. Establish `hmul : p ^ 2 = Ideal.absNorm v.asIdeal * Ideal.absNorm J` using `by rw [← hN, hJ, map_mul]`.

Take `⟨i, hi, hiv⟩` from `(Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩`. Establish `hi2 : i = 2` using `by interval_cases i`. Rewrite `hiv` using `[pow_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite `hiv` using `[pow_one]`.

Conclude with `absurd (hiv ▸ hp) hv`. Both sides reduce to the same expression. Substitute `hi2` using the available equality. Use `⟨p, ?_, hiv⟩` and prove the remaining obligations. Establish `hJ1 : Ideal.absNorm J = 1`.

Rewrite `hmul` using `[hiv]`. Conclude with `(Nat.mul_eq_left (pow_ne_zero _ hp.ne_zero)).1 hmul.symm`. Rewrite `hJ1` using `[Ideal.absNorm_eq_one_iff]`. Rewrite using `[hJ, hJ1, Ideal.mul_top]`.
-/
theorem eq_span_of_not_prime (h2 : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by
  have hP := v.isPrime
  have h2' := two_le_absNorm v
  have hm := Ideal.absNorm_mem v.asIdeal
  obtain ⟨p, hp, hpv⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ v.asIdeal := by
    rw [← Nat.prod_primeFactorsList (n := Ideal.absNorm v.asIdeal) (by omega), Nat.cast_list_prod] at hm
    obtain ⟨x, hx, hxv⟩ := (Ideal.IsPrime.multiset_prod_mem_iff_exists_mem hP
      (((Ideal.absNorm v.asIdeal).primeFactorsList.map Nat.cast : List (𝓞 K)) : Multiset (𝓞 K))).1
      (by simpa using hm)
    simp only [Multiset.mem_coe, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hxv⟩
  have hN : Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, h2]
  obtain ⟨J, hJ⟩ : v.asIdeal ∣ Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]; exact hpv
  have hmul : p ^ 2 = Ideal.absNorm v.asIdeal * Ideal.absNorm J := by rw [← hN, hJ, map_mul]
  obtain ⟨i, hi, hiv⟩ := (Nat.dvd_prime_pow hp).1 ⟨_, hmul⟩
  have hi2 : i = 2 := by
    interval_cases i
    · rw [pow_zero] at hiv; omega
    · rw [pow_one] at hiv; exact absurd (hiv ▸ hp) hv
    · rfl
  subst hi2
  refine ⟨p, ?_, hiv⟩
  have hJ1 : Ideal.absNorm J = 1 := by
    rw [hiv] at hmul
    exact (Nat.mul_eq_left (pow_ne_zero _ hp.ne_zero)).1 hmul.symm
  rw [Ideal.absNorm_eq_one_iff] at hJ1
  rw [hJ, hJ1, Ideal.mul_top]

/- English proof (translation)
Establish `hfin : {i | Ideal.absNorm (f i).asIdeal ≤ N}.Finite`. Establish `h1 : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite` using `Ideal.finite_setOfPred_absNorm_le N`. Use `Set.Finite.preimage (f := fun i => (f i).asIdeal) ?_ h1` and prove the remaining obligations. Introduce `i _ j _ hij`. Conclude with `hf (HeightOneSpectrum.ext hij)`.

Rewrite using `[← hfin.summable_compl_iff]`. Establish `hex : ∀ i : ↥({i | Ideal.absNorm (f i).asIdeal ≤ N}ᶜ : Set ι), ∃ p : ℕ, (f i).asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm (f i).asIdeal = p ^ 2` using `fun i => eq_span_of_not_prime h2 _ fun hp => i.2 (h i hp)`. Use `choose p hp1 hp2 using hex`. Establish `hinj : Function.Injective p` using `fun i j hij => Subtype.ext (hf (HeightOneSpectrum.ext (by rw [hp1, hp1, hij])))`. Use `(Real.summable_nat_pow_inv.2 one_lt_two).comp_injective hinj` as an intermediate fact.

Use `this.congr fun i => ?_` and prove the remaining obligations. Simplify using `[hp2]`.
-/
theorem summable_of_not_prime_or_le (h2 : Module.finrank ℚ K = 2) (N : ℕ) {ι : Type}
    (f : ι → HeightOneSpectrum (𝓞 K)) (hf : Function.Injective f)
    (h : ∀ i, (Ideal.absNorm (f i).asIdeal).Prime → Ideal.absNorm (f i).asIdeal ≤ N) :
    Summable fun i => ((Ideal.absNorm (f i).asIdeal : ℕ) : ℝ)⁻¹ := by
  have hfin : {i | Ideal.absNorm (f i).asIdeal ≤ N}.Finite := by
    have h1 : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ N}.Finite := Ideal.finite_setOfPred_absNorm_le N
    refine Set.Finite.preimage (f := fun i => (f i).asIdeal) ?_ h1
    intro i _ j _ hij
    exact hf (HeightOneSpectrum.ext hij)
  rw [← hfin.summable_compl_iff]
  have hex : ∀ i : ↥({i | Ideal.absNorm (f i).asIdeal ≤ N}ᶜ : Set ι), ∃ p : ℕ,
      (f i).asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm (f i).asIdeal = p ^ 2 :=
    fun i => eq_span_of_not_prime h2 _ fun hp => i.2 (h i hp)
  choose p hp1 hp2 using hex
  have hinj : Function.Injective p := fun i j hij =>
    Subtype.ext (hf (HeightOneSpectrum.ext (by rw [hp1, hp1, hij])))
  have := (Real.summable_nat_pow_inv.2 one_lt_two).comp_injective hinj
  refine this.congr fun i => ?_
  simp [hp2]

end field

/- English proof (translation)
Introduce `K _ _ _ h2 M hM D c N`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Take `⟨ρ, hρ, hZ⟩` from `GlobalTheory.T.ray_class_partial_zeta_continuation K h2 M hM D`. Use `choose Z hZd hZ1 _ hZs using hZ`.

Establish `hre : ∀ s : ℝ, 1 < s → 1 < (s : ℂ).re` using `fun s h => by simpa using h`. Use `not_summable_class (fun v : D.Pr => Ideal.absNorm v.1.asIdeal) (fun v => two_le_absNorm v.1) (fun v => D.cls v.1.asIdeal) ?_ ?_ (fun s => ∑ x, Z x s) (continuous_finsetSum _ fun x _ => (hZd x).continuous) ?_ ?_ c ?_` and prove the remaining obligations. Introduce `s hs`. Use `(GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.1.congr fun v => ?_` and prove the remaining obligations. Rewrite using `[norm_natCast_cpow_of_pos (by linarith [two_le_absNorm v.1])]`.

Simplify using the standard rewrite rules. Introduce `χ hχ`. Take `⟨L, hL, hL1, hL2⟩` from `GlobalTheory.T.ray_L_nonvanishing_at_one K h2 M hM D χ hχ`. Conclude with `⟨L, hL.continuous, hL1, fun s hs => by`. Rewrite using `[hL2 s (hre s hs), (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D χ s (hre s hs)).2.2]⟩`.

Simplify using `only [hZ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Conclude with `mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by exact_mod_cast hρ.ne')`. Introduce `s hs`. Rewrite using `[← (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.2]`. Establish `hco : D.coef 1 = ∑ x, D.cnt x`.

Use function extensionality and compare the values at `m`. Simplify using `[RayData.coef]`. Rewrite using `[hco, LSeries_sum fun x _ => (hZs x s (hre s hs)).1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun x _ => (hZs x s (hre s hs)).2`. Conclude with `summable_of_not_prime_or_le h2 N (fun v : {v : D.Pr // D.cls v.1.asIdeal = c} => v.1.1) (fun i j hij => Subtype.ext (Subtype.ext hij)) fun i hi => hcon i.1 i.2 hi`.
-/
theorem exists_prime_in_class : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (c : D.G) (N : ℕ), ∃ v : D.Pr, D.cls v.1.asIdeal = c ∧ (Ideal.absNorm v.1.asIdeal).Prime ∧ N < Ideal.absNorm v.1.asIdeal := by
  intro K _ _ _ h2 M hM D c N
  by_contra hcon
  push Not at hcon
  obtain ⟨ρ, hρ, hZ⟩ := GlobalTheory.T.ray_class_partial_zeta_continuation K h2 M hM D
  choose Z hZd hZ1 _ hZs using hZ
  have hre : ∀ s : ℝ, 1 < s → 1 < (s : ℂ).re := fun s h => by simpa using h
  refine not_summable_class (fun v : D.Pr => Ideal.absNorm v.1.asIdeal)
    (fun v => two_le_absNorm v.1) (fun v => D.cls v.1.asIdeal) ?_ ?_ (fun s => ∑ x, Z x s)
    (continuous_finsetSum _ fun x _ => (hZd x).continuous) ?_ ?_ c ?_
  · intro s hs
    refine (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.1.congr fun v => ?_
    rw [norm_natCast_cpow_of_pos (by linarith [two_le_absNorm v.1])]
    simp
  · intro χ hχ
    obtain ⟨L, hL, hL1, hL2⟩ := GlobalTheory.T.ray_L_nonvanishing_at_one K h2 M hM D χ hχ
    exact ⟨L, hL.continuous, hL1, fun s hs => by
      rw [hL2 s (hre s hs), (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D χ s (hre s hs)).2.2]⟩
  · simp only [hZ1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.2 Fintype.card_ne_zero) (by exact_mod_cast hρ.ne')
  · intro s hs
    rw [← (GlobalTheory.Mem.RayData.lseries_eq_exp_tsum K M hM D 1 s (hre s hs)).2.2]
    have hco : D.coef 1 = ∑ x, D.cnt x := by
      funext m
      simp [RayData.coef]
    rw [hco, LSeries_sum fun x _ => (hZs x s (hre s hs)).1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => (hZs x s (hre s hs)).2
  · exact summable_of_not_prime_or_le h2 N (fun v : {v : D.Pr // D.cls v.1.asIdeal = c} => v.1.1)
      (fun i j hij => Subtype.ext (Subtype.ext hij)) fun i hi => hcon i.1 i.2 hi

end GlobalTheory.Mem.RayPrimes
