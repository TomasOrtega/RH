import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormCoeffIntegralPowerSeriesLeProdZerosStatement

open GlobalTheory.ConvSer Filter Topology

namespace GlobalTheory.ConvSer

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h n`. Conclude with `h (Finsupp.single () n)`. Introduce `h ν`. Establish `hν : ν = Finsupp.single () (ν ())` using `by ext; simp`.

Rewrite using `[hν]`. Conclude with `h (ν ())`.
-/
theorem intg_iff_coeff_one_var {K : Type} [NormedField K] (f : PowerSeries K) :
    Intg f ↔ ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1 := by
  constructor
  · intro h n
    exact h (Finsupp.single () n)
  · intro h ν
    have hν : ν = Finsupp.single () (ν ()) := by
      ext; simp
    rw [hν]
    exact h (ν ())

/- English proof (translation)
Rewrite using `[norm_mul, norm_pow]`. Conclude with `mul_le_of_le_one_left (by positivity) ((intg_iff_coeff_one_var f).1 hf k)`.
-/
theorem norm_coeff_mul_pow_le_of_intg {K : Type} [NormedField K] {f : PowerSeries K}
    (hf : Intg f) (x : K) (k : ℕ) : ‖PowerSeries.coeff k f * x ^ k‖ ≤ ‖x‖ ^ k := by
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_left (by positivity) ((intg_iff_coeff_one_var f).1 hf k)

/- English proof (translation)
The claim follows from `Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx) (norm_coeff_mul_pow_le_of_intg hf x)`.
-/
theorem summable_coeff_mul_pow_of_intg {K : Type} [NormedField K] [CompleteSpace K]
    {f : PowerSeries K} (hf : Intg f) {x : K} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ => PowerSeries.coeff k f * x ^ k :=
  Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg x) hx)
    (norm_coeff_mul_pow_le_of_intg hf x)

/- English proof (translation)
Establish `hs : Summable fun n => a (n + 1) - a n` using `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])`. Establish `h1` using `hs.hasSum.tendsto_sum_nat`. Simplify using `only [Finset.sum_range_sub] at h1`. Use `⟨_, (h1.add_const (a 0)).congr fun n => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem exists_tendsto_of_sub_tendsto_zero_ultra {K : Type} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (a : ℕ → K) (h : Tendsto (fun n => a (n + 1) - a n) atTop (𝓝 0)) :
    ∃ l, Tendsto a atTop (𝓝 l) := by
  have hs : Summable fun n => a (n + 1) - a n :=
    NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (by rwa [Nat.cofinite_eq_atTop])
  have h1 := hs.hasSum.tendsto_sum_nat
  simp only [Finset.sum_range_sub] at h1
  refine ⟨_, (h1.add_const (a 0)).congr fun n => ?_⟩
  simp

/- English proof (translation)
Introduce `K _ _ _ G r hr hr1 hG hx hprod g hg hagree`. Establish `hcoef : ∀ n k, ‖PowerSeries.coeff k (g (n + 1)) - PowerSeries.coeff k (g n)‖ ≤ (∏ x ∈ G n, ‖x‖) / r ^ k`. Introduce `n k`. Establish `hI : Intg (g (n + 1) - g n)`. Rewrite using `[intg_iff_coeff_one_var]`.

Introduce `j`. Rewrite using `[map_sub, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `(intg_iff_coeff_one_var _).1 (hg _) j`. Rewrite using `[norm_neg]`.

Conclude with `(intg_iff_coeff_one_var _).1 (hg _) j`. Establish `hz : ∀ x ∈ G n, ‖x‖ < 1 ∧ ev1 (g (n + 1) - g n) x = 0`. Introduce `x hxn`. Use `⟨(hx n x hxn).2, ?_⟩` and prove the remaining obligations. Establish `h1` using `summable_coeff_mul_pow_of_intg (hg (n + 1)) (hx n x hxn).2`.

Establish `h2` using `summable_coeff_mul_pow_of_intg (hg n) (hx n x hxn).2`. Establish `h3` using `hagree n x hxn`. Unfold `ev1 at h3 ⊢`. Simplify using `only [map_sub, sub_mul]`. Rewrite using `[h1.tsum_sub h2, h3, sub_self]`.

Use `(GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K _ (G n) hI hz).1 r hr hr1 (fun x hxn => (hx n x hxn).1) k` as an intermediate fact. Rewrite `this` using `[map_sub]`. Rewrite using `[le_div_iff₀ (by positivity)]` and apply the resulting hypothesis. Establish `hlim : ∀ k, ∃ l, Tendsto (fun n => PowerSeries.coeff k (g n)) atTop (𝓝 l)`. Introduce `k`.

Apply `exists_tendsto_of_sub_tendsto_zero_ultra` to reduce the goal to its premises. Use `squeeze_zero_norm (fun n => hcoef n k) ?_` and prove the remaining obligations. Simplify using `using hprod.div_const (r ^ k)`. Use `choose c hc using hlim`. Establish `hfI : Intg (PowerSeries.mk c)`.

Rewrite using `[intg_iff_coeff_one_var]`. Introduce `k`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `le_of_tendsto' (hc k).norm fun n => (intg_iff_coeff_one_var _).1 (hg n) k`. Use `⟨PowerSeries.mk c, hfI, fun k => by simpa using hc k, ?_⟩` and prove the remaining obligations.

Introduce `n x hxn`. Establish `hx1` using `(hx n x hxn).2`. Establish `hconst : ∀ m, n ≤ m → ev1 (g m) x = ev1 (g n) x`. Introduce `m hm`. Proceed by induction on `m, hm using Nat.le_induction with`.

Consider the case `base => rfl`. Consider the case `succ m hm ih => rw [hagree m x (hG hm hxn), ih]`. Establish `ht : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (PowerSeries.mk c) x))`. Unfold `ev1`. Use `tendsto_tsum_of_dominated_convergence (bound := fun k => ‖x‖ ^ k) (summable_geometric_of_lt_one (norm_nonneg x) hx1) (fun k => ?_) (Eventually.of_forall fun m k => norm_coeff_mul_pow_le_of_intg (hg m) x k)` and prove the remaining obligations.

Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `(hc k).mul_const _`. Establish `ht2 : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (g n) x))` using `tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono fun m hm => (hconst m hm).symm)`. Conclude with `tendsto_nhds_unique ht ht2`.
-/
theorem exists_limit_of_agree_on_points : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (G : ℕ → Finset K) (r : ℝ), 0 < r → r ≤ 1 → Monotone G → (∀ n, ∀ x ∈ G n, r ≤ ‖x‖ ∧ ‖x‖ < 1) → Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) → ∀ g : ℕ → PowerSeries K, (∀ n, Intg (g n)) → (∀ n, ∀ x ∈ G n, ev1 (g (n + 1)) x = ev1 (g n) x) → ∃ f : PowerSeries K, Intg f ∧ (∀ k, Filter.Tendsto (fun n => PowerSeries.coeff k (g n)) Filter.atTop (nhds (PowerSeries.coeff k f))) ∧ ∀ n, ∀ x ∈ G n, ev1 f x = ev1 (g n) x := by
  intro K _ _ _ G r hr hr1 hG hx hprod g hg hagree
  have hcoef : ∀ n k, ‖PowerSeries.coeff k (g (n + 1)) - PowerSeries.coeff k (g n)‖ ≤
      (∏ x ∈ G n, ‖x‖) / r ^ k := by
    intro n k
    have hI : Intg (g (n + 1) - g n) := by
      rw [intg_iff_coeff_one_var]
      intro j
      rw [map_sub, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · exact (intg_iff_coeff_one_var _).1 (hg _) j
      · rw [norm_neg]; exact (intg_iff_coeff_one_var _).1 (hg _) j
    have hz : ∀ x ∈ G n, ‖x‖ < 1 ∧ ev1 (g (n + 1) - g n) x = 0 := by
      intro x hxn
      refine ⟨(hx n x hxn).2, ?_⟩
      have h1 := summable_coeff_mul_pow_of_intg (hg (n + 1)) (hx n x hxn).2
      have h2 := summable_coeff_mul_pow_of_intg (hg n) (hx n x hxn).2
      have h3 := hagree n x hxn
      unfold ev1 at h3 ⊢
      simp only [map_sub, sub_mul]
      rw [h1.tsum_sub h2, h3, sub_self]
    have := (GlobalTheory.T.norm_coeff_integral_powerSeries_le_prod_zeros K _ (G n) hI hz).1 r hr hr1 (fun x hxn => (hx n x hxn).1) k
    rw [map_sub] at this
    rwa [le_div_iff₀ (by positivity)]
  have hlim : ∀ k, ∃ l, Tendsto (fun n => PowerSeries.coeff k (g n)) atTop (𝓝 l) := by
    intro k
    apply exists_tendsto_of_sub_tendsto_zero_ultra
    refine squeeze_zero_norm (fun n => hcoef n k) ?_
    simpa using hprod.div_const (r ^ k)
  choose c hc using hlim
  have hfI : Intg (PowerSeries.mk c) := by
    rw [intg_iff_coeff_one_var]
    intro k
    rw [PowerSeries.coeff_mk]
    exact le_of_tendsto' (hc k).norm fun n => (intg_iff_coeff_one_var _).1 (hg n) k
  refine ⟨PowerSeries.mk c, hfI, fun k => by simpa using hc k, ?_⟩
  intro n x hxn
  have hx1 := (hx n x hxn).2
  have hconst : ∀ m, n ≤ m → ev1 (g m) x = ev1 (g n) x := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hagree m x (hG hm hxn), ih]
  have ht : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (PowerSeries.mk c) x)) := by
    unfold ev1
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖x‖ ^ k)
      (summable_geometric_of_lt_one (norm_nonneg x) hx1) (fun k => ?_)
      (Eventually.of_forall fun m k => norm_coeff_mul_pow_le_of_intg (hg m) x k)
    rw [PowerSeries.coeff_mk]
    exact (hc k).mul_const _
  have ht2 : Tendsto (fun m => ev1 (g m) x) atTop (𝓝 (ev1 (g n) x)) :=
    tendsto_const_nhds.congr' ((eventually_ge_atTop n).mono fun m hm => (hconst m hm).symm)
  exact tendsto_nhds_unique ht ht2

end GlobalTheory.ConvSer
