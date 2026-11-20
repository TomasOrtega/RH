import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscExpand

/- English proof (translation)
Use `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_` and prove the remaining obligations. Use `(denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖) (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y` and prove the remaining obligations. Rewrite using `[← map_add, norm_ofPre, norm_ofPre, norm_ofPre]`. Conclude with `gauge_add_le_max l u ρ a b`.
-/
theorem ultra (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) : IsUltrametricDist (Disc l u ρ) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add, norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

def smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ≥0) : Ideal A where
  carrier := {x | ‖toDisc l u ρ x‖ ≤ r}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    haveI := ultra l u ρ
    change ‖toDisc l u ρ (x + y)‖ ≤ r
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  smul_mem' a x hx := by
    change ‖toDisc l u ρ (a * x)‖ ≤ r
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_le _) hx (norm_nonneg _) zero_le_one).trans
      (one_mul _).le)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro x _`. Express the relevant statement in the definitionally equal form `‖toDisc l u ρ x‖ ≤ _`. Simplify using `using norm_toDisc_le x`. Consider the case `succ n ih`.

Rewrite using `[pow_succ]`. Use `Ideal.mul_le.2 fun x hx y hy => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `‖toDisc l u ρ (x * y)‖ ≤ _`. Rewrite using `[map_mul, pow_succ, NNReal.coe_mul]`. Conclude with `(norm_mul_le _ _).trans (mul_le_mul (ih hx) (h hy) (norm_nonneg _) (by positivity))`.
-/
theorem pow_le_smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ θ : ℝ≥0) (I : Ideal A)
    (h : I ≤ smallIdeal l u ρ θ) (n : ℕ) : I ^ n ≤ smallIdeal l u ρ (θ ^ n) := by
  induction n with
  | zero => intro x _; change ‖toDisc l u ρ x‖ ≤ _; simpa using norm_toDisc_le x
  | succ n ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    change ‖toDisc l u ρ (x * y)‖ ≤ _
    rw [map_mul, pow_succ, NNReal.coe_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (ih hx) (h hy) (norm_nonneg _) (by positivity))

/- English proof (translation)
Establish `hl1 : (1 : ℝ≥0) < l` using `by exact_mod_cast hl.out.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `Nat.cast_pos.2 hl.out.pos`. Use `set θ : ℝ≥0 := max (l : ℝ≥0)⁻¹ ρ with hθ`. Establish `hθ1 : θ < 1` using `max_lt (inv_lt_one_of_one_lt₀ hl1) h1`. Establish `hlm : (l : A) ∈ smallIdeal l (s X) ρ θ`.

Express the relevant statement in the definitionally equal form `‖toDisc l (s X) ρ l‖ ≤ _`. Use `le_trans ?_ (NNReal.coe_le_coe.2 (le_max_left _ _))` and prove the remaining obligations. Use `(norm_ofPre l (s X) ρ _).trans_le (gauge_le l (s X) ρ (by simpa using hl.out.pos) (Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩))` and prove the remaining obligations. Simplify using `[inv_mul_cancel₀ hl0.ne']`. Establish `hXm : s X ∈ smallIdeal l (s X) ρ θ`.

Express the relevant statement in the definitionally equal form `‖toDisc l (s X) ρ (s X)‖ ≤ _`. Use `le_trans ?_ (NNReal.coe_le_coe.2 (le_max_right _ _))` and prove the remaining obligations. Simplify using `using norm_toDisc_pow_le (l := l) (u := s X) 1 h0`. Establish `hE : s bk.E ∈ smallIdeal l (s X) ρ θ`. Take `⟨w, hw⟩` from `bk.coeff_zero`.

Establish `e : bk.E = X * (bk.Ep.divX : (Wq l bk.a)⟦X⟧) + (l : bk.S) * C (w : Wq l bk.a)`. Use `congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) (Polynomial.X_mul_divX_add bk.Ep)` as an intermediate fact. Simplify using `only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C] at this`. Rewrite `this` using `[hw, map_mul, map_natCast]`. Conclude with `this.symm`.

Rewrite using `[e, map_add, map_mul, map_mul, map_natCast]`. Conclude with `add_mem (Ideal.mul_mem_right _ _ hXm) (Ideal.mul_mem_right _ _ hlm)`. Establish `hJ : bk.J.map s ≤ smallIdeal l (s X) ρ θ`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Apply the tactic sequence `refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]`.

Rewrite using `[map_natCast]` and apply the resulting hypothesis. Conclude with `hE`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hr (NNReal.coe_lt_one.2 hθ1)`. Use `⟨n, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[Ideal.map_pow]`.

Use `pow_le_smallIdeal l (s X) ρ θ _ hJ n hx` as an intermediate fact. Conclude with `le_trans this (by rw [NNReal.coe_pow]; exact hn.le)`.
-/
theorem small (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  set θ : ℝ≥0 := max (l : ℝ≥0)⁻¹ ρ with hθ
  have hθ1 : θ < 1 := max_lt (inv_lt_one_of_one_lt₀ hl1) h1
  have hlm : (l : A) ∈ smallIdeal l (s X) ρ θ := by
    change ‖toDisc l (s X) ρ l‖ ≤ _
    refine le_trans ?_ (NNReal.coe_le_coe.2 (le_max_left _ _))
    refine (norm_ofPre l (s X) ρ _).trans_le (gauge_le l (s X) ρ (by simpa using hl.out.pos)
      (Submodule.subset_span ⟨1, 0, 0, ?_, by simp⟩))
    simp [inv_mul_cancel₀ hl0.ne']
  have hXm : s X ∈ smallIdeal l (s X) ρ θ := by
    change ‖toDisc l (s X) ρ (s X)‖ ≤ _
    refine le_trans ?_ (NNReal.coe_le_coe.2 (le_max_right _ _))
    simpa using norm_toDisc_pow_le (l := l) (u := s X) 1 h0
  have hE : s bk.E ∈ smallIdeal l (s X) ρ θ := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have e : bk.E = X * (bk.Ep.divX : (Wq l bk.a)⟦X⟧) + (l : bk.S) * C (w : Wq l bk.a) := by
      have := congrArg (fun p : Polynomial (Wq l bk.a) => (p : (Wq l bk.a)⟦X⟧)) (Polynomial.X_mul_divX_add bk.Ep)
      simp only [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C] at this
      rw [hw, map_mul, map_natCast] at this
      exact this.symm
    rw [e, map_add, map_mul, map_mul, map_natCast]
    exact add_mem (Ideal.mul_mem_right _ _ hXm) (Ideal.mul_mem_right _ _ hlm)
  have hJ : bk.J.map s ≤ smallIdeal l (s X) ρ θ := by
    rw [Ideal.map_le_iff_le_comap]
    refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    · rwa [map_natCast]
    · exact hE
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (NNReal.coe_lt_one.2 hθ1)
  refine ⟨n, fun x hx => ?_⟩
  rw [Ideal.map_pow] at hx
  have := pow_le_smallIdeal l (s X) ρ θ _ hJ n hx
  exact le_trans this (by rw [NNReal.coe_pow]; exact hn.le)

/- English proof (translation)
Use `isClosed_of_closure_subset fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[Metric.mem_closure_iff]`. Use `⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hd⟩` from `hy (ε / 2) (by positivity) filter_upwards [Metric.tendsto_nhds.1 hz.1 (ε / 2) (by positivity)] with i hi`. Rewrite `hi`, the goal using `[dist_zero_right]`.

Rewrite `hd` using `[dist_eq_norm]`. Establish `e : c i y = c i z + c i (y - z)` using `by rw [← map_add]; congr 1; ring`. Use `norm_add_le (c i z) (c i (y - z))` as an intermediate fact. Use `hc i (y - z)` as an intermediate fact. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z, hz, hd⟩` from `hy (ε / 3) (by positivity) filter_upwards [Metric.tendsto_nhds.1 hz.2 (ε / 3) (by positivity)] with F hF`. Rewrite `hd`, `hF`, the goal using `[dist_eq_norm]`. Establish `e : ∑ i ∈ F, j (c i y) * b i - y = (∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i) - (y - z)`. Simplify using `only [map_sub, sub_mul, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ‖∑ i ∈ F, j (c i (y - z)) * b i‖ ≤ ‖y - z‖` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => (norm_mul_le _ _).trans ((mul_le_mul ((hj _).trans (hc _ _)) (hb i) (norm_nonneg _) (norm_nonneg _)).trans (mul_one _).le)`. Establish `h3` using `norm_sub_le ((∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i)) (y - z)`. Establish `h4` using `norm_add_le (∑ i ∈ F, j (c i z) * b i - z) (∑ i ∈ F, j (c i (y - z)) * b i)`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isClosed_expand {D D' ι : Type} [NormedCommRing D] [NormedCommRing D'] [IsUltrametricDist D']
    (j : D →+* D') (hj : ∀ x, ‖j x‖ ≤ ‖x‖) (c : ι → (D' →+ D)) (hc : ∀ i y, ‖c i y‖ ≤ ‖y‖) (b : ι → D')
    (hb : ∀ i, ‖b i‖ ≤ 1) :
    IsClosed {y | Filter.Tendsto (fun i => c i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (c i y) * b i) y} := by
  refine isClosed_of_closure_subset fun y hy => ?_
  rw [Metric.mem_closure_iff] at hy
  refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  · obtain ⟨z, hz, hd⟩ := hy (ε / 2) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.1 (ε / 2) (by positivity)] with i hi
    rw [dist_zero_right] at hi ⊢
    rw [dist_eq_norm] at hd
    have e : c i y = c i z + c i (y - z) := by rw [← map_add]; congr 1; ring
    have := norm_add_le (c i z) (c i (y - z))
    have := hc i (y - z)
    rw [e]; linarith
  · obtain ⟨z, hz, hd⟩ := hy (ε / 3) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.2 (ε / 3) (by positivity)] with F hF
    rw [dist_eq_norm] at hd hF ⊢
    have e : ∑ i ∈ F, j (c i y) * b i - y =
        (∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i) - (y - z) := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
    have h2 : ‖∑ i ∈ F, j (c i (y - z)) * b i‖ ≤ ‖y - z‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ =>
        (norm_mul_le _ _).trans ((mul_le_mul ((hj _).trans (hc _ _)) (hb i) (norm_nonneg _) (norm_nonneg _)).trans
          (mul_one _).le)
    have h3 := norm_sub_le ((∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i)) (y - z)
    have h4 := norm_add_le (∑ i ∈ F, j (c i z) * b i - z) (∑ i ∈ F, j (c i (y - z)) * b i)
    rw [e]; linarith

/- English proof (translation)
Use `haveI := ultra l (s X) ρ`. Take `⟨hc1, hc2, hc3⟩` from `hc`. Use `(denseRange_ofPre l (s X) ρ).induction_on y (isClosed_expand j hj.norm_le cD hc3 _ fun i => norm_toDisc_le _) fun p => ?_` and prove the remaining obligations. Establish `base : ∀ a : A, Filter.Tendsto (fun i => cD i (toDisc l (s X) ρ a)) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (cD i (toDisc l (s X) ρ a)) * toDisc l (s X) ρ (TB.b i)) (toDisc l (s X) ρ a)`. Introduce `a`.

Use `⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `small l K bk bk.S (RingHom.id _) ρ h0 h1 (ε / 2) (by positivity)`. Use `Filter.mem_of_superset (TB.fin a n).compl_mem_cofinite fun i hi => ?_` and prove the remaining obligations. Establish `hi' : TB.c i a ∈ bk.J ^ n` using `by simpa using hi`. Establish `h2 : ‖toDisc l (X : bk.S) ρ (TB.c i a)‖ ≤ ε / 2` using `hn _ (by rwa [Ideal.map_id])`.

Express the relevant statement in the definitionally equal form `dist (cD i (toDisc l (s X) ρ a)) 0 < ε`. Rewrite using `[dist_zero_right, hc1]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, hn⟩` from `small l K bk A s ρ h0 h1 (ε / 2) (by positivity)`. Express the relevant statement in the definitionally equal form `∀ᶠ F in Filter.atTop, _`.

Use `filter_upwards [Filter.eventually_ge_atTop (TB.fin a n).toFinset] with F hF`. Establish `h2` using `hn _ (TB.approx a n F fun i hi => by`. Assume the negation of the conclusion as `h`. Conclude with `hi (hF (by simpa using h)))`. Rewrite `h2` using `[map_sub, map_sum]`.

Rewrite using `[dist_comm, dist_eq_norm]`. Simplify using `only [hc1, hj.ext, ← map_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨n, a, h⟩` from `IsLocalization.Away.surj (l : A) p`. Take `⟨w, hw⟩` from `(isUnit_l_disc l (X : bk.S) ρ).exists_left_inv`.

Establish `hw' : j w * l = 1` using `by rw [← map_natCast j, ← map_mul, hw, map_one]`. Establish `e : ofPre l (s X) ρ p = j (w ^ n) * toDisc l (s X) ρ a`. Establish `h2 : ofPre l (s X) ρ p * (l : Disc l (s X) ρ) ^ n = toDisc l (s X) ρ a`. Use `congrArg (ofPre l (s X) ρ) h` as an intermediate fact. Rewrite `this` using `[map_mul, map_pow, map_natCast, map_natCast]`. Then use the resulting hypothesis.

Rewrite using `[← h2, map_pow, mul_left_comm, ← mul_pow, hw', one_pow, mul_one]`. Rewrite using `[e]`. Simplify using `only [hc2]`. Use `⟨by simpa using (base a).1.const_mul (w ^ n), ?_⟩` and prove the remaining obligations. Simplify `(base a).2.mul_left (j (w ^ n))` using `only [map_mul, mul_assoc]`.
-/
theorem disc_expand (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (j : bk.DS ρ →+* Disc l (s X) ρ)
    (hj : IsDiscMap s j) (cD : ι → (Disc l (s X) ρ →+ bk.DS ρ))
    (hc : (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧
      (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) (y : Disc l (s X) ρ) :
    Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  haveI := ultra l (s X) ρ
  obtain ⟨hc1, hc2, hc3⟩ := hc
  refine (denseRange_ofPre l (s X) ρ).induction_on y
    (isClosed_expand j hj.norm_le cD hc3 _ fun i => norm_toDisc_le _) fun p => ?_
  have base : ∀ a : A, Filter.Tendsto (fun i => cD i (toDisc l (s X) ρ a)) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i (toDisc l (s X) ρ a)) * toDisc l (s X) ρ (TB.b i)) (toDisc l (s X) ρ a) := by
    intro a
    refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
    · obtain ⟨n, hn⟩ := small l K bk bk.S (RingHom.id _) ρ h0 h1 (ε / 2) (by positivity)
      refine Filter.mem_of_superset (TB.fin a n).compl_mem_cofinite fun i hi => ?_
      have hi' : TB.c i a ∈ bk.J ^ n := by simpa using hi
      have h2 : ‖toDisc l (X : bk.S) ρ (TB.c i a)‖ ≤ ε / 2 := hn _ (by rwa [Ideal.map_id])
      change dist (cD i (toDisc l (s X) ρ a)) 0 < ε
      rw [dist_zero_right, hc1]; linarith
    · obtain ⟨n, hn⟩ := small l K bk A s ρ h0 h1 (ε / 2) (by positivity)
      change ∀ᶠ F in Filter.atTop, _
      filter_upwards [Filter.eventually_ge_atTop (TB.fin a n).toFinset] with F hF
      have h2 := hn _ (TB.approx a n F fun i hi => by
        by_contra h
        exact hi (hF (by simpa using h)))
      rw [map_sub, map_sum] at h2
      rw [dist_comm, dist_eq_norm]
      simp only [hc1, hj.ext, ← map_mul]
      linarith
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : A) p
  obtain ⟨w, hw⟩ := (isUnit_l_disc l (X : bk.S) ρ).exists_left_inv
  have hw' : j w * l = 1 := by rw [← map_natCast j, ← map_mul, hw, map_one]
  have e : ofPre l (s X) ρ p = j (w ^ n) * toDisc l (s X) ρ a := by
    have h2 : ofPre l (s X) ρ p * (l : Disc l (s X) ρ) ^ n = toDisc l (s X) ρ a := by
      have := congrArg (ofPre l (s X) ρ) h
      rwa [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [← h2, map_pow, mul_left_comm, ← mul_pow, hw', one_pow, mul_one]
  rw [e]
  simp only [hc2]
  refine ⟨by simpa using (base a).1.const_mul (w ^ n), ?_⟩
  simpa only [map_mul, mul_assoc] using (base a).2.mul_left (j (w ^ n))

end GlobalTheory.BSP.DiscExpand
