import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassPreparation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StParametricCircleIntegralAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCircleArgumentPrinciple
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPowerSumsEsymmAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

def pointWithLastCLM (σ : Type) : ((σ → ℂ) × ℂ) →L[ℂ] (Option σ → ℂ) :=
  ContinuousLinearMap.pi fun o => match o with
    | none => ContinuousLinearMap.snd ℂ (σ → ℂ) ℂ
    | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℂ (σ → ℂ) ℂ)

/- English proof (translation)
Apply the tactic sequence `funext o; cases o <;> rfl`.
-/
theorem pointWithLastCLM_apply {σ : Type} (p : (σ → ℂ) × ℂ) :
    pointWithLastCLM σ p = pointWithLast p.1 p.2 := by
  funext o; cases o <;> rfl

/- English proof (translation)
Apply the tactic sequence `funext o; cases o <;> rfl`.
-/
theorem pointWithLast_coords {σ : Type} (x : Option σ → ℂ) :
    pointWithLast (fun i => x (some i)) (x none) = x := by
  funext o; cases o <;> rfl

/- English proof (translation)
Establish `h' : |(m : ℝ) - n| < 1`. Establish `e : ((m : ℂ) - n) = (((m : ℝ) - n : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite `h` using `[e, Complex.norm_real, Real.norm_eq_abs]`. Then use the resulting hypothesis. Rewrite `h'` using `[abs_lt]`. Establish `h1 : m < n + 1` using `by exact_mod_cast (show (m : ℝ) < n + 1 by linarith)`.

Establish `h2 : n < m + 1` using `by exact_mod_cast (show (n : ℝ) < m + 1 by linarith)`. Use linear arithmetic over natural numbers and integers.
-/
theorem natCast_eq_of_norm_sub_lt_one {m n : ℕ} (h : ‖(m : ℂ) - n‖ < 1) : m = n := by
  have h' : |(m : ℝ) - n| < 1 := by
    have e : ((m : ℂ) - n) = (((m : ℝ) - n : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_lt] at h'
  have h1 : m < n + 1 := by exact_mod_cast (show (m : ℝ) < n + 1 by linarith)
  have h2 : n < m + 1 := by exact_mod_cast (show (n : ℝ) < m + 1 by linarith)
  omega

/- English proof (translation)
Unfold `Multiset.esymm`. Use `Multiset.sum_eq_zero fun x hx => ?_` and prove the remaining obligations. Take `⟨t, ht, rfl⟩` from `Multiset.mem_map.1 hx`. Take `⟨hle, hcard⟩` from `Multiset.mem_powersetCard.1 ht`. Establish `: t = Multiset.replicate k 0` using `Multiset.eq_replicate.2 ⟨hcard, fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le hle hb)⟩`.

Rewrite using `[this, Multiset.prod_replicate, zero_pow (by omega)]`.
-/
theorem esymm_replicate_zero {n k : ℕ} (hk : 1 ≤ k) : (Multiset.replicate n (0 : ℂ)).esymm k = 0 := by
  unfold Multiset.esymm
  refine Multiset.sum_eq_zero fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨hle, hcard⟩ := Multiset.mem_powersetCard.1 ht
  have : t = Multiset.replicate k 0 :=
    Multiset.eq_replicate.2 ⟨hcard, fun b hb => Multiset.eq_of_mem_replicate (Multiset.mem_of_le hle hb)⟩
  rw [this, Multiset.prod_replicate, zero_pow (by omega)]

/- English proof (translation)
Substitute `hZ` using the available equality. Use `set p : Polynomial ℂ := (Z.map fun a => Polynomial.X - Polynomial.C a).prod with hp`. Establish `hdeg : p.natDegree = Multiset.card Z` using `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card Z`. Establish `h1 : p.eval t = (Z.map fun a => t - a).prod`. Rewrite using `[hp, Polynomial.eval_multiset_prod, Multiset.map_map]`.

Use `congr 1`. Conclude with `Multiset.map_congr rfl fun a _ => by simp`. Rewrite using `[← h1, Polynomial.eval_eq_sum_range' (n := Multiset.card Z + 1) (by omega), Finset.sum_range_succ, hp, Multiset.prod_X_sub_C_coeff Z le_rfl, ← hp]`. Simplify using `only [weierstrassPolynomial, Nat.sub_self, pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left, Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton, one_mul]`. Rewrite using `[add_comm]`.

Use `congr 1`. Simplify using `only [show (fun i => pointWithLast z t (some i)) = z from rfl, show pointWithLast z t none = t from rfl, hc]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (-1) ^ (Multiset.card Z - i) * Z.esymm (Multiset.card Z - i) * t ^ i)]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hp, Multiset.prod_X_sub_C_coeff Z (Finset.mem_range.1 hi).le]`.
-/
theorem weierstrassPolynomial_eq_prod {σ : Type} {d : ℕ} (c : Fin d → (σ → ℂ) → ℂ) (z : σ → ℂ)
    (Z : Multiset ℂ) (hZ : Multiset.card Z = d)
    (hc : ∀ j : Fin d, c j z = (-1) ^ (d - (j : ℕ)) * Z.esymm (d - (j : ℕ))) (t : ℂ) :
    weierstrassPolynomial c (pointWithLast z t) = (Z.map fun a => t - a).prod := by
  subst hZ
  set p : Polynomial ℂ := (Z.map fun a => Polynomial.X - Polynomial.C a).prod with hp
  have hdeg : p.natDegree = Multiset.card Z := Polynomial.natDegree_multiset_prod_X_sub_C_eq_card Z
  have h1 : p.eval t = (Z.map fun a => t - a).prod := by
    rw [hp, Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun a _ => by simp
  rw [← h1, Polynomial.eval_eq_sum_range' (n := Multiset.card Z + 1) (by omega), Finset.sum_range_succ,
    hp, Multiset.prod_X_sub_C_coeff Z le_rfl, ← hp]
  simp only [weierstrassPolynomial, Nat.sub_self, pow_zero, Multiset.esymm, Multiset.powersetCard_zero_left,
    Multiset.map_singleton, Multiset.prod_zero, Multiset.sum_singleton, one_mul]
  rw [add_comm]
  congr 1
  simp only [show (fun i => pointWithLast z t (some i)) = z from rfl, show pointWithLast z t none = t from rfl, hc]
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1) ^ (Multiset.card Z - i) * Z.esymm (Multiset.card Z - i) * t ^ i)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hp, Multiset.prod_X_sub_C_coeff Z (Finset.mem_range.1 hi).le]

/- English proof (translation)
Introduce `σ _ d f hf hord`. Use `set L := pointWithLastCLM σ`. Use `set O : Set (Option σ → ℂ) := {x | AnalyticAt ℂ f x} with hO`. Establish `hOo : IsOpen O` using `isOpen_analyticAt ℂ f`. Use `set F : (σ → ℂ) × ℂ → ℂ := fun p => f (L p) with hF`.

Establish `hFapply : ∀ z s, F (z, s) = f (pointWithLast z s)` using `fun z s => by`. Simplify using `only [hF, L, pointWithLastCLM_apply]`. Use `set O1 : Set ((σ → ℂ) × ℂ) := L ⁻¹' O with hO1def`. Establish `hO1 : IsOpen O1` using `hOo.preimage L.continuous`. Establish `hFd : DifferentiableOn ℂ F O1` using `fun p hp => ((show AnalyticAt ℂ f (L p) from hp).differentiableAt.comp p L.differentiableAt).differentiableWithinAt`.

Establish `hslice : ∀ z, IsOpen {s : ℂ | (z, s) ∈ O1}` using `fun z => hO1.preimage (continuous_const.prodMk continuous_id)`. Establish `hsliced : ∀ z, DifferentiableOn ℂ (fun s => F (z, s)) {s | (z, s) ∈ O1}` using `fun z => hFd.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun s hs => hs`. Establish `hL0 : L (0, 0) = 0` using `map_zero L`. Establish `hg0 : AnalyticAt ℂ (fun t => f (pointWithLast 0 t)) 0`. Establish `hlin : AnalyticAt ℂ (L.comp (ContinuousLinearMap.inr ℂ (σ → ℂ) ℂ)) 0` using `(L.comp (ContinuousLinearMap.inr ℂ (σ → ℂ) ℂ)).analyticAt 0`.

Use `hf.comp_of_eq hlin (by simp [hL0])` as an intermediate fact. Use `this.congr (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `[L, pointWithLastCLM_apply]`. Establish `hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (pointWithLast 0 t) ≠ 0`. Break down `hg0.eventually_eq_zero_or_eventually_ne_zero with h | h` into its components or cases.

Conclude with `absurd (analyticOrderAt_eq_top.2 h) (by rw [hord]; exact ENat.natCast_ne_top d)`. Conclude with `h`. Establish `h00 : ((0 : σ → ℂ), (0 : ℂ)) ∈ O1` using `by show AnalyticAt ℂ f (L (0, 0))`. Rewrite using `[hL0]`. Conclude with `hf`.

Establish `hO1t : ∀ᶠ t in 𝓝 (0 : ℂ), ((0 : σ → ℂ), t) ∈ O1` using `(hslice 0).mem_nhds h00`. Take `⟨ε, hε, hball⟩` from `Metric.eventually_nhds_iff_ball.1 ((eventually_nhdsWithin_iff.1 hne).and hO1t)`. Use `set r := ε / 2 with hrdef`. Establish `hr : 0 < r` using `half_pos hε`. Establish `hrb : closedBall (0 : ℂ) r ⊆ ball 0 ε` using `closedBall_subset_ball (half_lt_self hε)`.

Establish `hev : ∀ᶠ z : σ → ℂ in 𝓝 0, (∀ s ∈ closedBall (0 : ℂ) r, (z, s) ∈ O1) ∧ (∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0)`. Use `((isCompact_closedBall 0 r).eventually_forall_of_forall_eventually fun s hs => ?_).and ((isCompact_sphere 0 r).eventually_forall_of_forall_eventually fun s hs => ?_)` and prove the remaining obligations. Conclude with `hO1.mem_nhds (hball s (hrb hs)).2`. Establish `hs0 : s ≠ 0` using `ne_of_mem_sphere hs hr.ne'`. Establish `hb` using `hball s (hrb (sphere_subset_closedBall hs))`.

Establish `hF0 : F (0, s) ≠ 0` using `by rw [hFapply]; exact hb.1 hs0`. Conclude with `(hFd.continuousOn.continuousAt (hO1.mem_nhds hb.2)).eventually_ne hF0`. Take `⟨U, hUgood, hUo, hU0⟩` from `_root_.eventually_nhds_iff.1 hev`. Establish `hex : ∀ z, ∃ (Z : Multiset ℂ) (u : ℂ → ℂ), z ∈ U → ((∀ a ∈ Z, a ∈ ball (0 : ℂ) r) ∧ DifferentiableOn ℂ u {s | (z, s) ∈ O1} ∧ (∀ s ∈ closedBall (0 : ℂ) r, u s ≠ 0) ∧ (∀ s ∈ {s | (z, s) ∈ O1}, F (z, s) = (Z.map fun a => s - a).prod * u s) ∧ ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ {s | (z …`. Introduce `z`.

Distinguish the cases in `hz : z ∈ U`. Take `⟨Z, u, h⟩` from `hA (fun s => F (z, s)) _ 0 r hr (hslice z) (hUgood z hz).1 (hsliced z) (hUgood z hz).2`. Conclude with `⟨Z, u, fun _ => h⟩`. Conclude with `⟨0, 0, fun h => absurd h hz⟩`. Use `choose Z u hZu using hex`.

Use `set e1 : Option σ → ℂ := L (0, 1) with he1`. Use `set Dt : (σ → ℂ) × ℂ → ℂ := fun p => fderiv ℂ f (L p) e1 with hDtdef`. Establish `hDt : DifferentiableOn ℂ Dt O1`. Establish `hfO : AnalyticOnNhd ℂ f O` using `fun x hx => hx`. Establish `h1 : DifferentiableOn ℂ (fun p => fderiv ℂ f (L p)) O1` using `fun p hp => ((hfO.fderiv _ hp).differentiableAt.comp p L.differentiableAt).differentiableWithinAt`.

Conclude with `h1.clm_apply (differentiableOn_const e1)`. Establish `hderiv : ∀ z s, (z, s) ∈ O1 → deriv (fun s => F (z, s)) s = Dt (z, s)`. Introduce `z s hs`. Establish `h1 : HasFDerivAt f (fderiv ℂ f (L (z, s))) (L (z, s))` using `(show AnalyticAt ℂ f (L (z, s)) from hs).differentiableAt.hasFDerivAt`. Establish `h2 : HasDerivAt (fun s : ℂ => (z, s)) ((0 : σ → ℂ), (1 : ℂ)) s` using `(hasDerivAt_const s z).prodMk (hasDerivAt_id s)`.

Establish `h3` using `h1.comp_hasDerivAt s (L.hasFDerivAt.comp_hasDerivAt s h2)`. Conclude with `h3.deriv`. Establish `hps : ∀ k : ℕ, AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) U`. Introduce `k`. Use `set O2 : Set ((σ → ℂ) × ℂ) := O1 ∩ F ⁻¹' {0}ᶜ with hO2def`.

Establish `hO2 : IsOpen O2` using `hFd.continuousOn.isOpen_inter_preimage hO1 isOpen_compl_singleton`. Establish `hnum : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ k * Dt p) O2` using `(differentiableOn_snd.pow k).mul (hDt.mono Set.inter_subset_left)`. Establish `hΦ : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ k * Dt p / F p) O2` using `by simp only [div_eq_mul_inv]; exact hnum.mul ((hFd.mono Set.inter_subset_left).inv fun p (hp : p ∈ O2) => hp.2)`. Establish `hint` using `hC σ (fun p => p.2 ^ k * Dt p / F p) O2 U 0 r hr.le hO2 hUo hΦ fun z hz s hs => ⟨(hUgood z hz).1 s (sphere_subset_closedBall hs), (hUgood z hz).2 s hs⟩`. Introduce `z hz`.

Establish `h1 : AnalyticAt ℂ (fun z => (2 * π * I)⁻¹ * ∮ s in C(0, r), s ^ k * Dt (z, s) / F (z, s)) z` using `analyticAt_const.mul (hint z hz)`. Use `h1.congr (Filter.eventually_of_mem (hUo.mem_nhds hz) fun w hw => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[← (hZu w hw).2.2.2.2 (fun a => a ^ k) (differentiable_pow k).differentiableOn]`. Use `congr 1`.

Use `circleIntegral.integral_congr hr.le fun s hs => ?_` and prove the remaining obligations. Simplify using `only [hderiv w s ((hUgood w hw).1 s (sphere_subset_closedBall hs))]`. Establish `hZ0 : ∀ a ∈ Z 0, a = 0`. Introduce `a ha`. Establish `h` using `hZu 0 hU0`.

Assume the negation of the conclusion as `hne0`. Establish `haB : a ∈ closedBall (0 : ℂ) r` using `ball_subset_closedBall (h.1 a ha)`. Establish `hFa` using `h.2.2.2.1 a ((hUgood 0 hU0).1 a haB)`. Establish `hz : F (0, a) = 0`. Rewrite using `[hFa, Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, sub_self a⟩), zero_mul]`.

Conclude with `(hball a (hrb haB)).1 hne0 (by rw [← hFapply]; exact hz)`. Establish `hcard0 : Multiset.card (Z 0) = d`. Establish `h` using `hZu 0 hU0`. Establish `h0B : (0 : ℂ) ∈ closedBall (0 : ℂ) r` using `mem_closedBall_self hr.le`. Establish `hmem : {s : ℂ | ((0 : σ → ℂ), s) ∈ O1} ∈ 𝓝 (0 : ℂ)` using `(hslice 0).mem_nhds ((hUgood 0 hU0).1 0 h0B)`.

Establish `hrep : Z 0 = Multiset.replicate (Multiset.card (Z 0)) 0` using `Multiset.eq_replicate.2 ⟨rfl, hZ0⟩`. Establish `hord' : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = (Multiset.card (Z 0) : ℕ)`. Use `hg0.analyticOrderAt_eq_natCast.2 ⟨u 0, h.2.1.analyticAt hmem, h.2.2.1 0 h0B, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hmem] with s hs`. Rewrite using `[← hFapply, h.2.2.2.1 s hs]`.

Use `conv_lhs => rw [hrep]`. Simplify using the standard rewrite rules. Rewrite `hord'` using `[hord]`. Conclude with `hord'.symm` after adjusting the coercions. Establish `hcont : ContinuousAt (fun z => (Multiset.card (Z z) : ℂ)) 0`.

Use `(hps 0 0 hU0).continuousAt` as an intermediate fact. Simplify using `using this`. Establish `hevd : ∀ᶠ z in 𝓝 (0 : σ → ℂ), Multiset.card (Z z) = d` using `by filter_upwards [hcont.eventually (Metric.ball_mem_nhds ((Multiset.card (Z 0) : ℂ)) one_pos)] with z hz`. Rewrite `hz` using `[dist_eq_norm, hcard0]`. Conclude with `natCast_eq_of_norm_sub_lt_one hz`.

Take `⟨U2, hU2, hU2o, hU20⟩` from `_root_.eventually_nhds_iff.1 (hevd.and (hUo.mem_nhds hU0))`. Establish `hes : ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) U2` using `hN σ U2 d Z hU2o (fun z hz => (hU2 z hz).1) fun k _ _ => (hps k).mono fun z hz => (hU2 z hz).2`. Use `set c : Fin d → (σ → ℂ) → ℂ := fun j z => (-1) ^ (d - (j : ℕ)) * (Z z).esymm (d - (j : ℕ)) with hcdef`. Establish `hcan : ∀ j, AnalyticOnNhd ℂ (c j) U2` using `fun j => analyticOnNhd_const.mul (hes _)`. Establish `hc0 : ∀ j, c j 0 = 0`.

Introduce `j`. Establish `hrep : Z 0 = Multiset.replicate d 0` using `Multiset.eq_replicate.2 ⟨hcard0, hZ0⟩`. Simplify using `only [hcdef, hrep, esymm_replicate_zero (show 1 ≤ d - (j : ℕ) by omega), mul_zero]`. Use `set W : (σ → ℂ) × ℂ → ℂ := fun p => p.2 ^ d + ∑ j, c j p.1 * p.2 ^ (j : ℕ) with hWdef`. Establish `hWprod : ∀ z ∈ U2, ∀ s, W (z, s) = ((Z z).map fun a => s - a).prod` using `fun z hz s => weierstrassPolynomial_eq_prod c z (Z z) (hU2 z hz).1 (fun j => rfl) s`.

Establish `hWd : DifferentiableOn ℂ W (Prod.fst ⁻¹' U2)`. Establish `h1 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d) (Prod.fst ⁻¹' U2)` using `differentiableOn_snd.pow d`. Establish `h2 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => ∑ j, c j p.1 * p.2 ^ (j : ℕ)) (Prod.fst ⁻¹' U2)` using `DifferentiableOn.fun_sum fun j _ => by`. Establish `hc1 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => c j p.1) (Prod.fst ⁻¹' U2)` using `(hcan j).differentiableOn.comp differentiableOn_fst fun p hp => hp`. Conclude with `hc1.mul (differentiableOn_snd.pow _)`.

Conclude with `h1.add h2`. Use `set P : (Option σ → ℂ) →L[ℂ] (σ → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (some i) with hPdef`. Use `set q : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => (P p.1, p.2) with hqdef`. Establish `hqc : Continuous q` using `(P.continuous.comp continuous_fst).prodMk continuous_snd`. Establish `hqd : Differentiable ℂ q` using `(P.differentiable.comp differentiable_fst).prodMk differentiable_snd`.

Use `set A : Set ((Option σ → ℂ) × ℂ) := q ⁻¹' (O1 ∩ Prod.fst ⁻¹' U2) with hAdef`. Establish `hAo : IsOpen A` using `(hO1.inter (hU2o.preimage continuous_fst)).preimage hqc`. Use `set G : (Option σ → ℂ) × ℂ → ℂ := fun p => W (q p) * (p.2 - p.1 none) with hGdef`. Establish `hGd : DifferentiableOn ℂ G A`. Establish `hlast : DifferentiableOn ℂ (fun p : (Option σ → ℂ) × ℂ => p.2 - p.1 none) A` using `differentiableOn_snd.sub ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp (ContinuousLinearMap.fst ℂ (Option σ → ℂ) ℂ)).differentiableOn`.

Conclude with `(hWd.comp hqd.differentiableOn fun p (hp : p ∈ A) => hp.2).mul hlast`. Use `set O3 : Set ((Option σ → ℂ) × ℂ) := A ∩ G ⁻¹' {0}ᶜ with hO3def`. Establish `hO3 : IsOpen O3` using `hGd.continuousOn.isOpen_inter_preimage hAo isOpen_compl_singleton`. Use `set Φe : (Option σ → ℂ) × ℂ → ℂ := fun p => F (q p) / G p with hΦedef`. Establish `hΦe : DifferentiableOn ℂ Φe O3`.

Simplify using `only [hΦedef, div_eq_mul_inv]`. Conclude with `(hFd.comp hqd.differentiableOn fun p (hp : p ∈ O3) => hp.1.1).mul ((hGd.mono Set.inter_subset_left).inv fun p (hp : p ∈ O3) => hp.2)`. Use `set U3 : Set (Option σ → ℂ) := P ⁻¹' U2 ∩ {x | ‖x none‖ < r} with hU3def`. Establish `hU3o : IsOpen U3` using `(hU2o.preimage P.continuous).inter (isOpen_lt (continuous_norm.comp (continuous_apply none)) continuous_const)`. Establish `hmem3 : ∀ x ∈ U3, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ O3`.

Introduce `x hx s hs`. Establish `hzU` using `(hU2 (P x) hx.1).2`. Use `⟨⟨(hUgood _ hzU).1 s (sphere_subset_closedBall hs), hx.1⟩, ?_⟩` and prove the remaining obligations. Establish `hsn : ‖s‖ = r` using `by simpa using hs`. Establish `hxn : ‖x none‖ < r` using `hx.2`.

Rewrite using `[Set.mem_preimage, Set.mem_compl_singleton_iff]`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Use `show W (P x, s) ≠ 0`. Rewrite using `[hWprod _ hx.1]`. Use `Multiset.prod_ne_zero fun h0 => ?_` and prove the remaining obligations.

Take `⟨a, ha, has⟩` from `Multiset.mem_map.1 h0`. Establish `hab` using `mem_ball_zero_iff.1 ((hZu _ hzU).1 a ha)`. Rewrite `has` using `[sub_eq_zero]`. Rewrite `hab` using `[← has]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `h0`. Establish `h0' : s = x none` using `sub_eq_zero.1 h0`. Rewrite `hxn` using `[← h0']`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hint3` using `hC (Option σ) Φe O3 U3 0 r hr.le hO3 hU3o hΦe hmem3`.

Use `set e : (Option σ → ℂ) → ℂ := fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φe (x, s) with hedef`. Establish `he_eq : ∀ x ∈ U3, e x = u (P x) (x none)`. Introduce `x hx`. Establish `hzU` using `(hU2 (P x) hx.1).2`. Establish `h` using `hZu (P x) hzU`.

Establish `hw : x none ∈ ball (0 : ℂ) r` using `mem_ball_zero_iff.2 hx.2`. Establish `hcl : ∀ s ∈ closedBall (0 : ℂ) r, (P x, s) ∈ O1` using `(hUgood _ hzU).1`. Establish `hcauchy` using `two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable Set.countable_empty hw (h.2.1.continuousOn.mono hcl) fun s hs => h.2.1.differentiableAt ((hslice _).mem_nhds (hcl s (ball_subset_closedBall hs.1)))`. Rewrite using `[← hcauchy, smul_eq_mul]`. Use `show (2 * π * I)⁻¹ * _ = _`.

Use `congr 1`. Use `circleIntegral.integral_congr hr.le fun s hs => ?_` and prove the remaining obligations. Establish `hsO` using `hcl s (sphere_subset_closedBall hs)`. Establish `hG` using `(hmem3 x hx s hs).2`. Establish `hG' : G (x, s) = ((Z (P x)).map fun a => s - a).prod * (s - x none)` using `by show W (P x, s) * (s - x none) = _`.

Rewrite using `[hWprod _ hx.1]`. Rewrite `hG` using `[Set.mem_preimage, Set.mem_compl_singleton_iff, hG']`. Establish `h1` using `left_ne_zero_of_mul hG`. Simplify using `only [hΦedef, smul_eq_mul]`. Rewrite using `[show F (q (x, s)) = F (P x, s) from rfl, h.2.2.2.1 s hsO, hG', mul_div_mul_left _ _ h1, div_eq_mul_inv, mul_comm]`.

Establish `hU30 : (0 : Option σ → ℂ) ∈ U3`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show P 0 ∈ U2`. Rewrite using `[map_zero]`. Conclude with `hU20`.

Use `show ‖(0 : Option σ → ℂ) none‖ < r`. Simplify using `using hr`. Use `⟨e, c, analyticAt_const.mul (hint3 0 hU30), ?_, fun j => hcan j 0 hU20, hc0, ?_⟩` and prove the remaining obligations. Rewrite using `[he_eq 0 hU30, map_zero, Pi.zero_apply]`. Conclude with `(hZu 0 hU0).2.2.1 0 (mem_closedBall_self hr.le)`.

Use `filter_upwards [hU3o.mem_nhds hU30] with x hx`. Establish `hzU` using `(hU2 (P x) hx.1).2`. Rewrite using `[he_eq x hx]`. Establish `hx' : f x = F (P x, x none)`. Rewrite using `[hFapply]`.

Conclude with `(congrArg f (pointWithLast_coords x)).symm`. Establish `hxO : x none ∈ {s | (P x, s) ∈ O1}` using `(hUgood _ hzU).1 _ (ball_subset_closedBall (mem_ball_zero_iff.2 hx.2))`. Rewrite using `[hx', (hZu _ hzU).2.2.2.1 _ hxO, ← hWprod _ hx.1, mul_comm]`. Both sides reduce to the same expression.
-/
theorem WeierstrassPreparation.proof (hC : ParametricCircleIntegralAnalytic.Statement)
    (hA : CircleArgumentPrinciple.Statement) (hN : PowerSumsEsymmAnalytic.Statement) :
    WeierstrassPreparation.Statement := by
  intro σ _ d f hf hord

  set L := pointWithLastCLM σ
  set O : Set (Option σ → ℂ) := {x | AnalyticAt ℂ f x} with hO
  have hOo : IsOpen O := isOpen_analyticAt ℂ f
  set F : (σ → ℂ) × ℂ → ℂ := fun p => f (L p) with hF
  have hFapply : ∀ z s, F (z, s) = f (pointWithLast z s) := fun z s => by
    simp only [hF, L, pointWithLastCLM_apply]
  set O1 : Set ((σ → ℂ) × ℂ) := L ⁻¹' O with hO1def
  have hO1 : IsOpen O1 := hOo.preimage L.continuous
  have hFd : DifferentiableOn ℂ F O1 := fun p hp =>
    ((show AnalyticAt ℂ f (L p) from hp).differentiableAt.comp p L.differentiableAt).differentiableWithinAt
  have hslice : ∀ z, IsOpen {s : ℂ | (z, s) ∈ O1} := fun z =>
    hO1.preimage (continuous_const.prodMk continuous_id)
  have hsliced : ∀ z, DifferentiableOn ℂ (fun s => F (z, s)) {s | (z, s) ∈ O1} := fun z =>
    hFd.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun s hs => hs

  have hL0 : L (0, 0) = 0 := map_zero L
  have hg0 : AnalyticAt ℂ (fun t => f (pointWithLast 0 t)) 0 := by
    have hlin : AnalyticAt ℂ (L.comp (ContinuousLinearMap.inr ℂ (σ → ℂ) ℂ)) 0 :=
      (L.comp (ContinuousLinearMap.inr ℂ (σ → ℂ) ℂ)).analyticAt 0
    have := hf.comp_of_eq hlin (by simp [hL0])
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [L, pointWithLastCLM_apply]
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), f (pointWithLast 0 t) ≠ 0 := by
    rcases hg0.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.2 h) (by rw [hord]; exact ENat.natCast_ne_top d)
    · exact h
  have h00 : ((0 : σ → ℂ), (0 : ℂ)) ∈ O1 := by
    show AnalyticAt ℂ f (L (0, 0))
    rw [hL0]; exact hf
  have hO1t : ∀ᶠ t in 𝓝 (0 : ℂ), ((0 : σ → ℂ), t) ∈ O1 :=
    (hslice 0).mem_nhds h00
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((eventually_nhdsWithin_iff.1 hne).and hO1t)
  set r := ε / 2 with hrdef
  have hr : 0 < r := half_pos hε
  have hrb : closedBall (0 : ℂ) r ⊆ ball 0 ε := closedBall_subset_ball (half_lt_self hε)

  have hev : ∀ᶠ z : σ → ℂ in 𝓝 0,
      (∀ s ∈ closedBall (0 : ℂ) r, (z, s) ∈ O1) ∧ (∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0) := by
    refine ((isCompact_closedBall 0 r).eventually_forall_of_forall_eventually fun s hs => ?_).and
      ((isCompact_sphere 0 r).eventually_forall_of_forall_eventually fun s hs => ?_)
    · exact hO1.mem_nhds (hball s (hrb hs)).2
    · have hs0 : s ≠ 0 := ne_of_mem_sphere hs hr.ne'
      have hb := hball s (hrb (sphere_subset_closedBall hs))
      have hF0 : F (0, s) ≠ 0 := by rw [hFapply]; exact hb.1 hs0
      exact (hFd.continuousOn.continuousAt (hO1.mem_nhds hb.2)).eventually_ne hF0
  obtain ⟨U, hUgood, hUo, hU0⟩ := _root_.eventually_nhds_iff.1 hev

  have hex : ∀ z, ∃ (Z : Multiset ℂ) (u : ℂ → ℂ), z ∈ U →
      ((∀ a ∈ Z, a ∈ ball (0 : ℂ) r) ∧ DifferentiableOn ℂ u {s | (z, s) ∈ O1} ∧
        (∀ s ∈ closedBall (0 : ℂ) r, u s ≠ 0) ∧
        (∀ s ∈ {s | (z, s) ∈ O1}, F (z, s) = (Z.map fun a => s - a).prod * u s) ∧
        ∀ φ : ℂ → ℂ, DifferentiableOn ℂ φ {s | (z, s) ∈ O1} →
          (2 * π * I)⁻¹ * (∮ s in C(0, r), φ s * deriv (fun s => F (z, s)) s / F (z, s)) = (Z.map φ).sum) := by
    intro z
    by_cases hz : z ∈ U
    · obtain ⟨Z, u, h⟩ := hA (fun s => F (z, s)) _ 0 r hr (hslice z) (hUgood z hz).1 (hsliced z)
        (hUgood z hz).2
      exact ⟨Z, u, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hz⟩
  choose Z u hZu using hex

  set e1 : Option σ → ℂ := L (0, 1) with he1
  set Dt : (σ → ℂ) × ℂ → ℂ := fun p => fderiv ℂ f (L p) e1 with hDtdef
  have hDt : DifferentiableOn ℂ Dt O1 := by
    have hfO : AnalyticOnNhd ℂ f O := fun x hx => hx
    have h1 : DifferentiableOn ℂ (fun p => fderiv ℂ f (L p)) O1 := fun p hp =>
      ((hfO.fderiv _ hp).differentiableAt.comp p L.differentiableAt).differentiableWithinAt
    exact h1.clm_apply (differentiableOn_const e1)
  have hderiv : ∀ z s, (z, s) ∈ O1 → deriv (fun s => F (z, s)) s = Dt (z, s) := by
    intro z s hs
    have h1 : HasFDerivAt f (fderiv ℂ f (L (z, s))) (L (z, s)) :=
      (show AnalyticAt ℂ f (L (z, s)) from hs).differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℂ => (z, s)) ((0 : σ → ℂ), (1 : ℂ)) s :=
      (hasDerivAt_const s z).prodMk (hasDerivAt_id s)
    have h3 := h1.comp_hasDerivAt s (L.hasFDerivAt.comp_hasDerivAt s h2)
    exact h3.deriv

  have hps : ∀ k : ℕ, AnalyticOnNhd ℂ (fun z => ((Z z).map fun a => a ^ k).sum) U := by
    intro k
    set O2 : Set ((σ → ℂ) × ℂ) := O1 ∩ F ⁻¹' {0}ᶜ with hO2def
    have hO2 : IsOpen O2 := hFd.continuousOn.isOpen_inter_preimage hO1 isOpen_compl_singleton
    have hnum : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ k * Dt p) O2 :=
      (differentiableOn_snd.pow k).mul (hDt.mono Set.inter_subset_left)
    have hΦ : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ k * Dt p / F p) O2 :=
      by simp only [div_eq_mul_inv]; exact hnum.mul ((hFd.mono Set.inter_subset_left).inv fun p (hp : p ∈ O2) => hp.2)
    have hint := hC σ (fun p => p.2 ^ k * Dt p / F p) O2 U 0 r hr.le hO2 hUo hΦ
      fun z hz s hs => ⟨(hUgood z hz).1 s (sphere_subset_closedBall hs), (hUgood z hz).2 s hs⟩
    intro z hz
    have h1 : AnalyticAt ℂ (fun z => (2 * π * I)⁻¹ * ∮ s in C(0, r), s ^ k * Dt (z, s) / F (z, s)) z :=
      analyticAt_const.mul (hint z hz)
    refine h1.congr (Filter.eventually_of_mem (hUo.mem_nhds hz) fun w hw => ?_)
    beta_reduce
    rw [← (hZu w hw).2.2.2.2 (fun a => a ^ k) (differentiable_pow k).differentiableOn]
    congr 1
    refine circleIntegral.integral_congr hr.le fun s hs => ?_
    simp only [hderiv w s ((hUgood w hw).1 s (sphere_subset_closedBall hs))]

  have hZ0 : ∀ a ∈ Z 0, a = 0 := by
    intro a ha
    have h := hZu 0 hU0
    by_contra hne0
    have haB : a ∈ closedBall (0 : ℂ) r := ball_subset_closedBall (h.1 a ha)
    have hFa := h.2.2.2.1 a ((hUgood 0 hU0).1 a haB)
    have hz : F (0, a) = 0 := by
      rw [hFa, Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨a, ha, sub_self a⟩), zero_mul]
    exact (hball a (hrb haB)).1 hne0 (by rw [← hFapply]; exact hz)
  have hcard0 : Multiset.card (Z 0) = d := by
    have h := hZu 0 hU0
    have h0B : (0 : ℂ) ∈ closedBall (0 : ℂ) r := mem_closedBall_self hr.le
    have hmem : {s : ℂ | ((0 : σ → ℂ), s) ∈ O1} ∈ 𝓝 (0 : ℂ) := (hslice 0).mem_nhds ((hUgood 0 hU0).1 0 h0B)
    have hrep : Z 0 = Multiset.replicate (Multiset.card (Z 0)) 0 := Multiset.eq_replicate.2 ⟨rfl, hZ0⟩
    have hord' : analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = (Multiset.card (Z 0) : ℕ) := by
      refine hg0.analyticOrderAt_eq_natCast.2 ⟨u 0, h.2.1.analyticAt hmem, h.2.2.1 0 h0B, ?_⟩
      filter_upwards [hmem] with s hs
      rw [← hFapply, h.2.2.2.1 s hs]
      conv_lhs => rw [hrep]
      simp
    rw [hord] at hord'
    exact_mod_cast hord'.symm

  have hcont : ContinuousAt (fun z => (Multiset.card (Z z) : ℂ)) 0 := by
    have := (hps 0 0 hU0).continuousAt
    simpa using this
  have hevd : ∀ᶠ z in 𝓝 (0 : σ → ℂ), Multiset.card (Z z) = d := by
    filter_upwards [hcont.eventually (Metric.ball_mem_nhds ((Multiset.card (Z 0) : ℂ)) one_pos)] with z hz
    rw [dist_eq_norm, hcard0] at hz
    exact natCast_eq_of_norm_sub_lt_one hz
  obtain ⟨U2, hU2, hU2o, hU20⟩ := _root_.eventually_nhds_iff.1 (hevd.and (hUo.mem_nhds hU0))

  have hes : ∀ k, AnalyticOnNhd ℂ (fun z => (Z z).esymm k) U2 :=
    hN σ U2 d Z hU2o (fun z hz => (hU2 z hz).1) fun k _ _ => (hps k).mono fun z hz => (hU2 z hz).2
  set c : Fin d → (σ → ℂ) → ℂ := fun j z => (-1) ^ (d - (j : ℕ)) * (Z z).esymm (d - (j : ℕ)) with hcdef
  have hcan : ∀ j, AnalyticOnNhd ℂ (c j) U2 := fun j => analyticOnNhd_const.mul (hes _)
  have hc0 : ∀ j, c j 0 = 0 := by
    intro j
    have hrep : Z 0 = Multiset.replicate d 0 := Multiset.eq_replicate.2 ⟨hcard0, hZ0⟩
    simp only [hcdef, hrep, esymm_replicate_zero (show 1 ≤ d - (j : ℕ) by omega), mul_zero]

  set W : (σ → ℂ) × ℂ → ℂ := fun p => p.2 ^ d + ∑ j, c j p.1 * p.2 ^ (j : ℕ) with hWdef
  have hWprod : ∀ z ∈ U2, ∀ s, W (z, s) = ((Z z).map fun a => s - a).prod := fun z hz s =>
    weierstrassPolynomial_eq_prod c z (Z z) (hU2 z hz).1 (fun j => rfl) s
  have hWd : DifferentiableOn ℂ W (Prod.fst ⁻¹' U2) := by
    have h1 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d) (Prod.fst ⁻¹' U2) := differentiableOn_snd.pow d
    have h2 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => ∑ j, c j p.1 * p.2 ^ (j : ℕ)) (Prod.fst ⁻¹' U2) :=
      DifferentiableOn.fun_sum fun j _ => by
        have hc1 : DifferentiableOn ℂ (fun p : (σ → ℂ) × ℂ => c j p.1) (Prod.fst ⁻¹' U2) :=
          (hcan j).differentiableOn.comp differentiableOn_fst fun p hp => hp
        exact hc1.mul (differentiableOn_snd.pow _)
    exact h1.add h2

  set P : (Option σ → ℂ) →L[ℂ] (σ → ℂ) := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (some i)
    with hPdef
  set q : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => (P p.1, p.2) with hqdef
  have hqc : Continuous q := (P.continuous.comp continuous_fst).prodMk continuous_snd
  have hqd : Differentiable ℂ q :=
    (P.differentiable.comp differentiable_fst).prodMk differentiable_snd
  set A : Set ((Option σ → ℂ) × ℂ) := q ⁻¹' (O1 ∩ Prod.fst ⁻¹' U2) with hAdef
  have hAo : IsOpen A := (hO1.inter (hU2o.preimage continuous_fst)).preimage hqc
  set G : (Option σ → ℂ) × ℂ → ℂ := fun p => W (q p) * (p.2 - p.1 none) with hGdef
  have hGd : DifferentiableOn ℂ G A := by
    have hlast : DifferentiableOn ℂ (fun p : (Option σ → ℂ) × ℂ => p.2 - p.1 none) A :=
      differentiableOn_snd.sub ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Option σ => ℂ) none).comp
        (ContinuousLinearMap.fst ℂ (Option σ → ℂ) ℂ)).differentiableOn
    exact (hWd.comp hqd.differentiableOn fun p (hp : p ∈ A) => hp.2).mul hlast
  set O3 : Set ((Option σ → ℂ) × ℂ) := A ∩ G ⁻¹' {0}ᶜ with hO3def
  have hO3 : IsOpen O3 := hGd.continuousOn.isOpen_inter_preimage hAo isOpen_compl_singleton
  set Φe : (Option σ → ℂ) × ℂ → ℂ := fun p => F (q p) / G p with hΦedef
  have hΦe : DifferentiableOn ℂ Φe O3 := by
    simp only [hΦedef, div_eq_mul_inv]
    exact (hFd.comp hqd.differentiableOn fun p (hp : p ∈ O3) => hp.1.1).mul
      ((hGd.mono Set.inter_subset_left).inv fun p (hp : p ∈ O3) => hp.2)
  set U3 : Set (Option σ → ℂ) := P ⁻¹' U2 ∩ {x | ‖x none‖ < r} with hU3def
  have hU3o : IsOpen U3 :=
    (hU2o.preimage P.continuous).inter (isOpen_lt (continuous_norm.comp (continuous_apply none)) continuous_const)
  have hmem3 : ∀ x ∈ U3, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ O3 := by
    intro x hx s hs
    have hzU := (hU2 (P x) hx.1).2
    refine ⟨⟨(hUgood _ hzU).1 s (sphere_subset_closedBall hs), hx.1⟩, ?_⟩
    have hsn : ‖s‖ = r := by simpa using hs
    have hxn : ‖x none‖ < r := hx.2
    rw [Set.mem_preimage, Set.mem_compl_singleton_iff]
    refine mul_ne_zero ?_ ?_
    · show W (P x, s) ≠ 0
      rw [hWprod _ hx.1]
      refine Multiset.prod_ne_zero fun h0 => ?_
      obtain ⟨a, ha, has⟩ := Multiset.mem_map.1 h0
      have hab := mem_ball_zero_iff.1 ((hZu _ hzU).1 a ha)
      rw [sub_eq_zero] at has
      rw [← has] at hab
      linarith
    · intro h0
      have h0' : s = x none := sub_eq_zero.1 h0
      rw [← h0'] at hxn
      linarith
  have hint3 := hC (Option σ) Φe O3 U3 0 r hr.le hO3 hU3o hΦe hmem3
  set e : (Option σ → ℂ) → ℂ := fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φe (x, s) with hedef

  have he_eq : ∀ x ∈ U3, e x = u (P x) (x none) := by
    intro x hx
    have hzU := (hU2 (P x) hx.1).2
    have h := hZu (P x) hzU
    have hw : x none ∈ ball (0 : ℂ) r := mem_ball_zero_iff.2 hx.2
    have hcl : ∀ s ∈ closedBall (0 : ℂ) r, (P x, s) ∈ O1 := (hUgood _ hzU).1
    have hcauchy := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      Set.countable_empty hw (h.2.1.continuousOn.mono hcl)
      fun s hs => h.2.1.differentiableAt ((hslice _).mem_nhds (hcl s (ball_subset_closedBall hs.1)))
    rw [← hcauchy, smul_eq_mul]
    show (2 * π * I)⁻¹ * _ = _
    congr 1
    refine circleIntegral.integral_congr hr.le fun s hs => ?_
    have hsO := hcl s (sphere_subset_closedBall hs)
    have hG := (hmem3 x hx s hs).2
    have hG' : G (x, s) = ((Z (P x)).map fun a => s - a).prod * (s - x none) := by
      show W (P x, s) * (s - x none) = _
      rw [hWprod _ hx.1]
    rw [Set.mem_preimage, Set.mem_compl_singleton_iff, hG'] at hG
    have h1 := left_ne_zero_of_mul hG
    simp only [hΦedef, smul_eq_mul]
    rw [show F (q (x, s)) = F (P x, s) from rfl, h.2.2.2.1 s hsO, hG', mul_div_mul_left _ _ h1,
      div_eq_mul_inv, mul_comm]
  have hU30 : (0 : Option σ → ℂ) ∈ U3 := by
    refine ⟨?_, ?_⟩
    · show P 0 ∈ U2
      rw [map_zero]; exact hU20
    · show ‖(0 : Option σ → ℂ) none‖ < r
      simpa using hr
  refine ⟨e, c, analyticAt_const.mul (hint3 0 hU30), ?_, fun j => hcan j 0 hU20, hc0, ?_⟩
  · rw [he_eq 0 hU30, map_zero, Pi.zero_apply]
    exact (hZu 0 hU0).2.2.1 0 (mem_closedBall_self hr.le)
  · filter_upwards [hU3o.mem_nhds hU30] with x hx
    have hzU := (hU2 (P x) hx.1).2
    rw [he_eq x hx]
    have hx' : f x = F (P x, x none) := by
      rw [hFapply]; exact (congrArg f (pointWithLast_coords x)).symm
    have hxO : x none ∈ {s | (P x, s) ∈ O1} :=
      (hUgood _ hzU).1 _ (ball_subset_closedBall (mem_ball_zero_iff.2 hx.2))
    rw [hx', (hZu _ hzU).2.2.2.1 _ hxO, ← hWprod _ hx.1, mul_comm]
    rfl

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
