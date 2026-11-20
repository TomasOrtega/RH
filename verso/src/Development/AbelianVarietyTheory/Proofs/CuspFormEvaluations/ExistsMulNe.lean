import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NmatZeroMemBor
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIndepForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormQuotientThetaFlatAttainsSupOffCommonZerosStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.QuotientNoPositiveMaxOffCommonZerosStatement

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix
open Filter Asymptotics

namespace GlobalTheory.UpperModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Establish `hd : ∀ τ i, dmin X.Gm x τ i ≠ 0` using `fun τ i h => by`. Use `(hx τ).2 i` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`. Use `mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)` and prove the remaining obligations.

Conclude with `Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _`.
-/
theorem pnorm_pos (X : Data E r) (la : Wt X.Ψ r) {P : Frame X.Ψ r → ℂ} {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i h => by
    have := (hx τ).2 i
    rw [h] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

/- English proof (translation)
Use `⟨⟨DifferentiableOn.fun_sum fun q _ => (hf q).1.1.const_mul _, fun x hx b hb => ?_, fun γ hγ x hx => ?_⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.1 x hx b hb]; ring`. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.2 γ hγ x hx]; ring`.

Use `choose C hC using fun q => (hf q).2`. Use `⟨∑ q, ‖u q‖ * C q, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hN : 0 ≤ ∏ τ, ∏ i : Fin r, ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun q _ => by rw [norm_mul, mul_assoc]; rfl`. Use `_ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hC q x hx) (norm_nonneg _)`.
-/
theorem isBddSec_sum (X : Data E r) {la : Wt X.Ψ r} {m : ℕ} {f : Fin m → Frame X.Ψ r → ℂ}
    (hf : ∀ q, X.IsBddSec la (f q)) (u : Fin m → ℂ) : X.IsBddSec la fun x => ∑ q, u q * f q x := by
  refine ⟨⟨DifferentiableOn.fun_sum fun q _ => (hf q).1.1.const_mul _, fun x hx b hb => ?_,
    fun γ hγ x hx => ?_⟩, ?_⟩
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.1 x hx b hb]; ring
  · simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [(hf q).1.2.2 γ hγ x hx]; ring
  · choose C hC using fun q => (hf q).2
    refine ⟨∑ q, ‖u q‖ * C q, fun x hx => ?_⟩
    have hN : 0 ≤ ∏ τ, ∏ i : Fin r,
        ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ ^ (-(la τ i : ℝ) / 2) := by positivity
    calc X.pnorm la (fun x => ∑ q, u q * f q x) x
        ≤ (∑ q, ‖u q * f q x‖) * _ := mul_le_mul_of_nonneg_right (norm_sum_le _ _) hN
      _ = ∑ q, ‖u q‖ * X.pnorm la (f q) x := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun q _ => by rw [norm_mul, mul_assoc]; rfl
      _ ≤ _ := Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (hC q x hx) (norm_nonneg _)

/- English proof (translation)
The claim follows from `(Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, LeadJets.nmat_zero_mem_Bor X, by rw [LeadJets.rmul_nmat_zero, LeadJets.lact_one]⟩ k`.
-/
theorem s_xs {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) (k : Fin (nd X)) :
    Fl.s k (Fl.xs j) = 0 :=
  (Fl.S_eq _ (Fl.xs_mem j)).2 ⟨j, 1, one_mem _, nmat X 0, LeadJets.nmat_zero_mem_Bor X, by
      rw [LeadJets.rmul_nmat_zero, LeadJets.lact_one]⟩ k

/- English proof (translation)
Use `show cpt X x 0 ∈ X.dom`. Rewrite using `[LeadJets.cpt_zero]`. Conclude with `hx`.
-/
theorem zero_mem_OmF {X : Data E r} {x : Frame X.Ψ r} (hx : x ∈ X.dom) : (0 : V (nd X)) ∈ OmF X x := by
  show cpt X x 0 ∈ X.dom
  rw [LeadJets.cpt_zero]; exact hx

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨x, hx, -⟩` from `Xa.et_ne`. Take `⟨j, -⟩` from `(Fl.S_eq x hx).1 fun k => h k x hx`. Apply `Fl.coord j` to reduce the goal to its premises.

Establish `hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0` using `by filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds (zero_mem_OmF (Fl.xs_mem j))] with z hz`. Use extensionality with `k`. Simplify using `[h k _ hz]`. Rewrite using `[hev.fderiv_eq, fderiv_const_apply]`. Establish `hn` using `Xa.n_ge`.

Use `haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩`. Use `LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis` as an intermediate fact. Simplify `this` using `[ContinuousLinearMap.det]`.
-/
theorem exists_s_ne {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, -⟩ := Xa.et_ne
  obtain ⟨j, -⟩ := (Fl.S_eq x hx).1 fun k => h k x hx
  apply Fl.coord j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(OntoB.isOpen_OmF X (Fl.xs j)).mem_nhds (zero_mem_OmF (Fl.xs_mem j))] with z hz
    ext k
    simp [h k _ hz]
  rw [hev.fderiv_eq, fderiv_const_apply]
  have hn := Xa.n_ge
  haveI : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  have := LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis
  simpa [ContinuousLinearMap.det] using this

/- English proof (translation)
Establish `hj` using `fun q => LeadJets.jets (T := e) (a0 := e + 1) (U := fun j => OmF X (Fl.xs j)) (f := fun j z => f q (cpt X (Fl.xs j) z)) (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z)) (t := fun j _ k => if k = j then 1 else 0) le_rfl (fun j => OntoB.isO …`. Use `choose cc hcc using hj`. Set `v : Fin m → (Fin Fl.δ × multiLt (nd X) (e + 1) → ℂ)` to `fun q p => cc q p.2.1 p.1`. Establish `hdep : ¬ LinearIndependent ℂ v` using `fun h => by`. Use `h.fintype_card_le_finrank` as an intermediate fact.

Rewrite `this` using `[Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, ManyForms.card_multiLt_succ]`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu, i, hi⟩` from `Fintype.not_linearIndependent_iff.mp hdep`. Establish `hu' : ∀ α ∈ multiLt (nd X) (e + 1), ∀ k, ∑ q, u q * cc q α k = 0` using `fun α hα k => by`. Simplify `congrFun hu (k, ⟨α, hα⟩)` using `[v]`.

Use `⟨u, fun h => hi (by simp [h]), fun j => ?_⟩` and prove the remaining obligations. Establish `hz : ∀ (s : Fin (nd X) → ℂ) (w : ℂ) (t : Fin Fl.δ → ℂ), ∑ q, u q * LeadJets.leadVal s w t e (e + 1) (cc q) = 0` using `fun s w t => by`. Unfold `LeadJets.leadVal`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun α hα => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Simplify using `only [← mul_assoc, ← Finset.sum_mul, hu' α hα k, zero_mul]`. Establish `hsum` using `IsBigO.sum (s := Finset.univ) fun q _ => (hcc q j).const_mul_left (u q)`.

Use `hsum.congr_left fun z => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, hz, sub_zero]`.
-/
theorem exists_comb {X : Data E r} {Xa : ArchInM X} (Fl : FlatM X Xa) (e m : ℕ)
    (f : Fin m → Frame X.Ψ r → ℂ) (hf : ∀ q, DifferentiableOn ℂ (f q) X.dom)
    (hm : Fl.δ * (e + nd X).choose (nd X) < m) :
    ∃ u : Fin m → ℂ, u ≠ 0 ∧ ∀ j, (fun z : V (nd X) => ∑ q, u q * f q (cpt X (Fl.xs j) z))
      =O[𝓝 0] fun z => ‖z‖ ^ (e + 1) := by
  classical
  have hj := fun q => LeadJets.jets (T := e) (a0 := e + 1) (U := fun j => OmF X (Fl.xs j))
    (f := fun j z => f q (cpt X (Fl.xs j) z))
    (w := fun j z => Fl.w0 (cpt X (Fl.xs j) z)) (s := fun j z k => Fl.s k (cpt X (Fl.xs j) z))
    (t := fun j _ k => if k = j then 1 else 0) le_rfl
    (fun j => OntoB.isOpen_OmF X _)
    (fun j => zero_mem_OmF (Fl.xs_mem j))
    (fun j => OntoB.hol_comp X _ (hf q))
    (fun j => OntoB.hol_comp X _ Fl.weightForm_vanishes.1.1.1.1)
    (fun j k => OntoB.hol_comp X _ (Fl.s_van k).1.1.1.1)
    (fun j k => differentiableOn_const _)
    (fun j => by simpa only [LeadJets.cpt_zero] using Fl.w0_ne j)
    (fun j k => by simpa only [LeadJets.cpt_zero] using s_xs Fl j k)
    Fl.coord
    (fun v => ⟨v, fun j => by simp⟩)
  choose cc hcc using hj
  let v : Fin m → (Fin Fl.δ × multiLt (nd X) (e + 1) → ℂ) := fun q p => cc q p.2.1 p.1
  have hdep : ¬ LinearIndependent ℂ v := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe, ManyForms.card_multiLt_succ] at this
    omega
  obtain ⟨u, hu, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
  have hu' : ∀ α ∈ multiLt (nd X) (e + 1), ∀ k, ∑ q, u q * cc q α k = 0 := fun α hα k => by
    simpa [v] using congrFun hu (k, ⟨α, hα⟩)
  refine ⟨u, fun h => hi (by simp [h]), fun j => ?_⟩
  have hz : ∀ (s : Fin (nd X) → ℂ) (w : ℂ) (t : Fin Fl.δ → ℂ),
      ∑ q, u q * LeadJets.leadVal s w t e (e + 1) (cc q) = 0 := fun s w t => by
    unfold LeadJets.leadVal
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun α hα => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hu' α hα k, zero_mul]
  have hsum := IsBigO.sum (s := Finset.univ) fun q _ => (hcc q j).const_mul_left (u q)
  refine hsum.congr_left fun z => ?_
  simp only [Finset.sum_apply, mul_sub, Finset.sum_sub_distrib, hz, sub_zero]

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨x, hx, hfx⟩` from `hf0`. Take `⟨y, hy, hgy⟩` from `hg0`. Conclude with `hgy (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X) (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hf hg h hx hfx y hy)`.
-/
theorem exists_mul_ne {X : Data E r} {f g : Frame X.Ψ r → ℂ} (hf : DifferentiableOn ℂ f X.dom)
    (hg : DifferentiableOn ℂ g X.dom) (hf0 : ∃ x ∈ X.dom, f x ≠ 0) (hg0 : ∃ x ∈ X.dom, g x ≠ 0) :
    ∃ x ∈ X.dom, f x * g x ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨x, hx, hfx⟩ := hf0
  obtain ⟨y, hy, hgy⟩ := hg0
  exact hgy (ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom X)
    (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected r X).isPreconnected hf hg h hx hfx y hy)

/- English proof (translation)
Introduce `E _ _ _ r X Xa Fl m f hf hind`. Assume the negation of the conclusion as `hm`. Take `⟨u, hu, hO⟩` from `exists_comb Fl (Xa.T + nd X + 6) m f (fun q => (hf q).1.1) (by`. Rewrite using `[show Xa.T + nd X + 6 + nd X = Xa.T + 2 * nd X + 6 by ring]; omega)`. Establish `hg` using `isBddSec_sum X hf u`.

Establish `hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hu (hind u h)`. Take `⟨k, hk⟩` from `exists_s_ne Fl`.

Establish `d1` using `hg.1.1`. Establish `d2` using `Xa.secondTheta_vanishes.1.1.1.1`. Establish `d3` using `Xa.firstTheta_vanishes.1.1.1.1`. Establish `d4` using `Xa.et_sec.1`. Establish `d5` using `(Fl.s_van k).1.1.1.1`.

Take `⟨x, hx, hne⟩` from `exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5 (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3 (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk`. Simplify using `only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne`. Take `⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩` from `hne`. Take `⟨x0, hx0, hs0, hpos, hmax⟩` from `GlobalTheory.T.normQuotientThetaFlat_attains_sup_off_common_zeros E r X Xa Fl _ hg hO ⟨x, hx, by`. Establish `p1` using `pnorm_pos X (Xa.Fp + Xa.T • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1`.

Establish `p2` using `pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2`. Establish `p3` using `pnorm_pos X (2 • Xa.L - Xa.de) hx h3`. Establish `p4` using `pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4`. Establish `p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2` using `Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩`. Use the proof step `positivity⟩`.

Conclude with `GlobalTheory.T.quotient_no_positive_max_off_common_zeros E r X Xa Fl _ hg.1 x0 hx0 hs0 hpos hmax`.
-/
theorem upper : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (m : ℕ) (f : Fin m → Frame X.Ψ r → ℂ), (∀ q, X.IsBddSec (Xa.Fp + Xa.T • Xa.L) (f q)) → (∀ u : Fin m → ℂ, (∀ x ∈ X.dom, ∑ q, u q * f q x = 0) → u = 0) → m ≤ Fl.δ * (Xa.T + 2 * nd X + 6).choose (nd X) := by
  intro E _ _ _ r X Xa Fl m f hf hind
  by_contra hm
  obtain ⟨u, hu, hO⟩ := exists_comb Fl (Xa.T + nd X + 6) m f (fun q => (hf q).1.1) (by
    rw [show Xa.T + nd X + 6 + nd X = Xa.T + 2 * nd X + 6 by ring]; omega)
  have hg := isBddSec_sum X hf u
  have hg0 : ∃ x ∈ X.dom, ∑ q, u q * f q x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu (hind u h)
  obtain ⟨k, hk⟩ := exists_s_ne Fl
  have d1 := hg.1.1
  have d2 := Xa.secondTheta_vanishes.1.1.1.1
  have d3 := Xa.firstTheta_vanishes.1.1.1.1
  have d4 := Xa.et_sec.1
  have d5 := (Fl.s_van k).1.1.1.1
  obtain ⟨x, hx, hne⟩ := exists_mul_ne (((d1.mul d2).mul d3).mul d4) d5
    (exists_mul_ne ((d1.mul d2).mul d3) d4 (exists_mul_ne (d1.mul d2) d3
      (exists_mul_ne d1 d2 hg0 Xa.secondTheta_ne_zero) Xa.firstTheta_ne_zero) Xa.et_ne) hk
  simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or] at hne
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hne
  obtain ⟨x0, hx0, hs0, hpos, hmax⟩ := GlobalTheory.T.normQuotientThetaFlat_attains_sup_off_common_zeros E r X Xa Fl _ hg hO ⟨x, hx, by
    have p1 := pnorm_pos X (Xa.Fp + Xa.T • Xa.L) (P := fun x => ∑ q, u q * f q x) hx h1
    have p2 := pnorm_pos X ((nd X + 4) • Xa.L - Xa.Fp) hx h2
    have p3 := pnorm_pos X (2 • Xa.L - Xa.de) hx h3
    have p4 := pnorm_pos X ((Xa.i * (Xa.g0 / 2)) • Xa.de) hx h4
    have p5 : 0 < ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨k, Finset.mem_univ _, pow_pos (pnorm_pos X _ hx h5) 2⟩
    positivity⟩
  exact GlobalTheory.T.quotient_no_positive_max_off_common_zeros E r X Xa Fl _ hg.1 x0 hx0 hs0 hpos hmax

end GlobalTheory.UpperModel
