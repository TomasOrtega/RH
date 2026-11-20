import Mathlib
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ContinuousOnPot
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_boundary

def locMono {X : Type} {n nb : ℕ} (ψ : X → Fin n → ℂ) (σ : Fin nb → Option (Fin n)) (y : X) : ℂ :=
  ∏ k, (match σ k with
    | some i => ψ y i
    | none => 1)

open Filter Topology

/- English proof (translation)
Unfold `locMono`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `k _`. Consider the cases of `σ k with`. Consider the case `none => exact one_ne_zero`.

Consider the case `some i => exact h i`.
-/
theorem locMono_ne {X : Type} {n nb : ℕ} (ψ : X → Fin n → ℂ) (σ : Fin nb → Option (Fin n)) {y : X}
    (h : ∀ i, ψ y i ≠ 0) : locMono ψ σ y ≠ 0 := by
  unfold locMono
  rw [Finset.prod_ne_zero_iff]
  intro k _
  cases σ k with
  | none => exact one_ne_zero
  | some i => exact h i

/- English proof (translation)
Unfold `locMono`. Use `holoOn_prod A Finset.univ (f := fun k y => match σ k with` and prove the remaining obligations. Consider the case `some i => ψ y i`. Consider the case `none => 1) fun k _ => ?_`. Consider the cases of `σ k with`.

Consider the case `none => exact holoOn_const A _ 1`. Consider the case `some i => exact holoOn_coord A hψ i`.
-/
theorem holoOn_locMono {e nb : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (σ : Fin nb → Option (Fin e)) :
    A.HoloOn ψ.source (locMono ψ σ) := by
  unfold locMono
  refine holoOn_prod A Finset.univ (f := fun k y => match σ k with
    | some i => ψ y i
    | none => 1) fun k _ => ?_
  cases σ k with
  | none => exact holoOn_const A _ 1
  | some i => exact holoOn_coord A hψ i

/- English proof (translation)
Introduce `j`. Use `⟨(hψ j).1.mono ?_, (hψ j).2.mono ?_⟩` and prove the remaining obligations. Introduce and unpack `u ⟨hu1, hu2⟩`. Conclude with `⟨hu1, hu2.1⟩`. Introduce and unpack `u ⟨hu1, hu2⟩`.

Conclude with `⟨hu1.1, hu2⟩`.
-/
private theorem lift_map_comp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) (V : Set X) (hV : IsOpen V) :
    IsCompatChart A (ψ.restrOpen V hV) := by
  intro j
  refine ⟨(hψ j).1.mono ?_, (hψ j).2.mono ?_⟩
  · rintro u ⟨hu1, hu2⟩
    exact ⟨hu1, hu2.1⟩
  · rintro u ⟨hu1, hu2⟩
    exact ⟨hu1.1, hu2⟩

/- English proof (translation)
Establish `hcont : ContinuousOn (fun z => r z / r y) W` using `(holo_continuousOn A hr).div_const _`. Use `⟨W ∩ (fun z => r z / r y) ⁻¹' Complex.slitPlane, hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane, ⟨hy, ?_⟩, Set.inter_subset_left, fun z => Complex.log (r z / r y) + ((Real.log ‖r y‖ : ℝ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Use `show r y / r y ∈ Complex.slitPlane`. Rewrite using `[div_self (hr0 y hy)]`. Conclude with `Complex.one_mem_slitPlane`.

Introduce `j u hu`. Establish `hu' : u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W` using `⟨hu.1, hu.2.1⟩`. Establish `h1 : AnalyticAt ℂ (fun u => r ((A.chart j).symm u) / r y) u` using `(hr j u hu').div_const`. Establish `h2 : AnalyticAt ℂ Complex.log (r ((A.chart j).symm u) / r y)` using `analyticAt_clog hu.2.2`. Establish `h3 : AnalyticAt ℂ (fun u => Complex.log (r ((A.chart j).symm u) / r y)) u` using `AnalyticAt.comp (g := Complex.log) (f := fun u => r ((A.chart j).symm u) / r y) h2 h1`.

Conclude with `h3.add analyticAt_const`. Introduce and unpack `z ⟨hz, -⟩`. Simplify using `only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]`. Rewrite using `[Real.log_div (norm_ne_zero_iff.2 (hr0 z hz)) (norm_ne_zero_iff.2 (hr0 y hy))]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem eq_zero_of_mem_all_maximalIdeal_pow {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    {W : Set X} (hW : IsOpen W) {r : X → ℂ} (hr : A.HoloOn W r) (hr0 : ∀ z ∈ W, r z ≠ 0)
    {y : X} (hy : y ∈ W) :
    ∃ W' : Set X, IsOpen W' ∧ y ∈ W' ∧ W' ⊆ W ∧ ∃ F : X → ℂ, A.HoloOn W' F ∧
      ∀ z ∈ W', (F z).re = Real.log ‖r z‖ := by
  have hcont : ContinuousOn (fun z => r z / r y) W := (holo_continuousOn A hr).div_const _
  refine ⟨W ∩ (fun z => r z / r y) ⁻¹' Complex.slitPlane,
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane, ⟨hy, ?_⟩, Set.inter_subset_left,
    fun z => Complex.log (r z / r y) + ((Real.log ‖r y‖ : ℝ) : ℂ), ?_, ?_⟩
  · show r y / r y ∈ Complex.slitPlane
    rw [div_self (hr0 y hy)]
    exact Complex.one_mem_slitPlane
  · intro j u hu
    have hu' : u ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W := ⟨hu.1, hu.2.1⟩
    have h1 : AnalyticAt ℂ (fun u => r ((A.chart j).symm u) / r y) u := (hr j u hu').div_const
    have h2 : AnalyticAt ℂ Complex.log (r ((A.chart j).symm u) / r y) := analyticAt_clog hu.2.2
    have h3 : AnalyticAt ℂ (fun u => Complex.log (r ((A.chart j).symm u) / r y)) u :=
      AnalyticAt.comp (g := Complex.log) (f := fun u => r ((A.chart j).symm u) / r y) h2 h1
    exact h3.add analyticAt_const
  · rintro z ⟨hz, -⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 (hr0 z hz)) (norm_ne_zero_iff.2 (hr0 y hy))]
    ring

/- English proof (translation)
Use `choose ψ σ hψc hx₀ hsrc hinj hW hBc hdiv hG using hloc`. Use `choose G a v hGh hGz hvh hv0 hGe using hG`. Use `set V : Rb.X → Set Rb.X := fun b => (ψ b).source ∩ v b ⁻¹' {0}ᶜ with hVdef`. Establish `hVo : ∀ b, IsOpen (V b)` using `fun b => (holo_continuousOn _ (hvh b)).isOpen_inter_preimage (ψ b).open_source isOpen_compl_singleton`. Establish `hVs : ∀ b, V b ⊆ (ψ b).source` using `fun b => Set.inter_subset_left`.

Establish `hVU : ∀ b, V b ⊆ Rb.U b` using `fun b => (hVs b).trans (hsrc b)`. Establish `hVv : ∀ b, ∀ y ∈ V b, v b y ≠ 0` using `fun b y hy => hy.2`. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover V hVo (fun x _ => Set.mem_iUnion.2 ⟨x, hx₀ x, hv0 x⟩)`. Establish `hcov : ∀ x, ∃ b ∈ t, x ∈ V b`. Introduce `x`.

Use `ht (Set.mem_univ x)` as an intermediate fact. Simplify using `using this`. Use `choose jb hjt hjV using hcov`. Set `GG : t × Bool → MvPolynomial (Σ k, J k) ℂ` to `fun q => if q.2 then MvPolynomial.map (starRingEnd ℂ) (G q.1) else G q.1`. Set `aa : t × Bool → K → ℕ` to `fun q => a q.1`.

Establish `hGGh : ∀ q, IsMultiHomog (GG q) (aa q)`. Introduce and unpack `⟨j, _ | _⟩`. Conclude with `hGh j`. Conclude with `isMultiHomog_map_conj (hGh j)`. Establish `hGGz : ∀ q, ∀ z ∈ Bc, MvPolynomial.eval z (GG q) = 0`.

Introduce and unpack `⟨j, _ | _⟩ z hz`. Conclude with `hGz j z hz`. Use `show MvPolynomial.eval z (MvPolynomial.map (starRingEnd ℂ) (G j)) = 0`. Rewrite using `[eval_map_conj, hGz j _ (hconj z hz), map_zero]`. Establish `hwex : ∀ b q, ∃ w : Rb.X → ℂ, Rb.A.HoloOn (ψ b).source w ∧ ∀ y ∈ (ψ b).source, MvPolynomial.eval (Rb.lift b y) (GG q) = w y * locMono (ψ b) (σ b) y` using `fun b q => hdiv b (GG q) (aa q) (hGGh q) (hGGz q)`.

Use `choose w hwh hwe using hwex`. Set `Qf : ((Σ k, J k) → ℂ) → ℝ` to `fun z => ∑ q, ‖MvPolynomial.eval z (GG q)‖ ^ 2 / nd (aa q) z`. Establish `hQt : ∀ z (c : K → ℂ), (∀ k, c k ≠ 0) → Qf (fun p => c p.1 * z p) = Qf z`. Introduce `z c hc`. Conclude with `Finset.sum_congr rfl fun q _ => term_smul (hGGh q) hc z`.

Establish `hQsame : ∀ z z', SameOrbit z z' → Qf z = Qf z'`. Introduce and unpack `z z' ⟨c, hc, rfl⟩`. Conclude with `hQt z' c hc`. Establish `hQconj : ∀ z, Qf (fun p => starRingEnd ℂ (z p)) = Qf z`. Introduce `z`.

Simplify using `only [Qf, Fintype.sum_prod_type, Fintype.sum_bool, GG, aa, if_true, if_false, Bool.false_eq_true, nd_conj]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e1 : MvPolynomial.eval (fun p => starRingEnd ℂ (z p)) (MvPolynomial.map (starRingEnd ℂ) (G j)) = starRingEnd ℂ (MvPolynomial.eval z (G j))`. Rewrite using `[eval_map_conj]`. Simplify using `only [starRingEnd_self_apply]`.

Establish `e2 : ‖MvPolynomial.eval (fun p => starRingEnd ℂ (z p)) (G j)‖ = ‖MvPolynomial.eval z (MvPolynomial.map (starRingEnd ℂ) (G j))‖`. Rewrite using `[eval_map_conj, RCLike.norm_conj]`. Rewrite using `[e1, e2, RCLike.norm_conj]`. Expand and normalize the polynomial expressions, which then agree. Set `S : Rb.X → Rb.X → ℝ` to `fun b y => ∑ q, ‖w b q y‖ ^ 2 / nd (aa q) (Rb.lift b y)`.

Establish `hQS : ∀ b, ∀ y ∈ (ψ b).source, Qf (Rb.lift b y) = ‖locMono (ψ b) (σ b) y‖ ^ 2 * S b y`. Introduce `b y hy`. Simplify using `only [Qf, S, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hwe b q y hy, norm_mul, mul_pow]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hnd : ∀ b, ∀ y ∈ Rb.U b, ∀ q, 0 < nd (aa q) (Rb.lift b y)` using `fun b y hy q => nd_pos _ (Rb.mem b y hy).1`. Establish `hliftc : ∀ b, ContinuousOn (Rb.lift b) (Rb.U b)` using `fun b => continuousOn_pi.2 fun p => holo_continuousOn _ (Rb.holo b p)`. Establish `hwv : ∀ b (hb : b ∈ t), ∀ y ∈ (ψ b).source, w b (⟨b, hb⟩, false) y = v b y`. Introduce `b hb`.

Use `eqOn_of_coords_ne (ψ b) (ψ b).open_source subset_rfl (holo_continuousOn _ (hwh b _)) (holo_continuousOn _ (hvh b)) ?_` and prove the remaining obligations. Introduce `y hy hne`. Establish `h1` using `hwe b (⟨b, hb⟩, false) y hy`. Establish `h2` using `hGe b y hy`. Establish `hl` using `locMono_ne (ψ b) (σ b) hne`.

Establish `: GG (⟨b, hb⟩, false) = G b` using `rfl`. Rewrite `h1` using `[this]`. Conclude with `mul_right_cancel₀ hl (h1.symm.trans h2)`. Establish `hSpos : ∀ b (hb : b ∈ t), ∀ y ∈ V b, 0 < S b y`. Introduce `b hb y hy`.

Use `Finset.sum_pos' (fun q _ => div_nonneg (sq_nonneg _) (hnd b y (hVU b hy) q).le) ⟨(⟨b, hb⟩, false), Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[hwv b hb y (hVs b hy)]`. Conclude with `div_pos (pow_pos (norm_pos_iff.2 (hVv b y hy)) 2) (hnd b y (hVU b hy) _)`. Establish `hQc : ∀ b, ContinuousOn (fun y => Qf (Rb.lift b y)) (Rb.U b)`. Introduce `b`.

Use `continuousOn_finset_sum _ fun q _ => ?_` and prove the remaining obligations. Conclude with `ContinuousOn.div (((continuous_norm.comp (MvPolynomial.continuous_eval (GG q))).comp_continuousOn (hliftc b)).pow 2) ((continuous_nd (aa q)).comp_continuousOn (hliftc b)) fun y hy => (hnd b y hy q).ne'`. Establish `hSc : ∀ b, ContinuousOn (S b) (ψ b).source`. Introduce `b`. Use `continuousOn_finset_sum _ fun q _ => ?_` and prove the remaining obligations.

Conclude with `ContinuousOn.div ((continuous_norm.comp_continuousOn (holo_continuousOn _ (hwh b q))).pow 2) ((continuous_nd (aa q)).comp_continuousOn ((hliftc b).mono (hsrc b))) fun y hy => (hnd b y (hsrc b hy) q).ne'`. Set `Nf : Rb.X → ℝ` to `fun p => Qf (Rb.lift (jb p) p)`. Establish `hNf : ∀ p b, p ∈ Rb.U b → Nf p = Qf (Rb.lift b p)` using `fun p b hb => hQsame _ _ (Rb.compat (jb p) b p ⟨hVU _ (hjV p), hb⟩)`. Establish `hNc : Continuous Nf`. Use `continuous_iff_continuousAt.2 fun p => ?_` and prove the remaining obligations.

Establish `hev : (fun y => Qf (Rb.lift (jb p) y)) =ᶠ[𝓝 p] Nf` using `Filter.eventually_of_mem ((hVo (jb p)).mem_nhds (hjV p)) fun y hy => (hNf y (jb p) (hVU _ hy)).symm`. Conclude with `(((hQc (jb p)).mono (hVU _)).continuousAt ((hVo _).mem_nhds (hjV p))).congr hev`. Take `⟨M, hM⟩` from `isCompact_univ.exists_bound_of_continuousOn hNc.continuousOn`. Establish `hNnn : ∀ p, 0 ≤ Nf p` using `fun p => Finset.sum_nonneg fun q _ => div_nonneg (sq_nonneg _) (nd_pos _ (Rb.mem _ _ (hVU _ (hjV p))).1).le`. Use `set c0 : ℝ := Real.log (Real.sqrt M + 1) with hc0`.

Establish `hover : ∀ b b', b ∈ t → b' ∈ t → ∀ y ∈ V b ∩ V b', ∃ O : Set Rb.X, IsOpen O ∧ y ∈ O ∧ O ⊆ V b ∩ V b' ∧ ∃ r : Rb.X → ℂ, Rb.A.HoloOn O r ∧ (∀ z ∈ O, r z ≠ 0) ∧ ∀ z ∈ O, S b' z = ‖r z‖ ^ 2 * S b z`. Introduce `b b' hb hb' y hy`. Take `⟨hmem, -⟩` from `Rb.mem b' y (hVU b' hy.2)`. Use `choose ik hik using hmem`. Use `set O : Set Rb.X := (V b ∩ V b') ∩ ⋂ k, ((V b ∩ V b') ∩ (fun z => Rb.lift b' z ⟨k, ik k⟩) ⁻¹' {0}ᶜ) with hOdef`.

Establish `hOo : IsOpen O` using `((hVo b).inter (hVo b')).inter (isOpen_iInter_of_finite fun k => ContinuousOn.isOpen_inter_preimage ((holo_continuousOn _ (Rb.holo b' ⟨k, ik k⟩)).mono (Set.inter_subset_right.trans (hVU b'))) ((hVo b).inter (hVo b')) isOpen_compl_singleton)`. Establish `hyO : y ∈ O` using `⟨hy, Set.mem_iInter.2 fun k => ⟨hy, hik k⟩⟩`. Establish `hOsub : O ⊆ V b ∩ V b'` using `Set.inter_subset_left`. Establish `hOb : O ⊆ (ψ b).source` using `fun z hz => hVs b (hOsub hz).1`. Establish `hOb' : O ⊆ (ψ b').source` using `fun z hz => hVs b' (hOsub hz).2`.

Establish `hOnz : ∀ z ∈ O, ∀ k, Rb.lift b' z ⟨k, ik k⟩ ≠ 0` using `fun z hz k => (Set.mem_iInter.1 hz.2 k).2`. Set `c : K → Rb.X → ℂ` to `fun k z => Rb.lift b z ⟨k, ik k⟩ / Rb.lift b' z ⟨k, ik k⟩`. Establish `hcorb : ∀ z ∈ O, (∀ k, c k z ≠ 0) ∧ Rb.lift b z = fun p => c p.1 z * Rb.lift b' z p`. Introduce `z hz`. Take `⟨c', hc', he⟩` from `Rb.compat b b' z ⟨hVU b (hOsub hz).1, hVU b' (hOsub hz).2⟩`.

Establish `hcc : ∀ k, c k z = c' k`. Introduce `k`. Use `show Rb.lift b z ⟨k, ik k⟩ / Rb.lift b' z ⟨k, ik k⟩ = c' k`. Rewrite using `[he]`. Conclude with `mul_div_cancel_right₀ _ (hOnz z hz k)`.

Use `⟨fun k => by rw [hcc]; exact hc' k, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Rewrite using `[hcc p.1]`. Use `conv_lhs => rw [he]`. Establish `hch : ∀ k, Rb.A.HoloOn O (c k)` using `fun k => holoOn_div _ (holoOn_mono _ (Rb.holo b _) (fun z hz => hVU b (hOsub hz).1)) (holoOn_mono _ (Rb.holo b' _) (fun z hz => hVU b' (hOsub hz).2)) (hOnz · · k)`.

Establish `hch' : ∀ k, Rb.A.HoloOn O (fun z => 1 / c k z)` using `fun k => holoOn_div _ (holoOn_const _ _ 1) (hch k) (fun z hz => (hcorb z hz).1 k)`. Set `r : Rb.X → ℂ` to `fun z => (∏ k, c k z ^ a b k) * w b' (⟨b, hb⟩, false) z / v b z`. Set `r' : Rb.X → ℂ` to `fun z => (∏ k, (1 / c k z) ^ a b' k) * w b (⟨b', hb'⟩, false) z / v b' z`. Establish `hrh : Rb.A.HoloOn O r` using `holoOn_div _ (holoOn_mul _ (holoOn_prod _ Finset.univ fun k _ => holoOn_pow _ (hch k) _) (holoOn_mono _ (hwh b' _) hOb')) (holoOn_mono _ (hvh b) hOb) (fun z hz => hVv b z (hOsub hz).1)`. Establish `hrh' : Rb.A.HoloOn O r'` using `holoOn_div _ (holoOn_mul _ (holoOn_prod _ Finset.univ fun k _ => holoOn_pow _ (hch' k) _) (holoOn_mono _ (hwh b _) hOb)) (holoOn_mono _ (hvh b') hOb') (fun z hz => hVv b' z (hOsub hz).2)`.

Establish `hlm1 : ∀ z ∈ O, locMono (ψ b) (σ b) z = r z * locMono (ψ b') (σ b') z`. Introduce `z hz`. Establish `e1` using `hGe b z (hOb hz)`. Establish `e2` using `hwe b' (⟨b, hb⟩, false) z (hOb' hz)`. Establish `e3` using `eval_smul_homog (hGh b) (fun k => c k z) (Rb.lift b' z)`.

Establish `hGb : GG (⟨b, hb⟩, false) = G b` using `rfl`. Rewrite `e2` using `[hGb]`. Rewrite `e1` using `[(hcorb z hz).2, e3]`. Establish `hv` using `hVv b z (hOsub hz).1`. Simplify using `only [r]`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff hv]`. Take the linear combination `(-1 : ℂ) * e1 + (∏ k, c k z ^ a b k) * e2`. Establish `hlm2 : ∀ z ∈ O, locMono (ψ b') (σ b') z = r' z * locMono (ψ b) (σ b) z`. Introduce `z hz`. Establish `hl' : Rb.lift b' z = fun p => (1 / c p.1 z) * Rb.lift b z p`.

Use function extensionality and compare the values at `p`. Rewrite using `[(hcorb z hz).2]`. Clear denominators, using `[(hcorb z hz).1 p.1]` for the nonvanishing conditions. Establish `e1` using `hGe b' z (hOb' hz)`. Establish `e2` using `hwe b (⟨b', hb'⟩, false) z (hOb hz)`.

Establish `e3` using `eval_smul_homog (hGh b') (fun k => 1 / c k z) (Rb.lift b z)`. Establish `hGb : GG (⟨b', hb'⟩, false) = G b'` using `rfl`. Rewrite `e2` using `[hGb]`. Rewrite `e1` using `[hl', e3]`. Establish `hv` using `hVv b' z (hOsub hz).2`.

Simplify using `only [r']`. Rewrite using `[div_mul_eq_mul_div, eq_div_iff hv]`. Take the linear combination `(-1 : ℂ) * e1 + (∏ k, (1 / c k z) ^ a b' k) * e2`. Establish `hrr : ∀ z ∈ O, r z * r' z = 1`. Use `eqOn_of_coords_ne (ψ b) hOo hOb ((holo_continuousOn _ hrh).mul (holo_continuousOn _ hrh')) continuousOn_const ?_` and prove the remaining obligations.

Introduce `z hz hne`. Establish `hl` using `locMono_ne (ψ b) (σ b) hne`. Use `mul_right_cancel₀ hl ?_` and prove the remaining obligations. Rewrite using `[one_mul, mul_assoc, ← hlm2 z hz, ← hlm1 z hz]`. Establish `hr0 : ∀ z ∈ O, r z ≠ 0` using `fun z hz => left_ne_zero_of_mul_eq_one (hrr z hz)`.

Use `⟨O, hOo, hyO, hOsub, r, hrh, hr0, ?_⟩` and prove the remaining obligations. Use `eqOn_of_coords_ne (ψ b') hOo hOb' ((hSc b').mono hOb') (((continuous_norm.comp_continuousOn (holo_continuousOn _ hrh)).pow 2).mul ((hSc b).mono hOb)) ?_` and prove the remaining obligations. Introduce `z hz hne`. Establish `hl` using `locMono_ne (ψ b') (σ b') hne`. Establish `hq` using `hQsame _ _ (Rb.compat b b' z ⟨hVU b (hOsub hz).1, hVU b' (hOsub hz).2⟩)`.

Rewrite `hq` using `[hQS b z (hOb hz), hQS b' z (hOb' hz), hlm1 z hz, norm_mul, mul_pow]`. Establish `hl2 : ‖locMono (ψ b') (σ b') z‖ ^ 2 ≠ 0` using `pow_ne_zero _ (norm_ne_zero_iff.2 hl)`. Use `mul_left_cancel₀ hl2 ?_` and prove the remaining obligations. Rewrite using `[← hq]`. Expand and normalize the polynomial expressions, which then agree.

Set `L : LocPot Rb.X` to `{ U := fun x => V (jb x), isOpen_U := fun x => hVo _, mem_U := hjV, φ := fun x y => c0 - 1 / 2 * Real.log (S (jb x) y) }`. Set `s : Rb.X → Rb.X → ℂ` to `fun x y => locMono (ψ (jb x)) (σ (jb x)) y`. Establish `hnorm : ∀ x, ∀ y ∈ V (jb x), ‖s x y‖ * Real.exp (-L.φ x y) = Real.exp (-c0) * Real.sqrt (Qf (Rb.lift (jb x) y))`. Introduce `x y hy`. Establish `hS` using `hSpos (jb x) (hjt x) y hy`.

Rewrite using `[hQS _ y (hVs _ hy), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]`. Establish `he : Real.exp (1 / 2 * Real.log (S (jb x) y)) = Real.sqrt (S (jb x) y)`. Rewrite using `[← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add, show 1 / 2 * Real.log (S (jb x) y) + 1 / 2 * Real.log (S (jb x) y) = Real.log (S (jb x) y) by ring, Real.exp_log hS]`. Use `show ‖s x y‖ * Real.exp (-(c0 - 1 / 2 * Real.log (S (jb x) y))) = _`. Rewrite using `[show -(c0 - 1 / 2 * Real.log (S (jb x) y)) = 1 / 2 * Real.log (S (jb x) y) + -c0 by ring, Real.exp_add, he]`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨L, s, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Conclude with `smoothOn_pot Rb.A (fun q => w (jb x) q) (fun q => holoOn_mono _ (hwh _ q) (hVs _)) (Rb.lift (jb x)) (fun p => holoOn_mono _ (Rb.holo _ p) (hVU _)) aa (fun y hy q => hnd _ y (hVU _ hy) q) (fun y hy => hSpos _ (hjt x) y hy) c0`. Introduce `x x' y hy`.

Take `⟨O, hOo, hyO, hOsub, r, hrh, hr0, hSS⟩` from `hover (jb x) (jb x') (hjt x) (hjt x') y hy`. Take `⟨W', hW'o, hyW', hW'O, F, hF, hFre⟩` from `eq_zero_of_mem_all_maximalIdeal_pow Rb.A hOo hrh hr0 hyO`. Use `⟨W', hW'o, hyW', F, hF, ?_⟩` and prove the remaining obligations. Introduce and unpack `z ⟨⟨hzW, -⟩, -⟩`. Establish `hzO` using `hW'O hzW`.

Use `show (c0 - 1 / 2 * Real.log (S (jb x) z)) - (c0 - 1 / 2 * Real.log (S (jb x') z)) = (F z).re`. Rewrite using `[hFre z hzW, hSS z hzO, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hr0 z hzO))) (hSpos _ (hjt x) z (hOsub hzO).1).ne', Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `x`.

Conclude with `holoOn_mono _ (holoOn_locMono Rb.A (hψc _) (σ _)) (hVs _)`. Introduce and unpack `x x' y ⟨hy, hy'⟩`. Rewrite using `[hnorm x y hy, hnorm x' y hy', hQsame _ _ (Rb.compat (jb x) (jb x') y ⟨hVU _ hy, hVU _ hy'⟩)]`. Introduce `x`. Use `⟨(ψ (jb x)).restrOpen (V (jb x)) (hVo _), lift_map_comp _ (hψc _) _ _, ?_, ?_, σ (jb x), hinj _, ?_, fun _ => 1, holoOn_const _ _ 1, fun _ _ => one_ne_zero, ?_⟩` and prove the remaining obligations.

Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Conclude with `⟨hVs _ (hjV x), hjV x⟩`. Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Conclude with `Set.inter_subset_right`. Introduce `k`.

Rewrite using `[OpenPartialHomeomorph.restrOpen_source]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hyW, hys, hyV⟩`. Establish `h1 : y ∈ W k ∩ (ψ (jb x)).source` using `⟨hyW, hys⟩`.

Rewrite `h1` using `[hW (jb x) k]`. Conclude with `⟨⟨hys, hyV⟩, h1.2⟩`. Introduce and unpack `⟨⟨hys, hyV⟩, hex⟩`. Establish `h1 : y ∈ {y | y ∈ (ψ (jb x)).source ∧ ∃ i, σ (jb x) k = some i ∧ ψ (jb x) y i = 0}` using `⟨hys, hex⟩`. Rewrite `h1` using `[← hW (jb x) k]`.

Conclude with `⟨h1.1, hys, hyV⟩`. Introduce `y hy`. Rewrite using `[one_mul]`. Use `show locMono (ψ (jb x)) (σ (jb x)) y = _`. Unfold `locMono`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Consider the cases of `σ (jb x) k with`. Consider the case `none => rfl`. Consider the case `some i`. Simplify using `only [pow_one]`.

Both sides reduce to the same expression. Introduce `p`. Unfold `logNormSec`. Rewrite using `[hnorm p p (hjV p)]`. Establish `hN` using `hM p (Set.mem_univ p)`.

Rewrite `hN` using `[Real.norm_of_nonneg (hNnn p)]`. Establish `hsq : Real.sqrt (Nf p) ≤ Real.sqrt M` using `Real.sqrt_le_sqrt hN`. Establish `hpos : 0 < Real.sqrt M + 1` using `by positivity`. Apply `Real.log_nonpos (by positivity)` to reduce the goal to its premises. Rewrite using `[hc0, Real.exp_neg, Real.exp_log hpos, inv_mul_le_iff₀ hpos]`.

Use `show Real.sqrt (Nf p) ≤ _`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `p show locMono (ψ (jb p)) (σ (jb p)) p = 0 ↔ Rb.lift p p ∈ Bc`. Rewrite using `[← hBc (jb p) p (hVs _ (hjV p))]`. Take `⟨c, hc, he⟩` from `Rb.compat (jb p) p p ⟨hVU _ (hjV p), Rb.mem_U p⟩`.

Rewrite using `[he]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `htor _ h (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))` as an intermediate fact. Simplify `this` using `[inv_mul_cancel_left₀ (hc _)]`.

Introduce `h`. Conclude with `htor _ h c hc`. Introduce `p p' horb`. Establish `hq : Qf (Rb.lift (jb p') p') = Qf (Rb.lift (jb p) p)`. Rewrite using `[show Qf (Rb.lift (jb p') p') = Qf (Rb.lift p' p') from hNf p' p' (Rb.mem_U p'), hQsame _ _ horb, hQconj, ← show Qf (Rb.lift (jb p) p) = Qf (Rb.lift p p) from hNf p p (Rb.mem_U p)]`.

Simplify using `only [rW, logNormSec]`. Rewrite using `[hnorm p' p' (hjV p'), hnorm p p (hjV p), hq]`.
-/
theorem assemble {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    (Rb : AnLogRes P ⊤ n) (Bc : Set ((Σ k, J k) → ℂ))
    (htor : ∀ z ∈ Bc, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → (fun p : Σ k, J k => c p.1 * z p) ∈ Bc)
    (hconj : ∀ z ∈ Bc, (fun p => starRingEnd ℂ (z p)) ∈ Bc) (nb : ℕ) (W : Fin nb → Set Rb.X)
    (hloc : ∀ x₀ : Rb.X, ∃ (ψ : OpenPartialHomeomorph Rb.X (Fin n → ℂ)) (σ : Fin nb → Option (Fin n)),
      IsCompatChart Rb.A ψ ∧ x₀ ∈ ψ.source ∧ ψ.source ⊆ Rb.U x₀ ∧
      (∀ k k' i, σ k = some i → σ k' = some i → k = k') ∧
      (∀ k, W k ∩ ψ.source = {y ∈ ψ.source | ∃ i, σ k = some i ∧ ψ y i = 0}) ∧
      (∀ y ∈ ψ.source, Rb.lift x₀ y ∈ Bc ↔ locMono ψ σ y = 0) ∧
      (∀ (G : MvPolynomial (Σ k, J k) ℂ) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G a →
        (∀ z ∈ Bc, MvPolynomial.eval z G = 0) →
        ∃ v : Rb.X → ℂ, Rb.A.HoloOn ψ.source v ∧ ∀ y ∈ ψ.source,
          MvPolynomial.eval (Rb.lift x₀ y) G = v y * locMono ψ σ y) ∧
      ∃ (G : MvPolynomial (Σ k, J k) ℂ) (a : K → ℕ) (v : Rb.X → ℂ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G a ∧
        (∀ z ∈ Bc, MvPolynomial.eval z G = 0) ∧ Rb.A.HoloOn ψ.source v ∧ v x₀ ≠ 0 ∧
        ∀ y ∈ ψ.source, MvPolynomial.eval (Rb.lift x₀ y) G = v y * locMono ψ σ y) :
    ∃ (L : LocPot Rb.X) (s : Rb.X → Rb.X → ℂ), IsPotential Rb.A L ∧ IsSection Rb.A L s ∧
      IsSNC Rb.A L s (fun _ => 1) W ∧ (∀ p, logNormSec L s p ≤ 0) ∧ (∀ p, p ∈ bdry s ↔ Rb.lift p p ∈ Bc) ∧
      ∀ p p', SameOrbit (Rb.lift p' p') (fun q => starRingEnd ℂ (Rb.lift p p q)) → rW L s p' = rW L s p := by
  classical
  choose ψ σ hψc hx₀ hsrc hinj hW hBc hdiv hG using hloc
  choose G a v hGh hGz hvh hv0 hGe using hG
  set V : Rb.X → Set Rb.X := fun b => (ψ b).source ∩ v b ⁻¹' {0}ᶜ with hVdef
  have hVo : ∀ b, IsOpen (V b) := fun b =>
    (holo_continuousOn _ (hvh b)).isOpen_inter_preimage (ψ b).open_source isOpen_compl_singleton
  have hVs : ∀ b, V b ⊆ (ψ b).source := fun b => Set.inter_subset_left
  have hVU : ∀ b, V b ⊆ Rb.U b := fun b => (hVs b).trans (hsrc b)
  have hVv : ∀ b, ∀ y ∈ V b, v b y ≠ 0 := fun b y hy => hy.2
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hVo
    (fun x _ => Set.mem_iUnion.2 ⟨x, hx₀ x, hv0 x⟩)
  have hcov : ∀ x, ∃ b ∈ t, x ∈ V b := by
    intro x
    have := ht (Set.mem_univ x)
    simpa using this
  choose jb hjt hjV using hcov
  let GG : t × Bool → MvPolynomial (Σ k, J k) ℂ := fun q =>
    if q.2 then MvPolynomial.map (starRingEnd ℂ) (G q.1) else G q.1
  let aa : t × Bool → K → ℕ := fun q => a q.1
  have hGGh : ∀ q, IsMultiHomog (GG q) (aa q) := by
    rintro ⟨j, _ | _⟩
    · exact hGh j
    · exact isMultiHomog_map_conj (hGh j)
  have hGGz : ∀ q, ∀ z ∈ Bc, MvPolynomial.eval z (GG q) = 0 := by
    rintro ⟨j, _ | _⟩ z hz
    · exact hGz j z hz
    · show MvPolynomial.eval z (MvPolynomial.map (starRingEnd ℂ) (G j)) = 0
      rw [eval_map_conj, hGz j _ (hconj z hz), map_zero]
  have hwex : ∀ b q, ∃ w : Rb.X → ℂ, Rb.A.HoloOn (ψ b).source w ∧ ∀ y ∈ (ψ b).source,
      MvPolynomial.eval (Rb.lift b y) (GG q) = w y * locMono (ψ b) (σ b) y :=
    fun b q => hdiv b (GG q) (aa q) (hGGh q) (hGGz q)
  choose w hwh hwe using hwex
  let Qf : ((Σ k, J k) → ℂ) → ℝ := fun z => ∑ q, ‖MvPolynomial.eval z (GG q)‖ ^ 2 / nd (aa q) z
  have hQt : ∀ z (c : K → ℂ), (∀ k, c k ≠ 0) → Qf (fun p => c p.1 * z p) = Qf z := by
    intro z c hc
    exact Finset.sum_congr rfl fun q _ => term_smul (hGGh q) hc z
  have hQsame : ∀ z z', SameOrbit z z' → Qf z = Qf z' := by
    rintro z z' ⟨c, hc, rfl⟩
    exact hQt z' c hc
  have hQconj : ∀ z, Qf (fun p => starRingEnd ℂ (z p)) = Qf z := by
    intro z
    simp only [Qf, Fintype.sum_prod_type, Fintype.sum_bool, GG, aa, if_true, if_false,
      Bool.false_eq_true, nd_conj]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : MvPolynomial.eval (fun p => starRingEnd ℂ (z p)) (MvPolynomial.map (starRingEnd ℂ) (G j)) =
        starRingEnd ℂ (MvPolynomial.eval z (G j)) := by
      rw [eval_map_conj]
      simp only [starRingEnd_self_apply]
    have e2 : ‖MvPolynomial.eval (fun p => starRingEnd ℂ (z p)) (G j)‖ =
        ‖MvPolynomial.eval z (MvPolynomial.map (starRingEnd ℂ) (G j))‖ := by
      rw [eval_map_conj, RCLike.norm_conj]
    rw [e1, e2, RCLike.norm_conj]
    ring
  let S : Rb.X → Rb.X → ℝ := fun b y => ∑ q, ‖w b q y‖ ^ 2 / nd (aa q) (Rb.lift b y)
  have hQS : ∀ b, ∀ y ∈ (ψ b).source,
      Qf (Rb.lift b y) = ‖locMono (ψ b) (σ b) y‖ ^ 2 * S b y := by
    intro b y hy
    simp only [Qf, S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hwe b q y hy, norm_mul, mul_pow]
    ring
  have hnd : ∀ b, ∀ y ∈ Rb.U b, ∀ q, 0 < nd (aa q) (Rb.lift b y) :=
    fun b y hy q => nd_pos _ (Rb.mem b y hy).1
  have hliftc : ∀ b, ContinuousOn (Rb.lift b) (Rb.U b) :=
    fun b => continuousOn_pi.2 fun p => holo_continuousOn _ (Rb.holo b p)
  have hwv : ∀ b (hb : b ∈ t), ∀ y ∈ (ψ b).source, w b (⟨b, hb⟩, false) y = v b y := by
    intro b hb
    refine eqOn_of_coords_ne (ψ b) (ψ b).open_source subset_rfl (holo_continuousOn _ (hwh b _))
      (holo_continuousOn _ (hvh b)) ?_
    intro y hy hne
    have h1 := hwe b (⟨b, hb⟩, false) y hy
    have h2 := hGe b y hy
    have hl := locMono_ne (ψ b) (σ b) hne
    have : GG (⟨b, hb⟩, false) = G b := rfl
    rw [this] at h1
    exact mul_right_cancel₀ hl (h1.symm.trans h2)
  have hSpos : ∀ b (hb : b ∈ t), ∀ y ∈ V b, 0 < S b y := by
    intro b hb y hy
    refine Finset.sum_pos' (fun q _ => div_nonneg (sq_nonneg _) (hnd b y (hVU b hy) q).le)
      ⟨(⟨b, hb⟩, false), Finset.mem_univ _, ?_⟩
    rw [hwv b hb y (hVs b hy)]
    exact div_pos (pow_pos (norm_pos_iff.2 (hVv b y hy)) 2) (hnd b y (hVU b hy) _)
  have hQc : ∀ b, ContinuousOn (fun y => Qf (Rb.lift b y)) (Rb.U b) := by
    intro b
    refine continuousOn_finset_sum _ fun q _ => ?_
    exact ContinuousOn.div
      (((continuous_norm.comp (MvPolynomial.continuous_eval (GG q))).comp_continuousOn (hliftc b)).pow 2)
      ((continuous_nd (aa q)).comp_continuousOn (hliftc b)) fun y hy => (hnd b y hy q).ne'
  have hSc : ∀ b, ContinuousOn (S b) (ψ b).source := by
    intro b
    refine continuousOn_finset_sum _ fun q _ => ?_
    exact ContinuousOn.div ((continuous_norm.comp_continuousOn (holo_continuousOn _ (hwh b q))).pow 2)
      ((continuous_nd (aa q)).comp_continuousOn ((hliftc b).mono (hsrc b)))
      fun y hy => (hnd b y (hsrc b hy) q).ne'
  let Nf : Rb.X → ℝ := fun p => Qf (Rb.lift (jb p) p)
  have hNf : ∀ p b, p ∈ Rb.U b → Nf p = Qf (Rb.lift b p) := fun p b hb =>
    hQsame _ _ (Rb.compat (jb p) b p ⟨hVU _ (hjV p), hb⟩)
  have hNc : Continuous Nf := by
    refine continuous_iff_continuousAt.2 fun p => ?_
    have hev : (fun y => Qf (Rb.lift (jb p) y)) =ᶠ[𝓝 p] Nf :=
      Filter.eventually_of_mem ((hVo (jb p)).mem_nhds (hjV p)) fun y hy => (hNf y (jb p) (hVU _ hy)).symm
    exact (((hQc (jb p)).mono (hVU _)).continuousAt ((hVo _).mem_nhds (hjV p))).congr hev
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hNc.continuousOn
  have hNnn : ∀ p, 0 ≤ Nf p := fun p =>
    Finset.sum_nonneg fun q _ => div_nonneg (sq_nonneg _) (nd_pos _ (Rb.mem _ _ (hVU _ (hjV p))).1).le
  set c0 : ℝ := Real.log (Real.sqrt M + 1) with hc0
  have hover : ∀ b b', b ∈ t → b' ∈ t → ∀ y ∈ V b ∩ V b', ∃ O : Set Rb.X, IsOpen O ∧ y ∈ O ∧
      O ⊆ V b ∩ V b' ∧ ∃ r : Rb.X → ℂ, Rb.A.HoloOn O r ∧ (∀ z ∈ O, r z ≠ 0) ∧
      ∀ z ∈ O, S b' z = ‖r z‖ ^ 2 * S b z := by
    intro b b' hb hb' y hy
    obtain ⟨hmem, -⟩ := Rb.mem b' y (hVU b' hy.2)
    choose ik hik using hmem
    set O : Set Rb.X := (V b ∩ V b') ∩
      ⋂ k, ((V b ∩ V b') ∩ (fun z => Rb.lift b' z ⟨k, ik k⟩) ⁻¹' {0}ᶜ) with hOdef
    have hOo : IsOpen O := ((hVo b).inter (hVo b')).inter (isOpen_iInter_of_finite fun k =>
      ContinuousOn.isOpen_inter_preimage
        ((holo_continuousOn _ (Rb.holo b' ⟨k, ik k⟩)).mono (Set.inter_subset_right.trans (hVU b')))
        ((hVo b).inter (hVo b')) isOpen_compl_singleton)
    have hyO : y ∈ O := ⟨hy, Set.mem_iInter.2 fun k => ⟨hy, hik k⟩⟩
    have hOsub : O ⊆ V b ∩ V b' := Set.inter_subset_left
    have hOb : O ⊆ (ψ b).source := fun z hz => hVs b (hOsub hz).1
    have hOb' : O ⊆ (ψ b').source := fun z hz => hVs b' (hOsub hz).2
    have hOnz : ∀ z ∈ O, ∀ k, Rb.lift b' z ⟨k, ik k⟩ ≠ 0 := fun z hz k => (Set.mem_iInter.1 hz.2 k).2
    let c : K → Rb.X → ℂ := fun k z => Rb.lift b z ⟨k, ik k⟩ / Rb.lift b' z ⟨k, ik k⟩
    have hcorb : ∀ z ∈ O, (∀ k, c k z ≠ 0) ∧ Rb.lift b z = fun p => c p.1 z * Rb.lift b' z p := by
      intro z hz
      obtain ⟨c', hc', he⟩ := Rb.compat b b' z ⟨hVU b (hOsub hz).1, hVU b' (hOsub hz).2⟩
      have hcc : ∀ k, c k z = c' k := by
        intro k
        show Rb.lift b z ⟨k, ik k⟩ / Rb.lift b' z ⟨k, ik k⟩ = c' k
        rw [he]
        exact mul_div_cancel_right₀ _ (hOnz z hz k)
      refine ⟨fun k => by rw [hcc]; exact hc' k, ?_⟩
      funext p
      rw [hcc p.1]
      conv_lhs => rw [he]
    have hch : ∀ k, Rb.A.HoloOn O (c k) := fun k =>
      holoOn_div _ (holoOn_mono _ (Rb.holo b _) (fun z hz => hVU b (hOsub hz).1))
        (holoOn_mono _ (Rb.holo b' _) (fun z hz => hVU b' (hOsub hz).2)) (hOnz · · k)
    have hch' : ∀ k, Rb.A.HoloOn O (fun z => 1 / c k z) := fun k =>
      holoOn_div _ (holoOn_const _ _ 1) (hch k) (fun z hz => (hcorb z hz).1 k)
    let r : Rb.X → ℂ := fun z => (∏ k, c k z ^ a b k) * w b' (⟨b, hb⟩, false) z / v b z
    let r' : Rb.X → ℂ := fun z => (∏ k, (1 / c k z) ^ a b' k) * w b (⟨b', hb'⟩, false) z / v b' z
    have hrh : Rb.A.HoloOn O r :=
      holoOn_div _ (holoOn_mul _ (holoOn_prod _ Finset.univ fun k _ => holoOn_pow _ (hch k) _)
        (holoOn_mono _ (hwh b' _) hOb')) (holoOn_mono _ (hvh b) hOb) (fun z hz => hVv b z (hOsub hz).1)
    have hrh' : Rb.A.HoloOn O r' :=
      holoOn_div _ (holoOn_mul _ (holoOn_prod _ Finset.univ fun k _ => holoOn_pow _ (hch' k) _)
        (holoOn_mono _ (hwh b _) hOb)) (holoOn_mono _ (hvh b') hOb') (fun z hz => hVv b' z (hOsub hz).2)
    have hlm1 : ∀ z ∈ O, locMono (ψ b) (σ b) z = r z * locMono (ψ b') (σ b') z := by
      intro z hz
      have e1 := hGe b z (hOb hz)
      have e2 := hwe b' (⟨b, hb⟩, false) z (hOb' hz)
      have e3 := eval_smul_homog (hGh b) (fun k => c k z) (Rb.lift b' z)
      have hGb : GG (⟨b, hb⟩, false) = G b := rfl
      rw [hGb] at e2
      rw [(hcorb z hz).2, e3] at e1
      have hv := hVv b z (hOsub hz).1
      simp only [r]
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : ℂ) * e1 + (∏ k, c k z ^ a b k) * e2
    have hlm2 : ∀ z ∈ O, locMono (ψ b') (σ b') z = r' z * locMono (ψ b) (σ b) z := by
      intro z hz
      have hl' : Rb.lift b' z = fun p => (1 / c p.1 z) * Rb.lift b z p := by
        funext p
        rw [(hcorb z hz).2]
        field_simp [(hcorb z hz).1 p.1]
      have e1 := hGe b' z (hOb' hz)
      have e2 := hwe b (⟨b', hb'⟩, false) z (hOb hz)
      have e3 := eval_smul_homog (hGh b') (fun k => 1 / c k z) (Rb.lift b z)
      have hGb : GG (⟨b', hb'⟩, false) = G b' := rfl
      rw [hGb] at e2
      rw [hl', e3] at e1
      have hv := hVv b' z (hOsub hz).2
      simp only [r']
      rw [div_mul_eq_mul_div, eq_div_iff hv]
      linear_combination (-1 : ℂ) * e1 + (∏ k, (1 / c k z) ^ a b' k) * e2
    have hrr : ∀ z ∈ O, r z * r' z = 1 := by
      refine eqOn_of_coords_ne (ψ b) hOo hOb ((holo_continuousOn _ hrh).mul (holo_continuousOn _ hrh'))
        continuousOn_const ?_
      intro z hz hne
      have hl := locMono_ne (ψ b) (σ b) hne
      refine mul_right_cancel₀ hl ?_
      rw [one_mul, mul_assoc, ← hlm2 z hz, ← hlm1 z hz]
    have hr0 : ∀ z ∈ O, r z ≠ 0 := fun z hz => left_ne_zero_of_mul_eq_one (hrr z hz)
    refine ⟨O, hOo, hyO, hOsub, r, hrh, hr0, ?_⟩
    refine eqOn_of_coords_ne (ψ b') hOo hOb' ((hSc b').mono hOb')
      (((continuous_norm.comp_continuousOn (holo_continuousOn _ hrh)).pow 2).mul ((hSc b).mono hOb)) ?_
    intro z hz hne
    have hl := locMono_ne (ψ b') (σ b') hne
    have hq := hQsame _ _ (Rb.compat b b' z ⟨hVU b (hOsub hz).1, hVU b' (hOsub hz).2⟩)
    rw [hQS b z (hOb hz), hQS b' z (hOb' hz), hlm1 z hz, norm_mul, mul_pow] at hq
    have hl2 : ‖locMono (ψ b') (σ b') z‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hl)
    refine mul_left_cancel₀ hl2 ?_
    rw [← hq]
    ring
  let L : LocPot Rb.X :=
    { U := fun x => V (jb x), isOpen_U := fun x => hVo _, mem_U := hjV,
      φ := fun x y => c0 - 1 / 2 * Real.log (S (jb x) y) }
  let s : Rb.X → Rb.X → ℂ := fun x y => locMono (ψ (jb x)) (σ (jb x)) y
  have hnorm : ∀ x, ∀ y ∈ V (jb x),
      ‖s x y‖ * Real.exp (-L.φ x y) = Real.exp (-c0) * Real.sqrt (Qf (Rb.lift (jb x) y)) := by
    intro x y hy
    have hS := hSpos (jb x) (hjt x) y hy
    rw [hQS _ y (hVs _ hy), Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    have he : Real.exp (1 / 2 * Real.log (S (jb x) y)) = Real.sqrt (S (jb x) y) := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, sq, ← Real.exp_add,
        show 1 / 2 * Real.log (S (jb x) y) + 1 / 2 * Real.log (S (jb x) y) = Real.log (S (jb x) y) by ring,
        Real.exp_log hS]
    show ‖s x y‖ * Real.exp (-(c0 - 1 / 2 * Real.log (S (jb x) y))) = _
    rw [show -(c0 - 1 / 2 * Real.log (S (jb x) y)) = 1 / 2 * Real.log (S (jb x) y) + -c0 by ring,
      Real.exp_add, he]
    ring
  refine ⟨L, s, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    exact smoothOn_pot Rb.A (fun q => w (jb x) q) (fun q => holoOn_mono _ (hwh _ q) (hVs _))
      (Rb.lift (jb x)) (fun p => holoOn_mono _ (Rb.holo _ p) (hVU _)) aa
      (fun y hy q => hnd _ y (hVU _ hy) q) (fun y hy => hSpos _ (hjt x) y hy) c0
  · intro x x' y hy
    obtain ⟨O, hOo, hyO, hOsub, r, hrh, hr0, hSS⟩ := hover (jb x) (jb x') (hjt x) (hjt x') y hy
    obtain ⟨W', hW'o, hyW', hW'O, F, hF, hFre⟩ := eq_zero_of_mem_all_maximalIdeal_pow Rb.A hOo hrh hr0 hyO
    refine ⟨W', hW'o, hyW', F, hF, ?_⟩
    rintro z ⟨⟨hzW, -⟩, -⟩
    have hzO := hW'O hzW
    show (c0 - 1 / 2 * Real.log (S (jb x) z)) - (c0 - 1 / 2 * Real.log (S (jb x') z)) = (F z).re
    rw [hFre z hzW, hSS z hzO, Real.log_mul (pow_ne_zero 2 (norm_ne_zero_iff.2 (hr0 z hzO)))
      (hSpos _ (hjt x) z (hOsub hzO).1).ne', Real.log_pow]
    push_cast
    ring
  · intro x
    exact holoOn_mono _ (holoOn_locMono Rb.A (hψc _) (σ _)) (hVs _)
  · rintro x x' y ⟨hy, hy'⟩
    rw [hnorm x y hy, hnorm x' y hy',
      hQsame _ _ (Rb.compat (jb x) (jb x') y ⟨hVU _ hy, hVU _ hy'⟩)]
  · intro x
    refine ⟨(ψ (jb x)).restrOpen (V (jb x)) (hVo _), lift_map_comp _ (hψc _) _ _, ?_, ?_, σ (jb x),
      hinj _, ?_, fun _ => 1, holoOn_const _ _ 1, fun _ _ => one_ne_zero, ?_⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact ⟨hVs _ (hjV x), hjV x⟩
    · rw [OpenPartialHomeomorph.restrOpen_source]
      exact Set.inter_subset_right
    · intro k
      rw [OpenPartialHomeomorph.restrOpen_source]
      ext y
      constructor
      · rintro ⟨hyW, hys, hyV⟩
        have h1 : y ∈ W k ∩ (ψ (jb x)).source := ⟨hyW, hys⟩
        rw [hW (jb x) k] at h1
        exact ⟨⟨hys, hyV⟩, h1.2⟩
      · rintro ⟨⟨hys, hyV⟩, hex⟩
        have h1 : y ∈ {y | y ∈ (ψ (jb x)).source ∧ ∃ i, σ (jb x) k = some i ∧ ψ (jb x) y i = 0} :=
          ⟨hys, hex⟩
        rw [← hW (jb x) k] at h1
        exact ⟨h1.1, hys, hyV⟩
    · intro y hy
      rw [one_mul]
      show locMono (ψ (jb x)) (σ (jb x)) y = _
      unfold locMono
      refine Finset.prod_congr rfl fun k _ => ?_
      cases σ (jb x) k with
      | none => rfl
      | some i =>
        simp only [pow_one]
        rfl
  · intro p
    unfold logNormSec
    rw [hnorm p p (hjV p)]
    have hN := hM p (Set.mem_univ p)
    rw [Real.norm_of_nonneg (hNnn p)] at hN
    have hsq : Real.sqrt (Nf p) ≤ Real.sqrt M := Real.sqrt_le_sqrt hN
    have hpos : 0 < Real.sqrt M + 1 := by positivity
    apply Real.log_nonpos (by positivity)
    rw [hc0, Real.exp_neg, Real.exp_log hpos, inv_mul_le_iff₀ hpos]
    show Real.sqrt (Nf p) ≤ _
    linarith
  · intro p
    show locMono (ψ (jb p)) (σ (jb p)) p = 0 ↔ Rb.lift p p ∈ Bc
    rw [← hBc (jb p) p (hVs _ (hjV p))]
    obtain ⟨c, hc, he⟩ := Rb.compat (jb p) p p ⟨hVU _ (hjV p), Rb.mem_U p⟩
    rw [he]
    constructor
    · intro h
      have := htor _ h (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
      simpa [inv_mul_cancel_left₀ (hc _)] using this
    · intro h
      exact htor _ h c hc
  · intro p p' horb
    have hq : Qf (Rb.lift (jb p') p') = Qf (Rb.lift (jb p) p) := by
      rw [show Qf (Rb.lift (jb p') p') = Qf (Rb.lift p' p') from hNf p' p' (Rb.mem_U p'),
        hQsame _ _ horb, hQconj, ← show Qf (Rb.lift (jb p) p) = Qf (Rb.lift p p) from hNf p p (Rb.mem_U p)]
    simp only [rW, logNormSec]
    rw [hnorm p' p' (hjV p'), hnorm p p (hjV p), hq]

end PositivityTheory.Xgp.c_bm_exists_boundary
