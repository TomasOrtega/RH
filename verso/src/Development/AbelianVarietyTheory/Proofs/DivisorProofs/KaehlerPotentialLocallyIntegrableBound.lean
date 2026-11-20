import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartMatrixSmoothInvertible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExponentialChartSmoothFormStatement
open CategoryTheory AlgebraicGeometry Filter Topology Set MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg
open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.RhoSmooth

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.FinChart

open Matrix in

/- English proof (translation)
Unfold `mean`. Use `congr 1`. Use `integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)` and prove the remaining obligations. Distinguish the cases in `h0 : cutoff (q ξ) = 0`. Simplify using `only [h0, mul_zero]`.

Use `show f ξ * _ = g ξ * _`. Rewrite using `[h ξ (cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' h0))]`.
-/
theorem mean_congr_cutoff {d : ℕ} (q f g : (Fin d → ℂ) → ℝ) (h : ∀ ξ, q ξ < 1 → f ξ = g ξ) :
    mean q f = mean q g := by
  unfold mean
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  by_cases h0 : cutoff (q ξ) = 0
  · simp only [h0, mul_zero]
  · show f ξ * _ = g ξ * _
    rw [h ξ (cutoff_pos_iff.1 ((cutoff_nonneg _).lt_of_ne' h0))]

open Matrix in

/- English proof (translation)
Introduce `k _ Y p σ d _ _ R a E ψ ha hE hψ`. Establish `key : ∀ y, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y' ∈ W, CxPts.CInfAt (fun z => rho a E ψ z t) y'`. Introduce `y`. Take `⟨c, hy, hloc⟩` from `hψ y`. Set `N : Set ((Fin d → ℂ) × (Fin d → ℂ))` to `{q | q.1 ∈ c.finChart.target ∧ E c (c.finChart.symm q.1) q.2 ∈ c.e.source}`.

Set `G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ` to `fun q => c.finChart (E c (c.finChart.symm q.1) q.2)`. Set `q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ` to `fun z ξ => a c (c.finChart.symm z) ξ`. Set `L : (Fin d → ℂ) × (Fin d → ℂ) →L[ℝ] V d × V d` to `(toV d).toContinuousLinearMap.prodMap (toV d).toContinuousLinearMap`. Establish `hU : IsOpen c.finChart.target` using `c.finChart.open_target`. Establish `hz₀ : c.finChart y ∈ c.finChart.target` using `c.finChart.map_source hy`.

Establish `hFy : c.finChart.symm (c.finChart y) = y` using `c.finChart.left_inv hy`. Establish `hN : IsOpen N`. Establish `hc : ContinuousOn (fun q : (Fin d → ℂ) × (Fin d → ℂ) => E c (c.finChart.symm q.1) q.2) (c.finChart.target ×ˢ univ)` using `(hE.cont c).comp L.continuous.continuousOn fun q hq => ⟨hq.1, mem_univ _⟩`. Use `hc.isOpen_inter_preimage (hU.prod isOpen_univ) c.e.open_source` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Conclude with `Set.ext fun q => ⟨fun h => ⟨⟨h.1, trivial⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩`. Establish `h0N : (c.finChart y, (0 : Fin d → ℂ)) ∈ N` using `⟨hz₀, by show E c (c.finChart.symm (c.finChart y)) 0 ∈ c.e.source`. Rewrite using `[hFy, hE.zero c y hy]`. Conclude with `hy⟩`. Establish `hGs : ContDiffOn ℝ ∞ G N` using `(toV d).symm.contDiff.comp_contDiffOn ((hE.smooth c c).comp L.contDiff.contDiffOn fun q hq => ⟨hq.1, hq.2⟩)`.

Establish `hG0 : G (c.finChart y, 0) = c.finChart y` using `by show c.finChart (E c (c.finChart.symm (c.finChart y)) 0) = c.finChart y`. Rewrite using `[hFy, hE.zero c y hy]`. Establish `hder : HasFDerivAt (fun ξ => G (c.finChart y, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0`. Establish `hd : DifferentiableAt ℝ (fun ξ => G (c.finChart y, ξ)) 0` using `((hGs.contDiffAt (hN.mem_nhds h0N)).differentiableAt (by simp)).comp (0 : Fin d → ℂ) (differentiableAt_const _ |>.prodMk differentiableAt_id)`. Use `hd.hasFDerivAt using 1` and compare the differences between its conclusion and the goal.

Use `(ContinuousLinearMap.ext fun ξ => ?_).symm` and prove the remaining obligations. Establish `h1` using `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const ξ) (by simp)`. Establish `h2` using `(toV d).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1`. Establish `hj` using `hE.jets c y hy (toV d ξ) 1`. Rewrite `hj` using `[iteratedDeriv_one, jet_one]`.

Establish `e : (fun t : ℝ => c.e (E c y (t • (toV d ξ).ofLp))) = (toV d) ∘ (fun ξ => G (c.finChart y, ξ)) ∘ (fun t : ℝ => id t • ξ)`. Use function extensionality and compare the values at `t`. Use `show _ = toV d (c.finChart (E c (c.finChart.symm (c.finChart y)) (t • ξ)))`. Rewrite using `[hFy]`. Both sides reduce to the same expression.

Rewrite `hj` using `[e, h2.deriv]`. Simplify using `using (toV d).injective hj`. Take `⟨hM, -, hform⟩` from `MatSmooth.matIn_smooth_unit_form k Y p σ d R a ha c`. Establish `hq : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (c.finChart.target ×ˢ univ)`. Establish `hexpr : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => ((p.2 ᵥ* matIn a c (toV d p.1)) ⬝ᵥ star p.2).re) (c.finChart.target ×ˢ univ)`.

Simplify using `only [Matrix.vecMul, dotProduct, Pi.star_apply]`. Use `Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun i _ => (ContDiffOn.sum fun j _ => ?_).mul ?_)` and prove the remaining obligations. Conclude with `((contDiff_apply ℝ ℂ j).comp contDiff_snd).contDiffOn.mul ((hM j i).comp ((toV d).contDiff.comp contDiff_fst).contDiffOn fun p hp => hp.1)`. Conclude with `(Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn`. Use `hexpr.congr fun p hp => ?_` and prove the remaining obligations.

Use `hform (toV d p.1) hp.1 (toV d p.2)` as an intermediate fact. Rewrite using `[← Complex.ofReal_re (q p.1 p.2)]`. Conclude with `congrArg Complex.re this`. Establish `hhom : ∀ z ∈ c.finChart.target, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ` using `fun z hz => (continuous_and_smul ha (c.finChart.map_target hz)).2`. Establish `hpos : ∀ z ∈ c.finChart.target, ∀ ξ, ξ ≠ 0 → 0 < q z ξ` using `fun z hz ξ hξ => ha.2 c _ (c.finChart.map_target hz) ξ hξ`.

Take `⟨δ, hδ, U', hU'o, hzU', hU'U, hmem, hsm⟩` from `GlobalTheory.T.exponential_chart_smooth_form d c.finChart.target N G q (c.finChart y) hU hz₀ hN h0N hGs hG0 hder hq hhom hpos`. Use `⟨c.e.source ∩ c.finChart ⁻¹' U', c.finChart.isOpen_inter_preimage hU'o, ⟨hy, hzU'⟩, ?_⟩` and prove the remaining obligations. Use `filter_upwards [Ioo_mem_nhdsGT hδ] with t ht y' hy'`. Use `cInfAt_of_chart (c.finChart.isOpen_inter_preimage hU'o) c ?_ hy'.1 hy'` and prove the remaining obligations. Use `(c.contDiffOn_finChart_iff ∞ _ _).1 (((hsm _ hloc t ht.1 ht.2).mono ?_).congr ?_)` and prove the remaining obligations.

Introduce `z hz`. Use `hz.2.2` as an intermediate fact. Rewrite `this` using `[mem_preimage, c.finChart.right_inv hz.1]`. Then use the resulting hypothesis. Introduce `z hz`. Establish `hzU : z ∈ U'`.

Use `hz.2.2` as an intermediate fact. Rewrite `this` using `[mem_preimage, c.finChart.right_inv hz.1]`. Then use the resulting hypothesis. Use `show rho a E ψ (c.finChart.symm z) t = _`. Rewrite using `[rho_eq ha hE ψ hz.2.1 t, rhoIn]`. Use `mean_congr_cutoff _ _ _ fun ξ hξ => ?_` and prove the remaining obligations.

Establish `hm` using `(hmem z hzU t ht.1 ht.2 ξ hξ).2`. Use `show _ = ψ (c.finChart.symm (c.finChart (E c (c.finChart.symm z) (t • ξ))))`. Rewrite using `[c.finChart.left_inv hm]`. Use `choose W hWo hyW hev using key`. Take `⟨s, -, hs⟩` from `(isCompact_univ (X := CxPts p σ)).elim_nhds_subcover W fun y _ => (hWo y).mem_nhds (hyW y)`.

Establish `hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ s, ∀ y' ∈ W y, CxPts.CInfAt (fun z => rho a E ψ z t) y'` using `(eventually_all_finset s).2 fun y _ => hev y`. Take `⟨δ, hδ, hδs⟩` from `(nhdsGT_basis_of_exists_gt ⟨1, one_pos⟩).eventually_iff.1 hall`. Use `⟨δ, hδ, fun t ht0 htδ y => ?_⟩` and prove the remaining obligations. Take `⟨i, hi, hyi⟩` from `mem_iUnion₂.1 (hs (mem_univ y))`. Conclude with `hδs ⟨ht0, htδ⟩ i hi y hyi`.
-/
theorem rho_cInfAt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [CompactSpace (CxPts p σ)] (R : AnRead p σ d) (a : ChartForm p σ d) (E : ChartMap p σ d) (ψ : CxPts p σ → ℝ), IsKaehlerForm R a → IsExph a E → (∀ y, ∃ c : AlgChart p σ d, y ∈ c.e.source ∧ MeasureTheory.LocallyIntegrableOn (ψ ∘ c.finChart.symm) c.finChart.target MeasureTheory.volume) → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ → ∀ y, CxPts.CInfAt (fun z => rho a E ψ z t) y := by
  intro k _ Y p σ d _ _ R a E ψ ha hE hψ
  have key : ∀ y, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y' ∈ W, CxPts.CInfAt (fun z => rho a E ψ z t) y' := by
    intro y
    obtain ⟨c, hy, hloc⟩ := hψ y
    let N : Set ((Fin d → ℂ) × (Fin d → ℂ)) :=
      {q | q.1 ∈ c.finChart.target ∧ E c (c.finChart.symm q.1) q.2 ∈ c.e.source}
    let G : (Fin d → ℂ) × (Fin d → ℂ) → Fin d → ℂ := fun q => c.finChart (E c (c.finChart.symm q.1) q.2)
    let q : (Fin d → ℂ) → (Fin d → ℂ) → ℝ := fun z ξ => a c (c.finChart.symm z) ξ
    let L : (Fin d → ℂ) × (Fin d → ℂ) →L[ℝ] V d × V d :=
      (toV d).toContinuousLinearMap.prodMap (toV d).toContinuousLinearMap
    have hU : IsOpen c.finChart.target := c.finChart.open_target
    have hz₀ : c.finChart y ∈ c.finChart.target := c.finChart.map_source hy
    have hFy : c.finChart.symm (c.finChart y) = y := c.finChart.left_inv hy
    have hN : IsOpen N := by
      have hc : ContinuousOn (fun q : (Fin d → ℂ) × (Fin d → ℂ) => E c (c.finChart.symm q.1) q.2)
          (c.finChart.target ×ˢ univ) :=
        (hE.cont c).comp L.continuous.continuousOn fun q hq => ⟨hq.1, mem_univ _⟩
      have := hc.isOpen_inter_preimage (hU.prod isOpen_univ) c.e.open_source
      convert this using 1
      exact Set.ext fun q => ⟨fun h => ⟨⟨h.1, trivial⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    have h0N : (c.finChart y, (0 : Fin d → ℂ)) ∈ N := ⟨hz₀, by
      show E c (c.finChart.symm (c.finChart y)) 0 ∈ c.e.source
      rw [hFy, hE.zero c y hy]; exact hy⟩
    have hGs : ContDiffOn ℝ ∞ G N :=
      (toV d).symm.contDiff.comp_contDiffOn ((hE.smooth c c).comp L.contDiff.contDiffOn fun q hq => ⟨hq.1, hq.2⟩)
    have hG0 : G (c.finChart y, 0) = c.finChart y := by
      show c.finChart (E c (c.finChart.symm (c.finChart y)) 0) = c.finChart y
      rw [hFy, hE.zero c y hy]
    have hder : HasFDerivAt (fun ξ => G (c.finChart y, ξ)) (ContinuousLinearMap.id ℝ (Fin d → ℂ)) 0 := by
      have hd : DifferentiableAt ℝ (fun ξ => G (c.finChart y, ξ)) 0 :=
        ((hGs.contDiffAt (hN.mem_nhds h0N)).differentiableAt (by simp)).comp (0 : Fin d → ℂ)
          (differentiableAt_const _ |>.prodMk differentiableAt_id)
      convert hd.hasFDerivAt using 1
      refine (ContinuousLinearMap.ext fun ξ => ?_).symm
      have h1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).smul_const ξ) (by simp)
      have h2 := (toV d).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
      have hj := hE.jets c y hy (toV d ξ) 1
      rw [iteratedDeriv_one, jet_one] at hj
      have e : (fun t : ℝ => c.e (E c y (t • (toV d ξ).ofLp))) =
          (toV d) ∘ (fun ξ => G (c.finChart y, ξ)) ∘ (fun t : ℝ => id t • ξ) := by
        funext t
        show _ = toV d (c.finChart (E c (c.finChart.symm (c.finChart y)) (t • ξ)))
        rw [hFy]
        rfl
      rw [e, h2.deriv] at hj
      simpa using (toV d).injective hj
    obtain ⟨hM, -, hform⟩ := MatSmooth.matIn_smooth_unit_form k Y p σ d R a ha c
    have hq : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) => q p.1 p.2) (c.finChart.target ×ˢ univ) := by
      have hexpr : ContDiffOn ℝ ∞ (fun p : (Fin d → ℂ) × (Fin d → ℂ) =>
          ((p.2 ᵥ* matIn a c (toV d p.1)) ⬝ᵥ star p.2).re) (c.finChart.target ×ˢ univ) := by
        simp only [Matrix.vecMul, dotProduct, Pi.star_apply]
        refine Complex.reCLM.contDiff.comp_contDiffOn (ContDiffOn.sum fun i _ => (ContDiffOn.sum fun j _ => ?_).mul ?_)
        · exact ((contDiff_apply ℝ ℂ j).comp contDiff_snd).contDiffOn.mul
            ((hM j i).comp ((toV d).contDiff.comp contDiff_fst).contDiffOn fun p hp => hp.1)
        · exact (Complex.conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ i).comp contDiff_snd)).contDiffOn
      refine hexpr.congr fun p hp => ?_
      have := hform (toV d p.1) hp.1 (toV d p.2)
      rw [← Complex.ofReal_re (q p.1 p.2)]
      exact congrArg Complex.re this
    have hhom : ∀ z ∈ c.finChart.target, ∀ (t : ℝ) ξ, q z (t • ξ) = t ^ 2 * q z ξ := fun z hz =>
      (continuous_and_smul ha (c.finChart.map_target hz)).2
    have hpos : ∀ z ∈ c.finChart.target, ∀ ξ, ξ ≠ 0 → 0 < q z ξ := fun z hz ξ hξ =>
      ha.2 c _ (c.finChart.map_target hz) ξ hξ
    obtain ⟨δ, hδ, U', hU'o, hzU', hU'U, hmem, hsm⟩ :=
      GlobalTheory.T.exponential_chart_smooth_form d c.finChart.target N G q (c.finChart y) hU hz₀ hN h0N hGs hG0 hder hq hhom hpos
    refine ⟨c.e.source ∩ c.finChart ⁻¹' U', c.finChart.isOpen_inter_preimage hU'o, ⟨hy, hzU'⟩, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT hδ] with t ht y' hy'
    refine cInfAt_of_chart (c.finChart.isOpen_inter_preimage hU'o) c ?_ hy'.1 hy'
    refine (c.contDiffOn_finChart_iff ∞ _ _).1 (((hsm _ hloc t ht.1 ht.2).mono ?_).congr ?_)
    · intro z hz
      have := hz.2.2
      rwa [mem_preimage, c.finChart.right_inv hz.1] at this
    · intro z hz
      have hzU : z ∈ U' := by
        have := hz.2.2
        rwa [mem_preimage, c.finChart.right_inv hz.1] at this
      show rho a E ψ (c.finChart.symm z) t = _
      rw [rho_eq ha hE ψ hz.2.1 t, rhoIn]
      refine mean_congr_cutoff _ _ _ fun ξ hξ => ?_
      have hm := (hmem z hzU t ht.1 ht.2 ξ hξ).2
      show _ = ψ (c.finChart.symm (c.finChart (E c (c.finChart.symm z) (t • ξ))))
      rw [c.finChart.left_inv hm]
  choose W hWo hyW hev using key
  obtain ⟨s, -, hs⟩ := (isCompact_univ (X := CxPts p σ)).elim_nhds_subcover W
    fun y _ => (hWo y).mem_nhds (hyW y)
  have hall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ s, ∀ y' ∈ W y, CxPts.CInfAt (fun z => rho a E ψ z t) y' :=
    (eventually_all_finset s).2 fun y _ => hev y
  obtain ⟨δ, hδ, hδs⟩ := (nhdsGT_basis_of_exists_gt ⟨1, one_pos⟩).eventually_iff.1 hall
  refine ⟨δ, hδ, fun t ht0 htδ y => ?_⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 (hs (mem_univ y))
  exact hδs ⟨ht0, htδ⟩ i hi y hyi

end GlobalTheory.ChernReg.RhoSmooth
