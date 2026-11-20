import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGramStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvHodgeMetricGramMumfordGoodGrowthBoundaryChartStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundFrameChangeOrthogonalSummaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHodgeMetricPeriodChartAtBoundaryPointStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.LieBaseGood

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy`. Take `⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩` from `GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy`. Take `⟨ρ, hρ, hρ2, c₀, N₀, hb⟩` from `GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP`. Set `W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim)` to `(ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩ WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ`. Establish `hWo : IsOpen W` using `(ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))`.

Set `G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ` to `fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹`. Set `Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ` to `fun τ u => Q τ u.ofLp`. Establish `hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ)` using `(EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable`. Establish `hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1)`. Introduce `τ i k`.

Use `(hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_` and prove the remaining obligations. Conclude with `(PiLp.norm_apply_le u k').trans_lt (by simpa using hu)`. Establish `hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2)`. Simplify `hind` using `[Q']`. Establish `hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧ GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v`.

Introduce `v hv`. Take `⟨hpd, hcd, hgb⟩` from `hb v hv.2`. Use `⟨?_, hcd, hgb⟩` and prove the remaining obligations. Conclude with `(Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero`. Establish `horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0`.

Introduce `v hv τ τ' hne`. Use `horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne` as an intermediate fact. Rewrite `this` using `[ch.right_inv hv.1.1]`. Then use the resulting hypothesis. Take `⟨r', hr', c', N', hfr⟩` from `GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ) Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'`. Use `⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩` and prove the remaining obligations.

Introduce `b _`. Rewrite using `[hy0]`. Both sides reduce to the same expression. Introduce `z hz`. Rewrite using `[hbd z hz]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi⟩`. Conclude with `⟨Fin.castLE ha i, by simp, hi⟩`. Introduce and unpack `⟨b, hb', hb0⟩`. Take `⟨i, -, rfl⟩` from `Finset.mem_map.1 hb'`.

Conclude with `⟨i, hb0⟩`. Establish `h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ)` using `Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ))) filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ`. Take `⟨hzs, hzb⟩` from `hz`. Rewrite `hzb` using `[mem_ball_zero_iff]`. Establish `hzW : ch z ∈ W`.

Use `⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))`. Introduce `i hi`. Conclude with `(hbd z hzs).2 ⟨i, hi⟩ hzO`. Establish `hGB` using `hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ`.

Use `GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB` and prove the remaining obligations. Use `filter_upwards [hWo.mem_nhds hzW] with u hu`. Use `hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ` as an intermediate fact. Rewrite `this` using `[ch.right_inv hu.1.1]`. Conclude with `this.symm`.
-/
theorem lieGram_isGood : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (C : FlagCpt T.Z e), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : C.Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e C X j f f₀ Eb A₀ → IsGood Eb (openPart j) (lieGram e U hj f₀ A₀) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ch, a, ha, g, rk, τ₀, B, hP, hHolo, hys, hy0, hpoly, hbd, A, hA, Q, hQ, hcard, hind, hform, horth⟩ :=
    GlobalTheory.T.exists_hodgeMetric_periodChart_at_boundaryPoint E H Dw l Xo c O β Y T F e σ U hσ hU C X j f f₀ Eb A₀ hj hL y hy
  obtain ⟨ρ, hρ, hρ2, c₀, N₀, hb⟩ := GlobalTheory.T.inv_hodgeMetricGram_mumfordGoodGrowth_boundaryChart X.dim a ha g rk τ₀ B hP
  let W : Set (ReciprocityTheory.L2DbarEstimates.V X.dim) :=
    (ch.target ∩ ch.symm ⁻¹' GlobalTheory.CxPts.ptsIn X.str (σ.comp e.toRingHom) (openPart j)) ∩
      WithLp.ofLp ⁻¹' GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ
  have hWo : IsOpen W := (ch.isOpen_inter_preimage_symm (GlobalTheory.CxPts.isOpen_ptsIn _)).inter
    ((GlobalTheory.HodgeChartRow.isOpen_punctured ha ρ).preimage (PiLp.continuous_ofLp 2 _))
  let G₀ : ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin g) (Fin g) ℂ :=
    fun u => (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B u.ofLp)⁻¹
  let Q' : ∀ τ : E →+* ℂ, ReciprocityTheory.L2DbarEstimates.V X.dim → Matrix (Fin (Dw.mult τ)) (Fin g) ℂ := fun τ u => Q τ u.ofLp
  have hdo : Differentiable ℂ (WithLp.ofLp : ReciprocityTheory.L2DbarEstimates.V X.dim → Fin X.dim → ℂ) :=
    (EuclideanSpace.equiv (Fin X.dim) ℂ).differentiable
  have hQ' : ∀ τ i k, DifferentiableOn ℂ (fun u => Q' τ u i k) (Metric.ball 0 1) := by
    intro τ i k
    refine (hQ τ i k).comp hdo.differentiableOn fun u hu k' => ?_
    exact (PiLp.norm_apply_le u k').trans_lt (by simpa using hu)
  have hind' : LinearIndependent ℂ (fun p : Σ τ, Fin (Dw.mult τ) => Q' p.1 0 p.2) := by
    simpa [Q'] using hind
  have hG₀ : ∀ v ∈ W, (G₀ v).det ≠ 0 ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => G₀ u i k) v) ∧
      GlobalTheory.GoodMetric.GoodBound (Finset.univ.map (Fin.castLEEmb ha)) c₀ N₀ G₀ v := by
    intro v hv
    obtain ⟨hpd, hcd, hgb⟩ := hb v hv.2
    refine ⟨?_, hcd, hgb⟩
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.2 hpd.det_pos.ne')).ne_zero
  have horth' : ∀ v ∈ W, ∀ τ τ', τ ≠ τ' → Q' τ v * G₀ v * (Q' τ' v)ᴴ = 0 := by
    intro v hv τ τ' hne
    have := horth (ch.symm v) (ch.map_target hv.1.1) hv.1.2 τ τ' hne
    rwa [ch.right_inv hv.1.1] at this
  obtain ⟨r', hr', c', N', hfr⟩ := GlobalTheory.T.mumfordGoodGrowthBound_frameChange_orthogonalSummands X.dim g (Finset.univ.map (Fin.castLEEmb ha)) W G₀ c₀ N₀ (E →+* ℂ)
    Dw.mult Q' 1 hWo one_pos hQ' hcard hind' hG₀ horth'
  refine ⟨ch, Finset.univ.map (Fin.castLEEmb ha), hHolo, hys, ?_, ?_, A, hA, c', N', ?_⟩
  · intro b _
    rw [hy0]
    rfl
  · intro z hz
    rw [hbd z hz]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨Fin.castLE ha i, by simp, hi⟩
    · rintro ⟨b, hb', hb0⟩
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hb'
      exact ⟨i, hb0⟩
  · have h1 : ∀ᶠ z in nhds y, z ∈ ch.source ∧ ch z ∈ Metric.ball (0 : ReciprocityTheory.L2DbarEstimates.V X.dim) (min r' ρ) :=
      Filter.Eventually.and (ch.open_source.mem_nhds hys) ((ch.continuousAt hys).preimage_mem_nhds
        (by rw [hy0]; exact Metric.ball_mem_nhds _ (lt_min hr' hρ)))
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hzO τ
    obtain ⟨hzs, hzb⟩ := hz
    rw [mem_ball_zero_iff] at hzb
    have hzW : ch z ∈ W := by
      refine ⟨⟨ch.map_source hzs, Set.mem_preimage.2 (by rw [ch.left_inv hzs]; exact hzO)⟩, ?_, ?_⟩
      · exact fun k => (PiLp.norm_apply_le _ k).trans_lt (hzb.trans_le (min_le_right _ _))
      · intro i hi
        exact (hbd z hzs).2 ⟨i, hi⟩ hzO
    have hGB := hfr (ch z) hzW (hzb.trans_le (min_le_left _ _)) τ
    refine GlobalTheory.T.mumfordGoodGrowthBound_congr_germ_gram X.dim _ _ c' N' _ _ (ch z) ?_ hGB
    filter_upwards [hWo.mem_nhds hzW] with u hu
    have := hform (ch.symm u) (ch.map_target hu.1.1) hu.1.2 τ
    rw [ch.right_inv hu.1.1] at this
    exact this.symm

end GlobalTheory.LieBaseGood
