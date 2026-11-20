import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTangentGraphLowerDensity
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyLelongMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.inPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i))

def TangentGraphLowerDensity.outPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I} :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : {j : Fin n // j ∉ I} => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : {j : Fin n // j ∉ I} => innerSL ℂ (b j))

/- English proof (translation)
Simplify using `[TangentGraphLowerDensity.inPart]`.
-/
theorem TangentGraphLowerDensity.inPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by
  simp [TangentGraphLowerDensity.inPart]

/- English proof (translation)
Simplify using `[TangentGraphLowerDensity.outPart]`.
-/
theorem TangentGraphLowerDensity.outPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by
  simp [TangentGraphLowerDensity.outPart]

/- English proof (translation)
Use `PiLp.ext fun i => ?_` and prove the remaining obligations. Simplify using `[TangentGraphLowerDensity.inPart_apply, frameProj]`.
-/
theorem TangentGraphLowerDensity.inPart_eq_toLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by
  refine PiLp.ext fun i => ?_
  simp [TangentGraphLowerDensity.inPart_apply, frameProj]

/- English proof (translation)
Rewrite using `[← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]`. Simplify using `only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply, OrthonormalBasis.repr_apply_apply]`. Use `(Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3` and compare the differences between its conclusion and the goal. Use `congr 1`. Conclude with `Subsingleton.elim _ _`.
-/
theorem TangentGraphLowerDensity.norm_sq_split {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by
  classical
  rw [← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply,
    OrthonormalBasis.repr_apply_apply]
  convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3
  congr 1; exact Subsingleton.elim _ _

/- English proof (translation)
Introduce `n d b I₀ S Ω V g w₀ hcard hΩ _hV hw₀ hg hproj hSV htan θ hθ`. Use `set P := TangentGraphLowerDensity.inPart b I₀ with hPdef`. Use `set Q := TangentGraphLowerDensity.outPart b I₀ with hQdef`. Establish `hgd : DifferentiableAt ℂ g w₀` using `hg.differentiableAt (hΩ.mem_nhds hw₀)`. Establish `hQ0 : Q.comp (fderiv ℂ g w₀) = 0`.

Use `ContinuousLinearMap.ext fun v => PiLp.ext fun j => ?_` and prove the remaining obligations. Establish `h1 : HasFDerivAt (fun w => inner ℂ (b j) (g w)) ((innerSL ℂ (b (j : Fin n))).comp (fderiv ℂ g w₀)) w₀` using `(innerSL ℂ (b (j : Fin n))).hasFDerivAt.comp w₀ hgd.hasFDerivAt`. Establish `h2` using `h1.fderiv`. Rewrite `h2` using `[htan j j.2]`. Establish `h3` using `congrArg (fun L => L v) h2`.

Simplify `h3.symm` using `[hQdef, TangentGraphLowerDensity.outPart_apply]`. Establish `hQd : HasFDerivAt (fun w => Q (g w)) (0 : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I₀}) w₀`. Establish `h` using `Q.hasFDerivAt.comp w₀ hgd.hasFDerivAt`. Rewrite `h` using `[hQ0]`. Conclude with `h`.

Choose the witnesses or unpack the hypotheses as in `⟨η, hη, hθη⟩ : ∃ η : ℝ, 0 < η ∧ θ * (1 + η) ^ (2 * d) < 1 := by`. Establish `hc : Continuous fun η : ℝ => θ * (1 + η) ^ (2 * d)` using `by fun_prop`. Establish `h0 : ∀ᶠ η in 𝓝 (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1` using `hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ.2)`. Establish `h0' : ∀ᶠ η in 𝓝[>] (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1` using `nhdsWithin_le_nhds h0`. Take `⟨η, h1, h2⟩` from `(h0'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists`.

Conclude with `⟨η, h2, h1⟩`. Establish `hlo` using `hasFDerivAt_iff_isLittleO.1 hQd`. Establish `hev : ∀ᶠ w in 𝓝 w₀, ‖Q (g w) - Q (g w₀)‖ ≤ η * ‖w - w₀‖ ∧ w ∈ Ω`. Use `((hlo.def hη).mono fun w hw => ?_).and (hΩ.mem_nhds hw₀)` and prove the remaining obligations. Simplify using `using hw`.

Take `⟨δ, hδ, hδw⟩` from `Metric.eventually_nhds_iff.1 hev`. Use `⟨(1 + η) * δ, by positivity, fun ρ hρ => ?_⟩` and prove the remaining obligations. Establish `h1η : 0 < 1 + η` using `by linarith`. Use `set s := ρ / (1 + η) with hs`. Establish `hs0 : 0 < s` using `div_pos hρ.1 h1η`.

Establish `hsδ : s < δ`. Rewrite using `[hs, div_lt_iff₀ h1η]`. Combine the linear relations using `[hρ.2]`. Use `set x₀ : EuclideanSpace ℂ I₀ := WithLp.toLp 2 w₀ with hx₀`. Establish `hPx : ∀ w ∈ Ω, P (g w) = WithLp.toLp 2 w` using `fun w hw => by`.

Rewrite using `[hPdef, TangentGraphLowerDensity.inPart_eq_toLp, hproj w hw]`. Establish `hsub : Metric.ball x₀ s ⊆ P '' (S ∩ Metric.ball (g w₀) ρ)`. Introduce `v hv`. Establish `hv' : ‖v - x₀‖ < s` using `by rwa [Metric.mem_ball, dist_eq_norm] at hv`. Establish `hww : ‖WithLp.ofLp v - w₀‖ ≤ ‖v - x₀‖`.

Use `(pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_` and prove the remaining obligations. Simplify `PiLp.norm_apply_le (v - x₀) i` using `[hx₀]`. Establish `hwδ : dist (WithLp.ofLp v) w₀ < δ`. Rewrite using `[dist_eq_norm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨hQw, hwΩ⟩` from `hδw hwδ`. Use `⟨g (WithLp.ofLp v), ⟨?_, ?_⟩, by rw [hPx _ hwΩ, WithLp.toLp_ofLp]⟩` and prove the remaining obligations. Establish `hm : g (WithLp.ofLp v) ∈ S ∩ V` using `hSV ▸ Set.mem_image_of_mem g hwΩ`. Conclude with `hm.1`. Rewrite using `[Metric.mem_ball, dist_eq_norm]`.

Establish `hsplit` using `TangentGraphLowerDensity.norm_sq_split b I₀ (g (WithLp.ofLp v) - g w₀)`. Establish `hPd : P (g (WithLp.ofLp v) - g w₀) = v - x₀`. Rewrite using `[map_sub, hPx _ hwΩ, hPx _ hw₀, WithLp.toLp_ofLp]`. Establish `hQd' : Q (g (WithLp.ofLp v) - g w₀) = Q (g (WithLp.ofLp v)) - Q (g w₀)` using `map_sub _ _ _`. Rewrite `hsplit` using `[← hPdef, ← hQdef, hPd, hQd']`.

Establish `hle : ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + ‖Q (g (WithLp.ofLp v)) - Q (g w₀)‖`. Use polynomial arithmetic with `[norm_nonneg (g (WithLp.ofLp v) - g w₀), norm_nonneg (v - x₀), norm_nonneg (Q (g (WithLp.ofLp v)) - Q (g w₀))]`. Combine the equalities or inequalities in the displayed calculation. Establish `hd0 : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hcardI : Fintype.card I₀ = d` using `by rw [Fintype.card_coe, hcard]`.

Set `L` to `LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFinOfCardEq hcardI)`. Establish `hball : μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) = ENNReal.ofReal (s ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1)`. Rewrite using `[← VarietyLelongMono.euclBall_measure d (L x₀) hs0, ← L.image_ball, L.isometry.hausdorffMeasure_image (Or.inl hd0)]`. Establish `hLip : LipschitzWith 1 P` using `LipschitzWith.of_dist_le_mul fun x y => by`. Rewrite using `[dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]`.

Establish `h` using `TangentGraphLowerDensity.norm_sq_split b I₀ (x - y)`. Rewrite `h` using `[← hPdef, ← hQdef]`. Use polynomial arithmetic with `[norm_nonneg (P (x - y)), norm_nonneg (x - y), norm_nonneg (Q (x - y))]`. Establish `hreal : θ * ρ ^ (2 * d) ≤ s ^ (2 * d)`. Establish `hpos : 0 < (1 + η) ^ (2 * d)` using `by positivity`.

Establish `hρp : 0 ≤ ρ ^ (2 * d)` using `by have := hρ.1; positivity`. Rewrite using `[hs, div_pow, le_div_iff₀ hpos]`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `h` using `hLip.hausdorffMeasure_image_le hd0 (S ∩ Metric.ball (g w₀) ρ)`.

Simplify using `using h`.
-/
theorem TangentGraphLowerDensity.proof : TangentGraphLowerDensity.Statement := by
  intro n d b I₀ S Ω V g w₀ hcard hΩ _hV hw₀ hg hproj hSV htan θ hθ
  classical
  set P := TangentGraphLowerDensity.inPart b I₀ with hPdef
  set Q := TangentGraphLowerDensity.outPart b I₀ with hQdef
  have hgd : DifferentiableAt ℂ g w₀ := hg.differentiableAt (hΩ.mem_nhds hw₀)

  have hQ0 : Q.comp (fderiv ℂ g w₀) = 0 := by
    refine ContinuousLinearMap.ext fun v => PiLp.ext fun j => ?_
    have h1 : HasFDerivAt (fun w => inner ℂ (b j) (g w))
        ((innerSL ℂ (b (j : Fin n))).comp (fderiv ℂ g w₀)) w₀ :=
      (innerSL ℂ (b (j : Fin n))).hasFDerivAt.comp w₀ hgd.hasFDerivAt
    have h2 := h1.fderiv
    rw [htan j j.2] at h2
    have h3 := congrArg (fun L => L v) h2
    simpa [hQdef, TangentGraphLowerDensity.outPart_apply] using h3.symm
  have hQd : HasFDerivAt (fun w => Q (g w)) (0 : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I₀}) w₀ := by
    have h := Q.hasFDerivAt.comp w₀ hgd.hasFDerivAt
    rw [hQ0] at h
    exact h

  obtain ⟨η, hη, hθη⟩ : ∃ η : ℝ, 0 < η ∧ θ * (1 + η) ^ (2 * d) < 1 := by
    have hc : Continuous fun η : ℝ => θ * (1 + η) ^ (2 * d) := by fun_prop
    have h0 : ∀ᶠ η in 𝓝 (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ.2)
    have h0' : ∀ᶠ η in 𝓝[>] (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 := nhdsWithin_le_nhds h0
    obtain ⟨η, h1, h2⟩ := (h0'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    exact ⟨η, h2, h1⟩
  have hlo := hasFDerivAt_iff_isLittleO.1 hQd
  have hev : ∀ᶠ w in 𝓝 w₀, ‖Q (g w) - Q (g w₀)‖ ≤ η * ‖w - w₀‖ ∧ w ∈ Ω := by
    refine ((hlo.def hη).mono fun w hw => ?_).and (hΩ.mem_nhds hw₀)
    simpa using hw
  obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨(1 + η) * δ, by positivity, fun ρ hρ => ?_⟩
  have h1η : 0 < 1 + η := by linarith
  set s := ρ / (1 + η) with hs
  have hs0 : 0 < s := div_pos hρ.1 h1η
  have hsδ : s < δ := by
    rw [hs, div_lt_iff₀ h1η]
    linarith [hρ.2]
  set x₀ : EuclideanSpace ℂ I₀ := WithLp.toLp 2 w₀ with hx₀
  have hPx : ∀ w ∈ Ω, P (g w) = WithLp.toLp 2 w := fun w hw => by
    rw [hPdef, TangentGraphLowerDensity.inPart_eq_toLp, hproj w hw]

  have hsub : Metric.ball x₀ s ⊆ P '' (S ∩ Metric.ball (g w₀) ρ) := by
    intro v hv
    have hv' : ‖v - x₀‖ < s := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have hww : ‖WithLp.ofLp v - w₀‖ ≤ ‖v - x₀‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simpa [hx₀] using PiLp.norm_apply_le (v - x₀) i
    have hwδ : dist (WithLp.ofLp v) w₀ < δ := by
      rw [dist_eq_norm]
      linarith
    obtain ⟨hQw, hwΩ⟩ := hδw hwδ
    refine ⟨g (WithLp.ofLp v), ⟨?_, ?_⟩, by rw [hPx _ hwΩ, WithLp.toLp_ofLp]⟩
    · have hm : g (WithLp.ofLp v) ∈ S ∩ V := hSV ▸ Set.mem_image_of_mem g hwΩ
      exact hm.1
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsplit := TangentGraphLowerDensity.norm_sq_split b I₀ (g (WithLp.ofLp v) - g w₀)
      have hPd : P (g (WithLp.ofLp v) - g w₀) = v - x₀ := by
        rw [map_sub, hPx _ hwΩ, hPx _ hw₀, WithLp.toLp_ofLp]
      have hQd' : Q (g (WithLp.ofLp v) - g w₀) = Q (g (WithLp.ofLp v)) - Q (g w₀) := map_sub _ _ _
      rw [← hPdef, ← hQdef, hPd, hQd'] at hsplit
      have hle : ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + ‖Q (g (WithLp.ofLp v)) - Q (g w₀)‖ := by
        nlinarith [norm_nonneg (g (WithLp.ofLp v) - g w₀), norm_nonneg (v - x₀),
          norm_nonneg (Q (g (WithLp.ofLp v)) - Q (g w₀))]
      calc ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + η * ‖v - x₀‖ := by nlinarith
        _ = (1 + η) * ‖v - x₀‖ := by ring
        _ < (1 + η) * s := by gcongr
        _ = ρ := by rw [hs]; field_simp

  have hd0 : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcardI : Fintype.card I₀ = d := by rw [Fintype.card_coe, hcard]
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFinOfCardEq hcardI)
  have hball : μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) =
      ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
    rw [← VarietyLelongMono.euclBall_measure d (L x₀) hs0, ← L.image_ball,
      L.isometry.hausdorffMeasure_image (Or.inl hd0)]
  have hLip : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    have h := TangentGraphLowerDensity.norm_sq_split b I₀ (x - y)
    rw [← hPdef, ← hQdef] at h
    nlinarith [norm_nonneg (P (x - y)), norm_nonneg (x - y), norm_nonneg (Q (x - y))]
  have hreal : θ * ρ ^ (2 * d) ≤ s ^ (2 * d) := by
    have hpos : 0 < (1 + η) ^ (2 * d) := by positivity
    have hρp : 0 ≤ ρ ^ (2 * d) := by have := hρ.1; positivity
    rw [hs, div_pow, le_div_iff₀ hpos]
    calc θ * ρ ^ (2 * d) * (1 + η) ^ (2 * d) = ρ ^ (2 * d) * (θ * (1 + η) ^ (2 * d)) := by ring
      _ ≤ ρ ^ (2 * d) * 1 := by gcongr
      _ = ρ ^ (2 * d) := mul_one _
  calc ENNReal.ofReal (θ * ρ ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1)
      ≤ ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
        gcongr
    _ = μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) := hball.symm
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (P '' (S ∩ Metric.ball (g w₀) ρ)) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ) := by
        have h := hLip.hausdorffMeasure_image_le hd0 (S ∩ Metric.ball (g w₀) ρ)
        simpa using h

end

end GroundTheory.Heights₂.Heights
