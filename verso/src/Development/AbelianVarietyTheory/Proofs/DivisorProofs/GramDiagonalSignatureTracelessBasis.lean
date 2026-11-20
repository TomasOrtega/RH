import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasis

noncomputable section

namespace GlobalTheory.SUVol.LieMeasFree

open MeasureTheory Matrix NumberField
open scoped ENNReal
open GlobalTheory.SUVol GlobalTheory.SUVol.DensOne ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.SUVol.LieMeas

/- English proof (translation)
Use `set D : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) with hDdef`. Establish `hD : ∀ τ, D τ * D τ = 1`. Introduce `τ`. Rewrite using `[hDdef, diagonal_mul_diagonal, ← diagonal_one]`. Apply the tactic sequence `congr 1; funext a; unfold sgn; split_ifs <;> simp`.

Establish `hDc : ∀ τ, (D τ).map (starRingEnd ℂ) = D τ`. Introduce `τ`. Rewrite using `[hDdef, diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Establish `hxD : ∀ τ, (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) = D τ` using `fun τ => by`. Rewrite using `[← gram_eq]`. Conclude with `ho τ`. Establish `hx : ∀ τ, (mat x τ).det ≠ 0`.

Introduce `τ h`. Establish `h1` using `congrArg Matrix.det (hxD τ)`. Establish `h2` using `congrArg Matrix.det (hD τ)`. Rewrite `h1` using `[det_mul, det_mul, det_transpose, h]`. Simplify using `[← h1] at h2`.

Establish `hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0` using `fun i => skew_matrix G (he i).2`. Establish `hE : LinearIndependent E e` using `GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli`. Establish `hR : ∀ τ : Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1)` using `fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE`. Establish `hmem : ∀ (τ : Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧ ((e i).map τ.1).trace = 0`. Introduce `τ i`.

Use `⟨map_skew G (hsk i) τ.1, ?_⟩` and prove the remaining obligations. Establish `h1 : ((e i).map τ.1).trace = τ.1 (e i).trace` using `by simp [Matrix.trace, map_sum]`. Rewrite using `[h1, (he i).1, map_zero]`. Establish `hinj : Function.Injective (coordMap Ψ e)`. Use `(injective_iff_map_eq_zero (coordMap Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_` and prove the remaining obligations.

Establish `h1` using `coordMap_apply Ψ e c τ`. Rewrite `h1` using `[hc]`. Conclude with `Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i`. Establish `hsurj : ∀ Z ∈ realLie Ψ G, ∃ c, coordMap Ψ e c = Z`. Introduce `Z hZ`.

Establish `hX'` using `(mem_realLie_iff Ψ G Z).1 hZ`. Establish `hspan : ∀ τ : Ψ, Matrix.of (Z τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1)` using `fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2`. Use `choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)`. Use `⟨c, funext fun τ => ?_⟩` and prove the remaining obligations. Establish `h1` using `coordMap_apply Ψ e c τ`.

Rewrite `h1` using `[hc τ]`. Conclude with `h1`. Establish `hin : ∀ c, coordMap Ψ e c ∈ realLie Ψ G`. Introduce `c`. Use `(mem_realLie_iff Ψ G _).2 fun τ => ?_` and prove the remaining obligations.

Rewrite using `[coordMap_apply]`. Use `⟨?_, by simp [trace_sum, (hmem τ _).2]⟩` and prove the remaining obligations. Establish `h1 : (∑ i, c τ i • (e i).map τ.1).map (starRingEnd ℂ) = ∑ i, c τ i • ((e i).map τ.1).map (starRingEnd ℂ)`. Use extensionality with `a b`. Simplify using `[Matrix.sum_apply]`.

Rewrite using `[h1, transpose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hmem τ i).1, smul_zero]`. Set `f0 : (Ψ → Fin (r ^ 2 - 1) → ℝ) →ₗ[ℝ] (realLie Ψ G).comap (fromFrame x)` to `((toFrame x).comp (coordMap Ψ e)).codRestrict _ fun c => by`. Express the relevant statement in the definitionally equal form `fromFrame x (toFrame x (coordMap Ψ e c)) ∈ realLie Ψ G`.

Rewrite using `[fromFrame_toFrame x hx]`. Conclude with `hin c`. Establish `hf0 : ∀ c, fromFrame x (f0 c).1 = coordMap Ψ e c` using `fun c => fromFrame_toFrame x hx _`. Establish `hb : Function.Bijective f0`. Use `⟨fun c d h => hinj (by rw [← hf0, ← hf0, h]), fun Y => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `hsurj _ Y.2`. Use `⟨c, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `toFrame x (coordMap Ψ e c) = Y.1`. Rewrite using `[hc, toFrame_fromFrame x hx]`. Set `f` to `LinearEquiv.ofBijective f0 hb`.

Set `Y : Ψ → Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ` to `fun τ i => (mat x τ)⁻¹ * (e i).map τ.1 * mat x τ`. Establish `hfY : ∀ τ i σ, Matrix.of (fun a b => (f (Pi.single τ (Pi.single i 1))).1 (σ, a, b)) = if σ = τ then Y τ i else 0`. Introduce `τ i σ`. Express the relevant statement in the definitionally equal form `Matrix.of (fun a b => toFrame x (coordMap Ψ e (Pi.single τ (Pi.single i 1))) (σ, a, b)) = _`. Rewrite using `[toFrame_apply, coordMap_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[Y, Pi.single_apply]`. Simplify using `[h]`. Establish `hgram : (Matrix.of fun p q : Fin (r ^ 2 - 1) × Ψ => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1))) (f (Pi.single q.2 (Pi.single q.1 1)))) = blockDiagonal fun τ => Matrix.of fun i j => (trace (Y τ i * (Y τ j)ᴴ)).re`.

Use extensionality with `⟨i, τ⟩ ⟨j, σ⟩`. Rewrite using `[Matrix.of_apply, Submodule.coe_inner, inner_eq_sum_trace, blockDiagonal_apply]`. Simplify using `only [hfY]`. Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]`. Distinguish the cases in `h : τ = σ`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hYli : ∀ τ, LinearIndependent ℝ (Y τ)`. Introduce `τ`.

Use `Fintype.linearIndependent_iff.2 fun g hg => Fintype.linearIndependent_iff.1 (hR τ) g ?_` and prove the remaining obligations. Establish `h1 : (mat x τ)⁻¹ * (∑ i, g i • (e i).map τ.1) * mat x τ = 0`. Rewrite using `[← hg]`. Simplify using `[Y, Finset.mul_sum, Finset.sum_mul]`. Establish `h2` using `congrArg (fun M => mat x τ * M * (mat x τ)⁻¹) h1`.

Simplify using `only [Matrix.mul_zero, Matrix.zero_mul] at h2`. Rewrite `h2` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Then use the resulting hypothesis. Establish `htr : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ), trace ((mat x τ)⁻¹ * M * mat x τ) = trace M`. Introduce `τ M`. Rewrite using `[trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`.

Establish `hYsk : ∀ τ i, (Y τ i)ᵀ * D τ + D τ * (Y τ i).map (starRingEnd ℂ) = 0 ∧ (Y τ i).trace = 0`. Introduce `τ i`. Use `⟨?_, by rw [htr, (hmem τ i).2]⟩` and prove the remaining obligations. Establish `h0 : mat x τ * Y τ i = (e i).map τ.1 * mat x τ`. Simplify using `only [Y, Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Establish `h1` using `congrArg (fun M => (mat x τ)ᵀ * M * (mat x τ).map (starRingEnd ℂ)) (hmem τ i).1`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul] at h1`. Rewrite using `[← hxD τ, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, h0, transpose_mul, Matrix.mul_assoc _ ((mat x τ).map _), ← Matrix.map_mul, h0, Matrix.map_mul]`. Simplify using `only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`.

Establish `hdetτ : ∀ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det = (Matrix.of fun i j => trace (Y τ i * Y τ j)).det`. Introduce `τ`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Establish `h1 : Y τ i * Y τ j = (mat x τ)⁻¹ * ((e i * e j).map τ.1) * mat x τ`. Rewrite using `[Matrix.map_mul]`. Simplify using `only [Y, Matrix.mul_assoc]`. Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]`. Rewrite using `[Matrix.of_apply, h1, htr]`.

Simplify using `[Matrix.trace, map_sum, Matrix.mul_apply]`. Establish `hcF : Continuous fun Z : (realLie Ψ G).comap (fromFrame x) => fromFrame x Z.1` using `(fromFrame x).continuous_of_finiteDimensional.comp continuous_subtype_val`. Establish `hcf : Continuous f` using `f.toLinearMap.continuous_of_finiteDimensional`. Unfold `riemLie`. Rewrite using `[volume_eq_sqrt_gram_map f, Measure.map_smul, Measure.map_map hcF.measurable hcf.measurable, hgram, det_blockDiagonal, Finset.abs_prod, norm_prod]`.

Use `congr 3`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[hdetτ, abs_det_re_trace (D τ) (hD τ) (hDc τ) (Y τ) (hYli τ) (hYsk τ)]`. Use function extensionality and compare the values at `c`. Conclude with `hf0 c`.
-/
theorem riemLie_eq_smul_formLie_of_signs (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Ψ : Finset (E →+* ℂ)) (x : Frame Ψ r) (p0 : Ψ → ℕ)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (_hr : 2 ≤ r) (hG : G.det ≠ 0)
    (ho : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (he : ∀ i, (e i).trace = 0 ∧ ∀ u w, herm G (e i *ᵥ u) w + herm G u (e i *ᵥ w) = 0)
    (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie Ψ G x = ENNReal.ofReal (Real.sqrt
      ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖) • formLie Ψ e := by
  classical
  set D : Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => Matrix.diagonal fun a : Fin r => ((sgn (p0 τ) (a : ℕ) : ℝ) : ℂ) with hDdef
  have hD : ∀ τ, D τ * D τ = 1 := by
    intro τ
    rw [hDdef, diagonal_mul_diagonal, ← diagonal_one]
    congr 1; funext a; unfold sgn; split_ifs <;> simp
  have hDc : ∀ τ, (D τ).map (starRingEnd ℂ) = D τ := by
    intro τ
    rw [hDdef, diagonal_map (map_zero _)]
    congr 1; funext a; simp
  have hxD : ∀ τ, (mat x τ)ᵀ * G.map τ.1 * (mat x τ).map (starRingEnd ℂ) = D τ := fun τ => by
    rw [← gram_eq]; exact ho τ
  have hx : ∀ τ, (mat x τ).det ≠ 0 := by
    intro τ h
    have h1 := congrArg Matrix.det (hxD τ)
    have h2 := congrArg Matrix.det (hD τ)
    rw [det_mul, det_mul, det_transpose, h] at h1
    simp [← h1] at h2
  have hsk : ∀ i, (e i)ᵀ * G + G * (e i).map cc = 0 := fun i => skew_matrix G (he i).2
  have hE : LinearIndependent E e := GlobalTheory.T.real_independent_skew_matrices G hG e hsk hli
  have hR : ∀ τ : Ψ, LinearIndependent ℝ (fun i => (e i).map τ.1) := fun τ => GlobalTheory.T.linear_independent_complex_map τ.1 e hE
  have hmem : ∀ (τ : Ψ) i, ((e i).map τ.1)ᵀ * G.map τ.1 + G.map τ.1 * ((e i).map τ.1).map (starRingEnd ℂ) = 0 ∧
      ((e i).map τ.1).trace = 0 := by
    intro τ i
    refine ⟨map_skew G (hsk i) τ.1, ?_⟩
    have h1 : ((e i).map τ.1).trace = τ.1 (e i).trace := by simp [Matrix.trace, map_sum]
    rw [h1, (he i).1, map_zero]
  have hinj : Function.Injective (coordMap Ψ e) := by
    refine (injective_iff_map_eq_zero (coordMap Ψ e)).2 fun c hc => funext fun τ => funext fun i => ?_
    have h1 := coordMap_apply Ψ e c τ
    rw [hc] at h1
    exact Fintype.linearIndependent_iff.1 (hR τ) (c τ) h1.symm i
  have hsurj : ∀ Z ∈ realLie Ψ G, ∃ c, coordMap Ψ e c = Z := by
    intro Z hZ
    have hX' := (mem_realLie_iff Ψ G Z).1 hZ
    have hspan : ∀ τ : Ψ, Matrix.of (Z τ) ∈ Submodule.span ℝ (Set.range fun i => (e i).map τ.1) :=
      fun τ => GlobalTheory.T.unitary_lie_algebra_spanned (G.map τ.1) (det_map_ne G hG τ.1) _ (hR τ) (hmem τ) _ (hX' τ).1 (hX' τ).2
    choose c hc using fun τ => (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hspan τ)
    refine ⟨c, funext fun τ => ?_⟩
    have h1 := coordMap_apply Ψ e c τ
    rw [hc τ] at h1
    exact h1
  have hin : ∀ c, coordMap Ψ e c ∈ realLie Ψ G := by
    intro c
    refine (mem_realLie_iff Ψ G _).2 fun τ => ?_
    rw [coordMap_apply]
    refine ⟨?_, by simp [trace_sum, (hmem τ _).2]⟩
    have h1 : (∑ i, c τ i • (e i).map τ.1).map (starRingEnd ℂ) =
        ∑ i, c τ i • ((e i).map τ.1).map (starRingEnd ℂ) := by
      ext a b; simp [Matrix.sum_apply]
    rw [h1, transpose_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, (hmem τ i).1, smul_zero]
  let f0 : (Ψ → Fin (r ^ 2 - 1) → ℝ) →ₗ[ℝ] (realLie Ψ G).comap (fromFrame x) :=
    ((toFrame x).comp (coordMap Ψ e)).codRestrict _ fun c => by
      change fromFrame x (toFrame x (coordMap Ψ e c)) ∈ realLie Ψ G
      rw [fromFrame_toFrame x hx]; exact hin c
  have hf0 : ∀ c, fromFrame x (f0 c).1 = coordMap Ψ e c := fun c => fromFrame_toFrame x hx _
  have hb : Function.Bijective f0 := by
    refine ⟨fun c d h => hinj (by rw [← hf0, ← hf0, h]), fun Y => ?_⟩
    obtain ⟨c, hc⟩ := hsurj _ Y.2
    refine ⟨c, Subtype.ext ?_⟩
    change toFrame x (coordMap Ψ e c) = Y.1
    rw [hc, toFrame_fromFrame x hx]
  let f := LinearEquiv.ofBijective f0 hb
  let Y : Ψ → Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) ℂ := fun τ i => (mat x τ)⁻¹ * (e i).map τ.1 * mat x τ
  have hfY : ∀ τ i σ, Matrix.of (fun a b => (f (Pi.single τ (Pi.single i 1))).1 (σ, a, b)) =
      if σ = τ then Y τ i else 0 := by
    intro τ i σ
    change Matrix.of (fun a b => toFrame x (coordMap Ψ e (Pi.single τ (Pi.single i 1))) (σ, a, b)) = _
    rw [toFrame_apply, coordMap_apply]
    split_ifs with h
    · subst h; simp [Y, Pi.single_apply]
    · simp [h]
  have hgram : (Matrix.of fun p q : Fin (r ^ 2 - 1) × Ψ => inner ℝ (f (Pi.single p.2 (Pi.single p.1 1)))
      (f (Pi.single q.2 (Pi.single q.1 1)))) =
      blockDiagonal fun τ => Matrix.of fun i j => (trace (Y τ i * (Y τ j)ᴴ)).re := by
    ext ⟨i, τ⟩ ⟨j, σ⟩
    rw [Matrix.of_apply, Submodule.coe_inner, inner_eq_sum_trace, blockDiagonal_apply]
    simp only [hfY]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)]
    by_cases h : τ = σ
    · subst h; simp
    · simp [h]
  have hYli : ∀ τ, LinearIndependent ℝ (Y τ) := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun g hg => Fintype.linearIndependent_iff.1 (hR τ) g ?_
    have h1 : (mat x τ)⁻¹ * (∑ i, g i • (e i).map τ.1) * mat x τ = 0 := by
      rw [← hg]; simp [Y, Finset.mul_sum, Finset.sum_mul]
    have h2 := congrArg (fun M => mat x τ * M * (mat x τ)⁻¹) h1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h2
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ (hx τ).isUnit,
      Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit] at h2
  have htr : ∀ τ (M : Matrix (Fin r) (Fin r) ℂ), trace ((mat x τ)⁻¹ * M * mat x τ) = trace M := by
    intro τ M
    rw [trace_mul_comm, Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
  have hYsk : ∀ τ i, (Y τ i)ᵀ * D τ + D τ * (Y τ i).map (starRingEnd ℂ) = 0 ∧ (Y τ i).trace = 0 := by
    intro τ i
    refine ⟨?_, by rw [htr, (hmem τ i).2]⟩
    have h0 : mat x τ * Y τ i = (e i).map τ.1 * mat x τ := by
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    have h1 := congrArg (fun M => (mat x τ)ᵀ * M * (mat x τ).map (starRingEnd ℂ)) (hmem τ i).1
    simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
    rw [← hxD τ, ← h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← transpose_mul, h0, transpose_mul,
      Matrix.mul_assoc _ ((mat x τ).map _), ← Matrix.map_mul, h0, Matrix.map_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hdetτ : ∀ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det =
      (Matrix.of fun i j => trace (Y τ i * Y τ j)).det := by
    intro τ
    rw [RingHom.map_det]
    congr 1
    ext i j
    have h1 : Y τ i * Y τ j = (mat x τ)⁻¹ * ((e i * e j).map τ.1) * mat x τ := by
      rw [Matrix.map_mul]
      simp only [Y, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hx τ).isUnit]
    rw [Matrix.of_apply, h1, htr]
    simp [Matrix.trace, map_sum, Matrix.mul_apply]
  have hcF : Continuous fun Z : (realLie Ψ G).comap (fromFrame x) => fromFrame x Z.1 :=
    (fromFrame x).continuous_of_finiteDimensional.comp continuous_subtype_val
  have hcf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  unfold riemLie
  rw [volume_eq_sqrt_gram_map f, Measure.map_smul, Measure.map_map hcF.measurable hcf.measurable, hgram,
    det_blockDiagonal, Finset.abs_prod, norm_prod]
  congr 3
  · refine Finset.prod_congr rfl fun τ _ => ?_
    rw [hdetτ, abs_det_re_trace (D τ) (hD τ) (hDc τ) (Y τ) (hYli τ) (hYsk τ)]
  · funext c
    exact hf0 c

end GlobalTheory.SUVol.LieMeasFree
