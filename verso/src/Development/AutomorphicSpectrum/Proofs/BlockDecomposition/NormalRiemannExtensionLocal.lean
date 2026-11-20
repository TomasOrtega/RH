import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalRiemannExtensionLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalUniversalDenominator
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalBoundedQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalLocallyIrreducible
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermCurve
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Branch

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets MvPolynomial Topology Filter Metric

/- English proof (translation)
Introduce `σ _ I h w U f hI hIc hh hw hU hf hb`. Establish `hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q)`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on with`. Consider the case `C c => simp`.

Consider the case `add p q hp hq => simp only [eval_add]`. Conclude with `hp.add hq`. Consider the case `mul_X p i hp => simp only [eval_mul, eval_X]`. Conclude with `hp.mul (differentiable_apply i)`. Take `⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩` from `hud σ I h w U f hI hh hw hU hf hb`.

Take `⟨M, hM⟩` from `hb.exists_norm_le`. Establish `hhg : h * g ∉ I` using `fun hm => (hI.mem_or_mem hm).elim hh hg`. Choose the witnesses or unpack the hypotheses as in `⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧ zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by`. Use `⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h1` using `hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩`.

Use `closure_mono (fun y hy => ?_) h1` and prove the remaining obligations. Conclude with `⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩`. Use `set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT`. Establish `hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g)` using `hpoly g`. Establish `hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧ eval z g * f z = F z`.

Introduce `z hz`. Establish `hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0`. Simplify `hz.2` using `only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or]`. Conclude with `⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2, hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩`. Establish `hTf : ∀ z ∈ T, F z / eval z g = f z` using `fun z hz => by`.

Take `⟨-, hg0, he⟩` from `hTS z hz`. Rewrite using `[← he, mul_div_cancel_left₀ _ hg0]`. Establish `hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆ Metric.closedBall 0 M`. Introduce and unpack `_ ⟨p, hp, rfl⟩`. Establish `hpc : p ∈ closure T` using `hdense hp.1`.

Establish `hcont : ContinuousWithinAt (fun z => F z / eval z g) T p` using `(((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div (hGd p).continuousAt hp.2)).continuousWithinAt`. Use `closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Rewrite using `[Metric.mem_closedBall, dist_zero_right]`. Use `show ‖F z / eval z g‖ ≤ M`.

Rewrite using `[hTf z hz]`. Conclude with `hM _ ⟨z, (hTS z hz).1, rfl⟩`. Establish `hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0)`. Introduce `hev`. Take `⟨z, hzW, hzT⟩` from `mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev`.

Conclude with `(hTS z hzT).2.1 (hzW hzT.1.1)`. Take `⟨V, hVo, hwV, H, hH, hFGH⟩` from `hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)`. Use `⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Take `⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩` from `hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩`.

Rewrite using `[hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]`. Use `set O := V ∩ Up`. Establish `hOo : IsOpen O` using `hVo.inter hUpo`. Establish `hpO : p ∈ O` using `⟨hp.1.2.1, hpUp⟩`. Use `set s := O ∩ T`.

Establish `heq : Set.EqOn H Fp s`. Introduce `z hz`. Take `⟨hzS, hg0, he⟩` from `hTS z hz.2`. Establish `h1 : eval z g * H z = eval z g * f z`. Rewrite using `[he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]`.

Rewrite using `[mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]`. Establish `hsO : insert p s ⊆ O` using `Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩`. Conclude with `heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO) ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s) (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩) (Set.mem_insert p s)`.
-/
theorem normalRiemannExtensionLocal (hud : LocalUniversalDenominator.Statement)
    (hbq : NormalBoundedQuotient.Statement) (hvan : VanishNearPoint.Statement) :
    NormalRiemannExtensionLocal.Statement := by
  intro σ _ I h w U f hI hIc hh hw hU hf hb
  classical
  have hpoly : ∀ q : MvPolynomial σ ℂ, Differentiable ℂ (fun z : σ → ℂ => eval z q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c => simp
    | add p q hp hq => simp only [eval_add]; exact hp.add hq
    | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)
  obtain ⟨g, hg, N, hNo, hwN, hNU, F, hF, hFg⟩ := hud σ I h w U f hI hh hw hU hf hb
  obtain ⟨M, hM⟩ := hb.exists_norm_le
  have hhg : h * g ∉ I := fun hm => (hI.mem_or_mem hm).elim hh hg
  obtain ⟨B, hBo, hwB, hBN, hdense⟩ : ∃ B : Set (σ → ℂ), IsOpen B ∧ w ∈ B ∧ B ⊆ N ∧
      zeroSetIn I ∩ B ⊆ closure ((zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0}) := by
    refine ⟨N, hNo, hwN, subset_rfl, fun z hz => ?_⟩
    have h1 := hNo.inter_closure ⟨hz.2, zeroSetIn_subset_closure_diff hvan I (h * g) hI hhg hz.1⟩
    refine closure_mono (fun y hy => ?_) h1
    exact ⟨⟨hy.2.1, hy.1⟩, hy.2.2⟩
  set T := (zeroSetIn I ∩ B) \ {z | eval z (h * g) = 0} with hT
  have hGd : Differentiable ℂ (fun z : σ → ℂ => eval z g) := hpoly g

  have hTS : ∀ z ∈ T, z ∈ (zeroSetIn I ∩ U) \ {z | eval z h = 0} ∧ eval z g ≠ 0 ∧
      eval z g * f z = F z := by
    intro z hz
    have hz2 : eval z h ≠ 0 ∧ eval z g ≠ 0 := by
      simpa only [Set.mem_ofPred_eq, eval_mul, mul_eq_zero, not_or] using hz.2
    exact ⟨⟨⟨hz.1.1, hNU (hBN hz.1.2)⟩, hz2.1⟩, hz2.2,
      hFg z ⟨⟨hz.1.1, hBN hz.1.2⟩, hz2.1⟩⟩
  have hTf : ∀ z ∈ T, F z / eval z g = f z := fun z hz => by
    obtain ⟨-, hg0, he⟩ := hTS z hz
    rw [← he, mul_div_cancel_left₀ _ hg0]
  have hbound : (fun z => F z / eval z g) '' ((zeroSetIn I ∩ B) \ {z | eval z g = 0}) ⊆
      Metric.closedBall 0 M := by
    rintro _ ⟨p, hp, rfl⟩
    have hpc : p ∈ closure T := hdense hp.1
    have hcont : ContinuousWithinAt (fun z => F z / eval z g) T p :=
      (((hF.continuousOn.continuousAt (hNo.mem_nhds (hBN hp.1.2))).div
        (hGd p).continuousAt hp.2)).continuousWithinAt
    refine closure_minimal ?_ Metric.isClosed_closedBall (hcont.mem_closure_image hpc)
    rintro _ ⟨z, hz, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F z / eval z g‖ ≤ M
    rw [hTf z hz]
    exact hM _ ⟨z, (hTS z hz).1, rfl⟩
  have hnv : ¬ (∀ᶠ z in 𝓝 w, z ∈ zeroSetIn I → eval z g = 0) := by
    intro hev
    obtain ⟨z, hzW, hzT⟩ := mem_closure_iff_nhds.1 (hdense ⟨hw, hwB⟩) _ hev
    exact (hTS z hzT).2.1 (hzW hzT.1.1)
  obtain ⟨V, hVo, hwV, H, hH, hFGH⟩ := hbq σ I w B F (fun z => eval z g) hI hIc hw hBo hwB
    (hF.mono hBN) hGd.differentiableOn hnv ((Metric.isBounded_closedBall).subset hbound)
  refine ⟨V ∩ B, hVo.inter hBo, ⟨hwV, hwB⟩, fun z hz => hNU (hBN hz.2), H, hH.mono Set.inter_subset_left, ?_⟩
  intro p hp
  obtain ⟨Up, hUpo, hpUp, Fp, hFp, hfFp⟩ :=
    hf p ⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩
  rw [hfFp ⟨⟨⟨hp.1.1, hNU (hBN hp.1.2.2)⟩, hp.2⟩, hpUp⟩]

  set O := V ∩ Up
  have hOo : IsOpen O := hVo.inter hUpo
  have hpO : p ∈ O := ⟨hp.1.2.1, hpUp⟩
  set s := O ∩ T
  have heq : Set.EqOn H Fp s := by
    intro z hz
    obtain ⟨hzS, hg0, he⟩ := hTS z hz.2
    have h1 : eval z g * H z = eval z g * f z := by
      rw [he, hFGH z ⟨hz.2.1.1, hz.1.1⟩]
    rw [mul_left_cancel₀ hg0 h1, hfFp ⟨hzS, hz.1.2⟩]
  have hsO : insert p s ⊆ O := Set.insert_subset_iff.2 ⟨hpO, fun z hz => hz.1⟩
  exact heq.of_subset_closure ((hH.mono Set.inter_subset_left).continuousOn.mono hsO)
    ((hFp.mono Set.inter_subset_right).continuousOn.mono hsO) (Set.subset_insert p s)
    (Set.insert_subset_iff.2 ⟨hOo.inter_closure ⟨hpO, hdense ⟨hp.1.1, hp.1.2.2⟩⟩, subset_closure⟩)
    (Set.mem_insert p s)

/- English proof (translation)
Introduce `σ _ X w hX hirr hacc`. Take `⟨Y, W, A, hW, hYX, hYa, hYi, hiso, hdom⟩` from `hslice σ X w hX hirr hacc`. Take `⟨Y', p, ρ, N, hY'Y, hcov⟩` from `hdisc σ Y w A hYa hYi hiso hdom`. Take `⟨r, hr, γ, hγd, hγi, hγ0, hγY⟩` from `hCv σ Y' w p ρ N hcov`. Establish `hcont : ContinuousAt γ 0` using `hγd.continuousOn.continuousAt (ball_mem_nhds 0 hr)`.

Establish `hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ)` using `hcont.preimage_mem_nhds (by rw [hγ0]; exact hW)`. Take `⟨r', hr', hsub⟩` from `Metric.mem_nhds_iff.1 (inter_mem hpre (ball_mem_nhds (0 : ℂ) hr))`. Establish `hle : ball (0 : ℂ) r' ⊆ ball 0 r` using `fun t ht => (hsub ht).2`. Conclude with `⟨r', hr', γ, hγd.mono hle, hγi.mono hle, hγ0, fun t ht => hYX ⟨hY'Y (hγY (hle ht)), (hsub ht).1⟩⟩`.
-/
theorem irreducibleGermCurve
    (hslice : ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ), IsAnalyticNear X w →
      GermIrreducibleAt X w → AccPt w (𝓟 X) →
      ∃ (Y W : Set (σ → ℂ)) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), W ∈ 𝓝 w ∧ Y ∩ W ⊆ X ∧
        IsAnalyticNear Y w ∧ GermIrreducibleAt Y w ∧ (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) ∧
        ∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0)
    (hdisc : ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ)
      (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w →
      (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) →
      (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) →
          ∀ᶠ y in 𝓝 (A w), h y = 0) →
      ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N)
    (hCv : CentredDiscCoverCurve.Statement) : IrreducibleGermCurve.Statement := by
  intro σ _ X w hX hirr hacc
  obtain ⟨Y, W, A, hW, hYX, hYa, hYi, hiso, hdom⟩ := hslice σ X w hX hirr hacc
  obtain ⟨Y', p, ρ, N, hY'Y, hcov⟩ := hdisc σ Y w A hYa hYi hiso hdom
  obtain ⟨r, hr, γ, hγd, hγi, hγ0, hγY⟩ := hCv σ Y' w p ρ N hcov
  have hcont : ContinuousAt γ 0 := hγd.continuousOn.continuousAt (ball_mem_nhds 0 hr)
  have hpre : γ ⁻¹' W ∈ 𝓝 (0 : ℂ) := hcont.preimage_mem_nhds (by rw [hγ0]; exact hW)
  obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.1 (inter_mem hpre (ball_mem_nhds (0 : ℂ) hr))
  have hle : ball (0 : ℂ) r' ⊆ ball 0 r := fun t ht => (hsub ht).2
  exact ⟨r', hr', γ, hγd.mono hle, hγi.mono hle, hγ0,
    fun t ht => hYX ⟨hY'Y (hγY (hle ht)), (hsub ht).1⟩⟩

end GlobalTheory.CompanionTheory.Ar.Branch
