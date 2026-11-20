import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StAPrimeChartLevi
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StChartVelLift
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm (levi)

/- English proof (translation)
Unfold `levi`. Establish `h : Complex.I • (r • w) = r • (Complex.I • w)` using `smul_comm _ _ _`. Rewrite using `[h]`. Simplify using `only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_real_smul {κ : Type*} [Fintype κ] (φ : (κ → ℂ) → ℝ) (z w : κ → ℂ) (r : ℝ) :
    levi φ z (r • w) = r ^ 2 * levi φ z w := by
  unfold levi
  have h : Complex.I • (r • w) = r • (Complex.I • w) := smul_comm _ _ _
  rw [h]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Take `⟨γ, h0, hd, hev, hv⟩` from `h`. Establish `hm : HasDerivAt (fun s : ℂ => (r : ℂ) * s) (r : ℂ) 0`. Simplify using `using (hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)`. Establish `ht : Tendsto (fun s : ℂ => (r : ℂ) * s) (𝓝 0) (𝓝 0)`. Simplify using `using hm.continuousAt.tendsto`.

Establish `hsw : ∀ {κ : Type} (u : κ → ℂ), (r : ℂ) • u = r • u` using `fun u => by`. Use function extensionality and compare the values at `p`. Simplify using `[Complex.real_smul]`. Use `⟨fun s => γ ((r : ℂ) * s), by simpa using h0, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hd' : HasDerivAt γ w ((r : ℂ) * 0)` using `by simpa using hd`.

Establish `h'` using `hd'.scomp (0 : ℂ) hm`. Rewrite `h'` using `[hsw]`. Conclude with `h'`. Use `filter_upwards [ht.eventually hev] with s hs`. Conclude with `⟨hs.1.comp s (differentiableAt_id.const_mul _), hs.2⟩`.

Establish `hv' : HasDerivAt (fun s => e (M.proj (γ s))) v ((r : ℂ) * 0)` using `by simpa using hv`. Establish `h'` using `hv'.scomp (0 : ℂ) hm`. Rewrite `h'` using `[hsw]`. Conclude with `h'`.
-/
theorem IsChartVel.real_smul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {d : ℕ} {M : CxModel P d} {e : OpenPartialHomeomorph M.Xc (Fin d → ℂ)} {z w : (Σ k, ι k) → ℂ}
    {v : Fin d → ℂ} (h : IsChartVel M e z w v) (r : ℝ) : IsChartVel M e z (r • w) (r • v) := by
  obtain ⟨γ, h0, hd, hev, hv⟩ := h
  have hm : HasDerivAt (fun s : ℂ => (r : ℂ) * s) (r : ℂ) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)
  have ht : Tendsto (fun s : ℂ => (r : ℂ) * s) (𝓝 0) (𝓝 0) := by
    simpa using hm.continuousAt.tendsto
  have hsw : ∀ {κ : Type} (u : κ → ℂ), (r : ℂ) • u = r • u := fun u => by
    funext p
    simp [Complex.real_smul]
  refine ⟨fun s => γ ((r : ℂ) * s), by simpa using h0, ?_, ?_, ?_⟩
  · have hd' : HasDerivAt γ w ((r : ℂ) * 0) := by simpa using hd
    have h' := hd'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'
  · filter_upwards [ht.eventually hev] with s hs
    exact ⟨hs.1.comp s (differentiableAt_id.const_mul _), hs.2⟩
  · have hv' : HasDerivAt (fun s => e (M.proj (γ s))) v ((r : ℂ) * 0) := by simpa using hv
    have h' := hv'.scomp (0 : ℂ) hm
    rw [hsw] at h'
    exact h'

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X`. Establish `hk : ∀ k : Fin X.S.R.N, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, X.M.proj z ∈ X.S.R.mid k → ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v → c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w`. Introduce `k`. Take `⟨Q, hcont, hrep⟩` from `hQ II Ψ K ι Ω E D O Lt X k`. Use `set e := X.S.R.chart k with he`.

Establish `hpos : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < Q y v`. Introduce `y hy v hv`. Take `⟨z, hz, hpz, w, hw, hcone, hnt⟩` from `hL II Ψ K ι Ω E D O Lt X k y hy v hv`. Establish `hs : X.M.proj z ∈ e.source` using `by rw [hpz]; exact e.map_target hy`. Establish `hr` using `hrep z hz hs w v hw`.

Rewrite `hr` using `[hpz, e.right_inv hy]`. Rewrite using `[← hr]`. Conclude with `D.A'_pos.2 z hz w hcone hnt`. Use `set S := (e '' closure (X.S.R.mid k)) ×ˢ Metric.sphere (0 : Fin D.n → ℂ) 1 with hS`. Establish `hcpt : IsCompact S` using `(isClosed_closure.isCompact.image_of_continuousOn (e.continuousOn.mono (X.S.R.closure_mid k))).prod (isCompact_sphere 0 1)`.

Establish `hsub : S ⊆ e.target ×ˢ Set.univ`. Introduce and unpack `⟨y, u⟩ ⟨⟨x, hx, rfl⟩, -⟩`. Conclude with `⟨e.map_source (X.S.R.closure_mid k hx), Set.mem_univ _⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ Q p.1 p.2 := by`. Break down `S.eq_empty_or_nonempty with hE | hne` into its components or cases.

Conclude with `⟨1, one_pos, by simp [hE]⟩`. Take `⟨p, hp, hmin⟩` from `hcpt.exists_isMinOn hne (hcont.mono hsub)`. Use `⟨Q p.1 p.2, hpos p.1 (hsub hp).1 p.2 ?_, fun q hq => hmin hq⟩` and prove the remaining obligations. Introduce `h0`. Establish `h2` using `hp.2`.

Rewrite `h2` using `[h0, Metric.mem_sphere, dist_self]`. Conclude with `zero_ne_one h2`. Use `⟨c, hc, fun z hz w hm v hv => ?_⟩` and prove the remaining obligations. Establish `hs : X.M.proj z ∈ e.source` using `X.S.R.mid_subset_source k hm`. Establish `hy : e (X.M.proj z) ∈ e '' closure (X.S.R.mid k)` using `⟨_, subset_closure hm, rfl⟩`.

Establish `h1` using `hrep z hz hs w v hv`. Break down `eq_or_ne v 0 with rfl | hv0` into its components or cases. Establish `h2` using `hrep z hz hs _ _ (hv.real_smul 0)`. Rewrite `h2` using `[levi_real_smul, smul_zero]`. Rewrite using `[h1, ← h2]`.

Simplify using the standard rewrite rules. Establish `hn : 0 < ‖v‖` using `norm_pos_iff.2 hv0`. Establish `h2` using `hrep z hz hs _ _ (hv.real_smul ‖v‖⁻¹)`. Rewrite `h2` using `[levi_real_smul]`. Establish `hu : (e (X.M.proj z), ‖v‖⁻¹ • v) ∈ S`.

Use `⟨hy, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']`. Establish `h3` using `hcle _ hu`. Rewrite `h3` using `[← h2]`. Combine the equalities or inequalities in the displayed calculation.

Clear the denominators using the available nonvanishing facts. Use `choose ck hck hmk using hk`. Establish `hne : (insert 1 (Finset.univ.image ck)).Nonempty` using `Finset.insert_nonempty _ _`. Use `⟨(insert 1 (Finset.univ.image ck)).min' hne, ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 (Finset.min'_mem _ hne) with h | h` into its components or cases.

Rewrite using `[h]`. Conclude with `one_pos`. Take `⟨k, -, hk⟩` from `Finset.mem_image.1 h`. Rewrite using `[← hk]`. Conclude with `hck k`.

Introduce `z hz w k hm v hv`. Conclude with `le_trans (mul_le_mul_of_nonneg_right (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k)))) (by positivity)) (hmk k z hz w hm v hv)`.
-/
theorem APrimeChartMargin.proof (hQ : APrimeChartLevi.Statement) (hL : ChartVelLift.Statement) :
    APrimeChartMargin.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  have hk : ∀ k : Fin X.S.R.N, ∃ c : ℝ, 0 < c ∧ ∀ z ∈ mcPts (mCoordIdeal D.y), ∀ w, X.M.proj z ∈ X.S.R.mid k →
      ∀ v : Fin D.n → ℂ, IsChartVel X.M (X.S.R.chart k) z w v →
        c * ‖v‖ ^ 2 ≤ levi (fun y => Real.log (D.A'.h y)) z w := by
    intro k
    obtain ⟨Q, hcont, hrep⟩ := hQ II Ψ K ι Ω E D O Lt X k
    set e := X.S.R.chart k with he
    have hpos : ∀ y ∈ e.target, ∀ v, v ≠ 0 → 0 < Q y v := by
      intro y hy v hv
      obtain ⟨z, hz, hpz, w, hw, hcone, hnt⟩ := hL II Ψ K ι Ω E D O Lt X k y hy v hv
      have hs : X.M.proj z ∈ e.source := by rw [hpz]; exact e.map_target hy
      have hr := hrep z hz hs w v hw
      rw [hpz, e.right_inv hy] at hr
      rw [← hr]
      exact D.A'_pos.2 z hz w hcone hnt
    set S := (e '' closure (X.S.R.mid k)) ×ˢ Metric.sphere (0 : Fin D.n → ℂ) 1 with hS
    have hcpt : IsCompact S :=
      (isClosed_closure.isCompact.image_of_continuousOn
        (e.continuousOn.mono (X.S.R.closure_mid k))).prod (isCompact_sphere 0 1)
    have hsub : S ⊆ e.target ×ˢ Set.univ := by
      rintro ⟨y, u⟩ ⟨⟨x, hx, rfl⟩, -⟩
      exact ⟨e.map_source (X.S.R.closure_mid k hx), Set.mem_univ _⟩
    obtain ⟨c, hc, hcle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ S, c ≤ Q p.1 p.2 := by
      rcases S.eq_empty_or_nonempty with hE | hne
      · exact ⟨1, one_pos, by simp [hE]⟩
      · obtain ⟨p, hp, hmin⟩ := hcpt.exists_isMinOn hne (hcont.mono hsub)
        refine ⟨Q p.1 p.2, hpos p.1 (hsub hp).1 p.2 ?_, fun q hq => hmin hq⟩
        intro h0
        have h2 := hp.2
        rw [h0, Metric.mem_sphere, dist_self] at h2
        exact zero_ne_one h2
    refine ⟨c, hc, fun z hz w hm v hv => ?_⟩
    have hs : X.M.proj z ∈ e.source := X.S.R.mid_subset_source k hm
    have hy : e (X.M.proj z) ∈ e '' closure (X.S.R.mid k) := ⟨_, subset_closure hm, rfl⟩
    have h1 := hrep z hz hs w v hv
    rcases eq_or_ne v 0 with rfl | hv0
    · have h2 := hrep z hz hs _ _ (hv.real_smul 0)
      rw [levi_real_smul, smul_zero] at h2
      rw [h1, ← h2]
      simp
    · have hn : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h2 := hrep z hz hs _ _ (hv.real_smul ‖v‖⁻¹)
      rw [levi_real_smul] at h2
      have hu : (e (X.M.proj z), ‖v‖⁻¹ • v) ∈ S := by
        refine ⟨hy, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h3 := hcle _ hu
      rw [← h2] at h3
      calc c * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * levi (fun y => Real.log (D.A'.h y)) z w) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = levi (fun y => Real.log (D.A'.h y)) z w := by
          field_simp
  choose ck hck hmk using hk
  have hne : (insert 1 (Finset.univ.image ck)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨(insert 1 (Finset.univ.image ck)).min' hne, ?_, ?_⟩
  · rcases Finset.mem_insert.1 (Finset.min'_mem _ hne) with h | h
    · rw [h]
      exact one_pos
    · obtain ⟨k, -, hk⟩ := Finset.mem_image.1 h
      rw [← hk]
      exact hck k
  · intro z hz w k hm v hv
    exact le_trans (mul_le_mul_of_nonneg_right (Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ k)))) (by positivity)) (hmk k z hz w hm v hv)

end GroundTheory.Heights₂.Heights.LowerBoundFree
