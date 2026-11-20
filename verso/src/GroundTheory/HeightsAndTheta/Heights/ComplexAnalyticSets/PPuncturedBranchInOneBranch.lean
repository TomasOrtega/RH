import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPuncturedBranchInOneBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchImageNhdOffCentre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Establish `hH : IsPreconnected {z : ℂ | z.re < Real.log R}` using `(convex_halfSpace_re_lt _).isPreconnected`. Establish `himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0}`. Use extensionality with `w`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Use `⟨?_, Complex.exp_ne_zero z⟩` and prove the remaining obligations. Rewrite using `[Complex.norm_exp]`. Conclude with `(Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)`. Introduce and unpack `⟨hw, hw0⟩`.

Use `⟨Complex.log w, ?_, Complex.exp_log hw0⟩` and prove the remaining obligations. Rewrite using `[Complex.log_re]`. Conclude with `Real.log_lt_log (norm_pos_iff.2 hw0) hw`. Rewrite using `[← himage]`. Conclude with `hH.image _ Complex.continuous_exp.continuousOn`.
-/
theorem isPreconnected_punctured_ball {R : ℝ} (hR : 0 < R) :
    IsPreconnected (Metric.ball (0 : ℂ) R \ {0}) := by
  have hH : IsPreconnected {z : ℂ | z.re < Real.log R} := (convex_halfSpace_re_lt _).isPreconnected
  have himage : Complex.exp '' {z : ℂ | z.re < Real.log R} = Metric.ball (0 : ℂ) R \ {0} := by
    ext w
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_sdiff, Metric.mem_ball, dist_zero_right,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero z⟩
      rw [Complex.norm_exp]
      exact (Real.exp_lt_exp.2 hz).trans_eq (Real.exp_log hR)
    · rintro ⟨hw, hw0⟩
      refine ⟨Complex.log w, ?_, Complex.exp_log hw0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.2 hw0) hw
  rw [← himage]
  exact hH.image _ Complex.continuous_exp.continuousOn

/- English proof (translation)
Introduce `n I q m c ν ρ _ hdim hρ hcov hdisj`. Take `⟨N, hN, hNc⟩` from `h₁ n I q hdim`. Establish `hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖` using `fun τ ↦ by simp [pi_norm_const]`. Establish `hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius` using `fun τ hτ ↦ by`. Rewrite using `[Metric.mem_ball, dist_zero_right, hnorm]` and apply the resulting hypothesis.

Establish `h0r : ‖(0 : ℂ)‖ < ν.radius` using `by simpa using ν.radius_pos`. Establish `hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ` using `fun τ hτ ↦ (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt`. Establish `hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q` using `ν.map_zero`. Establish `hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N` using `(hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)`. Take `⟨ε, hε, hεN⟩` from `Metric.eventually_nhds_iff.1 hev`.

Take `⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius` from `⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩`. Set `D : Set ℂ` to `Metric.ball 0 R \ {0}`. Establish `hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R` using `fun τ hτ ↦ ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩`. Establish `hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q`. Introduce `τ hτ h`.

Establish `h'` using `ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)`. Conclude with `(norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)`. Set `Vb : Fin m → Set ℂ` to `fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image`. Establish `hDo : IsOpen D` using `Metric.isOpen_ball.sdiff isClosed_singleton`. Establish `hVo : ∀ b, IsOpen (Vb b)`.

Introduce `b`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce and unpack `τ ⟨hτD, hτb⟩`. Establish `hτN : ν.toFun (fun _ ↦ τ) ∈ N` using `hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)`. Take `⟨U, hU, hUc⟩` from `hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)`.

Use `filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU] with σ hσD hσU`. Conclude with `⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩`. Establish `hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b')` using `fun b b' hbb ↦ Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)`. Establish `hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b` using `fun τ hτ ↦ by`. Take `⟨b, hb⟩` from `Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))`.

Conclude with `⟨b, hτ, hb⟩`. Establish `hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[hR0.ne']`. Take `⟨b, hb⟩` from `hcovD _ hτ₀`. Establish `hsub : D ⊆ Vb b`. Use `(isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b) (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩` and prove the remaining obligations. Conclude with `Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')`.

Introduce `τ hτ`. Take `⟨b', hb'⟩` from `hcovD τ hτ`. Distinguish the cases in `h : b' = b`. Conclude with `Or.inl (h ▸ hb')`. Conclude with `Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)`.

Use `⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_ball, dist_zero_right]` and apply the resulting hypothesis. Simplify using `using norm_pos_iff.1 hτ0`.
-/
theorem PuncturedBranchInOneBranch.proof (h₁ : BranchImageNhdOffCentre.Statement) :
    PuncturedBranchInOneBranch.Statement := by
  intro n I q m c ν ρ _ hdim hρ hcov hdisj
  obtain ⟨N, hN, hNc⟩ := h₁ n I q hdim
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]
  have hball : ∀ τ : ℂ, ‖τ‖ < ν.radius → (fun _ ↦ τ : Fin 1 → ℂ) ∈ Metric.ball 0 ν.radius := fun τ hτ ↦ by
    rwa [Metric.mem_ball, dist_zero_right, hnorm]
  have h0r : ‖(0 : ℂ)‖ < ν.radius := by simpa using ν.radius_pos

  have hcont : ∀ τ : ℂ, ‖τ‖ < ν.radius → ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) τ := fun τ hτ ↦
    (ν.differentiableOn.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds (hball τ hτ))).comp
      (f := fun τ : ℂ ↦ (fun _ ↦ τ : Fin 1 → ℂ)) (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N :=
    (hcont 0 h0r).preimage_mem_nhds (by show N ∈ 𝓝 (ν.toFun fun _ ↦ (0 : ℂ)); rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  obtain ⟨R, hR0, hRρ, hRε, hRν⟩ : ∃ R, 0 < R ∧ R ≤ ρ ∧ R ≤ ε ∧ R ≤ ν.radius :=
    ⟨min ρ (min ε ν.radius), lt_min hρ (lt_min hε ν.radius_pos), min_le_left _ _,
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  let D : Set ℂ := Metric.ball 0 R \ {0}
  have hD : ∀ τ ∈ D, 0 < ‖τ‖ ∧ ‖τ‖ < R := fun τ hτ ↦
    ⟨norm_pos_iff.2 (by simpa using hτ.2), by simpa using hτ.1⟩
  have hne : ∀ τ ∈ D, ν.toFun (fun _ ↦ τ) ≠ q := by
    intro τ hτ h
    have h' := ν.injOn (hball τ ((hD τ hτ).2.trans_le hRν)) (hball 0 h0r) (h.trans hq.symm)
    exact (norm_pos_iff.1 (hD τ hτ).1) (by simpa using congrFun h' 0)

  let Vb : Fin m → Set ℂ := fun b ↦ D ∩ (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) ⁻¹' (c b).image
  have hDo : IsOpen D := Metric.isOpen_ball.sdiff isClosed_singleton
  have hVo : ∀ b, IsOpen (Vb b) := by
    intro b
    rw [isOpen_iff_mem_nhds]
    rintro τ ⟨hτD, hτb⟩
    have hτN : ν.toFun (fun _ ↦ τ) ∈ N := hεN (by rw [dist_zero_right]; exact (hD τ hτD).2.trans_le hRε)
    obtain ⟨U, hU, hUc⟩ := hNc (c b) _ ⟨hτb, hτN⟩ (hne τ hτD)
    filter_upwards [hDo.mem_nhds hτD, (hcont τ ((hD τ hτD).2.trans_le hRν)).preimage_mem_nhds hU]
      with σ hσD hσU
    exact ⟨hσD, hUc ⟨ν.mapsTo (hball σ ((hD σ hσD).2.trans_le hRν)), hσU⟩⟩
  have hVd : ∀ b b', b ≠ b' → Disjoint (Vb b) (Vb b') := fun b b' hbb ↦
    Set.disjoint_left.2 fun τ hτ hτ' ↦ hne τ hτ.1 (hdisj b b' hbb ⟨hτ.2, hτ'.2⟩)
  have hcovD : ∀ τ ∈ D, ∃ b, τ ∈ Vb b := fun τ hτ ↦ by
    obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hcov τ (hD τ hτ).1 ((hD τ hτ).2.trans_le hRρ))
    exact ⟨b, hτ, hb⟩

  have hτ₀ : ((R / 2 : ℝ) : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    · simp [hR0.ne']
  obtain ⟨b, hb⟩ := hcovD _ hτ₀
  have hsub : D ⊆ Vb b := by
    refine (isPreconnected_punctured_ball hR0).subset_left_of_subset_union (hVo b)
      (isOpen_iUnion fun b' ↦ isOpen_iUnion fun (_ : b' ≠ b) ↦ hVo b') ?_ ?_ ⟨_, hτ₀, hb⟩
    · exact Set.disjoint_iUnion_right.2 fun b' ↦ Set.disjoint_iUnion_right.2 fun hb' ↦ hVd b b' (Ne.symm hb')
    · intro τ hτ
      obtain ⟨b', hb'⟩ := hcovD τ hτ
      by_cases h : b' = b
      · exact Or.inl (h ▸ hb')
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨b', h, hb'⟩)
  refine ⟨b, R, hR0, fun τ hτ0 hτR ↦ (hsub ⟨?_, ?_⟩).2⟩
  · rwa [Metric.mem_ball, dist_zero_right]
  · simpa using norm_pos_iff.1 hτ0

end GroundTheory.Heights₂.Heights
