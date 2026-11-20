import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormEvalSmulMulImRpowPolyDegreeSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormSlashHoloDecayStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerPeriodPolynomialLimitAtCuspStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitPolyOfPeriodicSlashFamilyConstStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalDiagPolyValuedInvariantTranslationTZpowMulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripEvalPolynomialDecayMulImRpowStatement

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Decay

/- English proof (translation)
Introduce `Γ hΓ σ`. Take `⟨n, hn, -, hmem⟩` from `Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero (σ * ModularGroup.T * σ⁻¹)`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `: (σ * ModularGroup.T * σ⁻¹) ^ n = σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹`. Rewrite using `[zpow_natCast, conj_pow]`.

Rewrite using `[← this]` and apply the resulting hypothesis.
-/
theorem per_exists : ∀ (Γ : Subgroup SL(2, ℤ)), Γ.FiniteIndex → ∀ σ : SL(2, ℤ), ∃ n : ℕ, 0 < n ∧ σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ := by
  intro Γ hΓ σ
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hΓ.index_ne_zero (σ * ModularGroup.T * σ⁻¹)
  refine ⟨n, hn, ?_⟩
  have : (σ * ModularGroup.T * σ⁻¹) ^ n = σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ := by
    rw [zpow_natCast, conj_pow]
  rwa [← this]

/- English proof (translation)
Unfold `eichler`. Use `Submodule.sum_mem _ fun j hj => ?_` and prove the remaining obligations. Rewrite using `[mem_degreeLT]`. Use `(degree_C_mul_X_pow_le _ _).trans_lt ?_` and prove the remaining obligations. Use `Finset.mem_range.1 hj` as an intermediate fact.

Conclude with `this` after adjusting the coercions.
-/
theorem eichler_mem (w : ℕ) (f : ℍ → ℂ) (τ : ℍ) : eichler w f τ ∈ degreeLT ℂ (w + 1) := by
  unfold eichler
  refine Submodule.sum_mem _ fun j hj => ?_
  rw [mem_degreeLT]
  refine (degree_C_mul_X_pow_le _ _).trans_lt ?_
  have := Finset.mem_range.1 hj
  exact_mod_cast this

/- English proof (translation)
Establish `h1` using `heq ⟨_, hγ⟩ (σ • τ)`. Establish `h2 : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) • σ • τ = σ • (ModularGroup.T ^ (n : ℤ) • τ)`. Simplify using `only [← mul_smul]`. Use `congr 1`. Use `group`.

Rewrite `h1` using `[h2]`. Rewrite using `[← h1]`. Establish `hm' : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ)`. Simplify using `only [Subgroup.coe_mk]`. Use `group`.

Establish `e1 : slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) = slP w (mat (σ * ModularGroup.T ^ (n : ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))`. Rewrite using `[show mat (σ * ModularGroup.T ^ (n : ℤ)) = mat σ * mat (ModularGroup.T ^ (n : ℤ)) from Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]`. Establish `e2 : slP w (mat σ) (slP w (mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) = slP w (mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ)) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))`. Rewrite using `[show mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ) = mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * mat σ from Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]`. Rewrite using `[e1, e2, hm']`.
-/
theorem per_cov (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (U : ℍ → ℂ[X]) (hU : ∀ τ, U τ ∈ degreeLT ℂ (w + 1))
    (heq : ∀ (γ : Γ) (τ : ℍ), slP w (mat γ) (U ((γ : SL(2, ℤ)) • τ)) = U τ) (σ : SL(2, ℤ)) (n : ℕ)
    (hγ : σ * ModularGroup.T ^ (n : ℤ) * σ⁻¹ ∈ Γ) (τ : ℍ) :
    slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • (ModularGroup.T ^ (n : ℤ) • τ)))) =
      slP w (mat σ) (U (σ • τ)) := by
  have h1 := heq ⟨_, hγ⟩ (σ • τ)
  have h2 : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) • σ • τ = σ • (ModularGroup.T ^ (n : ℤ) • τ) := by
    simp only [← mul_smul]; congr 1; group
  rw [h2] at h1
  rw [← h1]
  have hm' : ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ = σ * ModularGroup.T ^ (n : ℤ) := by
    simp only [Subgroup.coe_mk]; group
  have e1 : slP w (mat (ModularGroup.T ^ (n : ℤ))) (slP w (mat σ) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (σ * ModularGroup.T ^ (n : ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (σ * ModularGroup.T ^ (n : ℤ)) = mat σ * mat (ModularGroup.T ^ (n : ℤ)) from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  have e2 : slP w (mat σ) (slP w (mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ))) (U (σ • ModularGroup.T ^ (n : ℤ) • τ))) =
      slP w (mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ)) (U (σ • ModularGroup.T ^ (n : ℤ) • τ)) := by
    rw [show mat (((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * σ) = mat ((⟨_, hγ⟩ : Γ) : SL(2, ℤ)) * mat σ from
      Matrix.SpecialLinearGroup.coe_mul _ _, (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w _ _ _ (hU _)).2.1]
  rw [e1, e2, hm']

/- English proof (translation)
Introduce `Γ k hΓ hk f h p hp hequiv σ`. Establish `hk2 : 2 ≤ k` using `by omega`. Use `set w := k - 2 with hw`. Establish `hw1 : 1 ≤ w` using `by omega`. Use `set U : ℍ → ℂ[X] := fun τ => eichler w ⇑f τ - (eichler w ⇑h τ).map (starRingEnd ℂ) - p with hU`.

Establish `hpw : p ∈ degreeLT ℂ (w + 1)`. Rewrite using `[show w + 1 = k - 1 by omega]` and apply the resulting hypothesis. Establish `hUdeg : ∀ τ, U τ ∈ degreeLT ℂ (w + 1)`. Introduce `τ`. Use `Submodule.sub_mem _ (Submodule.sub_mem _ (eichler_mem w _ τ) ?_) hpw` and prove the remaining obligations.

Establish `h0` using `eichler_mem w (⇑h) τ`. Rewrite `h0`, the goal using `[mem_degreeLT]`. Conclude with `(degree_map_le).trans_lt h0`. Use `set V : ℍ → ℂ[X] := fun τ => slP w (mat σ) (U (σ • τ)) with hV`. Establish `hVdeg : ∀ τ, V τ ∈ degreeLT ℂ (w + 1)` using `fun τ => (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat σ) 1 _ (hUdeg _)).1`.

Establish `hexp : (-((k : ℝ) - 2) / 2) = -(w : ℝ) / 2`. Rewrite using `[hw, Nat.cast_sub hk2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hfun : (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) = fun τ => ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2)`.

Use function extensionality and compare the values at `τ`. Rewrite using `[hexp]`. Conclude with `GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash w σ (U (σ • τ)) τ (hUdeg _)`. Express the relevant statement in the definitionally equal form `Filter.Tendsto (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) _ _`. Rewrite using `[hfun]`.

Take `⟨n, hn, hγ⟩` from `per_exists Γ hΓ σ`. Establish `hVper : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ` using `fun τ => per_cov Γ w U hUdeg hequiv σ n hγ τ`. Take `⟨hfd, Cf, cf, hcf, hfb⟩` from `GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ f σ`. Take `⟨hhd, Ch, ch, hch, hhb⟩` from `GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ h σ`. Take `⟨Q, C', c, hQ, hc, hQb⟩` from `GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp k (⇑f) (⇑h) p σ Cf cf Ch ch hk2 hcf hch (CuspFormClass.holo f) (CuspFormClass.holo h) hfd hhd hfb hhb hp`.

Establish `hQb' : ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w` using `hQb`. Establish `hQc` using `GlobalTheory.T.limit_poly_of_periodic_slash_family_const w n V Q C' c hn hc hQ hVdeg hVper hQb'`. Rewrite `hQb'` using `[hQc]`. Rewrite using `[Metric.tendsto_nhds]`. Introduce `ε hε`.

Take `⟨A, hA⟩` from `GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow w n (Q.coeff 0) V C' c hw1 hc hVdeg hQb' ε hε`. Use `(atImInfty_mem _).2 ⟨A, fun τ hτ => ?_⟩` and prove the remaining obligations. Establish `hnR : (0 : ℝ) < n` using `by exact_mod_cast hn`. Use `set m : ℤ := -⌊τ.re / n⌋ with hm`. Use `set τ' : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • τ with hτ'`.

Establish `hτ'v : τ' = ((((n : ℤ) * m : ℤ)) : ℝ) +ᵥ τ` using `modular_T_zpow_smul τ _`. Establish `hre : τ'.re = τ.re + n * m`. Rewrite using `[hτ'v]`. Simplify using `[add_comm]`. Establish `him : τ'.im = τ.im`.

Rewrite using `[hτ'v]`. Simplify using the standard rewrite rules. Establish `hg` using `GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul w n V hVdeg hVper m τ`. Establish `hfl1 : (⌊τ.re / n⌋ : ℝ) ≤ τ.re / n` using `Int.floor_le _`. Establish `hfl2 : τ.re / n < ⌊τ.re / n⌋ + 1` using `Int.lt_floor_add_one _`.

Establish `hr1 : 0 ≤ τ'.re`. Rewrite using `[hre, hm]`. Use `push_cast`. Use `(le_div_iff₀ hnR).1 hfl1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hr2 : τ'.re ≤ n`. Rewrite using `[hre, hm]`. Use `push_cast`. Use `(div_lt_iff₀ hnR).1 hfl2` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Use `hA τ' (him ▸ hτ) hr1 hr2` as an intermediate fact. Rewrite `this` using `[hg, him]`. Simplify using `only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]`. Rewrite using `[abs_of_nonneg (by positivity)]`. Conclude with `this`.
-/
theorem decay_at_cusp : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℕ), Γ.FiniteIndex → 3 ≤ k → ∀ (f h : CuspForm Γ (k : ℤ)) (p : ℂ[X]), p ∈ degreeLT ℂ (k - 1) → (∀ (γ : Γ) (τ : ℍ), slP (k - 2) (mat γ) (eichler (k - 2) ⇑f ((γ : SL(2, ℤ)) • τ) - (eichler (k - 2) ⇑h ((γ : SL(2, ℤ)) • τ)).map (starRingEnd ℂ) - p) = eichler (k - 2) ⇑f τ - (eichler (k - 2) ⇑h τ).map (starRingEnd ℂ) - p) → ∀ σ : SL(2, ℤ), Filter.Tendsto (fun τ : ℍ => ‖(eichler (k - 2) ⇑f (σ • τ) - (eichler (k - 2) ⇑h (σ • τ)).map (starRingEnd ℂ) - p).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) UpperHalfPlane.atImInfty (nhds 0) := by
  intro Γ k hΓ hk f h p hp hequiv σ
  have hk2 : 2 ≤ k := by omega
  set w := k - 2 with hw
  have hw1 : 1 ≤ w := by omega
  set U : ℍ → ℂ[X] := fun τ =>
    eichler w ⇑f τ - (eichler w ⇑h τ).map (starRingEnd ℂ) - p with hU
  have hpw : p ∈ degreeLT ℂ (w + 1) := by
    rwa [show w + 1 = k - 1 by omega]
  have hUdeg : ∀ τ, U τ ∈ degreeLT ℂ (w + 1) := by
    intro τ
    refine Submodule.sub_mem _ (Submodule.sub_mem _ (eichler_mem w _ τ) ?_) hpw
    have h0 := eichler_mem w (⇑h) τ
    rw [mem_degreeLT] at h0 ⊢
    exact (degree_map_le).trans_lt h0
  set V : ℍ → ℂ[X] := fun τ => slP w (mat σ) (U (σ • τ)) with hV
  have hVdeg : ∀ τ, V τ ∈ degreeLT ℂ (w + 1) := fun τ => (GlobalTheory.T.polyDegreeSlashAction_right_action_properties w (mat σ) 1 _ (hUdeg _)).1
  have hexp : (-((k : ℝ) - 2) / 2) = -(w : ℝ) / 2 := by
    rw [hw, Nat.cast_sub hk2]; push_cast; ring
  have hfun : (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ * (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) =
      fun τ => ‖(V τ).eval (τ : ℂ)‖ * τ.im ^ (-(w : ℝ) / 2) := by
    funext τ; rw [hexp]; exact GlobalTheory.T.norm_eval_smul_mul_im_rpow_polyDegreeSlash w σ (U (σ • τ)) τ (hUdeg _)
  change Filter.Tendsto (fun τ : ℍ => ‖(U (σ • τ)).eval ((σ • τ : ℍ) : ℂ)‖ *
    (σ • τ).im ^ (-((k : ℝ) - 2) / 2)) _ _
  rw [hfun]
  obtain ⟨n, hn, hγ⟩ := per_exists Γ hΓ σ
  have hVper : ∀ τ : ℍ, slP w (mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ :=
    fun τ => per_cov Γ w U hUdeg hequiv σ n hγ τ
  obtain ⟨hfd, Cf, cf, hcf, hfb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ f σ
  obtain ⟨hhd, Ch, ch, hch, hhb⟩ := GlobalTheory.T.cuspForm_slash_mdifferentiable_and_exp_decay Γ k hΓ h σ
  obtain ⟨Q, C', c, hQ, hc, hQb⟩ := GlobalTheory.T.eichlerPeriodPolynomial_limit_at_cusp k (⇑f) (⇑h) p σ Cf cf Ch ch hk2 hcf hch
    (CuspFormClass.holo f) (CuspFormClass.holo h) hfd hhd hfb hhb hp
  have hQb' : ∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w :=
    hQb
  have hQc := GlobalTheory.T.limit_poly_of_periodic_slash_family_const w n V Q C' c hn hc hQ hVdeg hVper hQb'
  rw [hQc] at hQb'
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨A, hA⟩ := GlobalTheory.T.strip_eval_polynomial_decay_mul_im_rpow w n (Q.coeff 0) V C' c hw1 hc hVdeg hQb' ε hε
  refine (atImInfty_mem _).2 ⟨A, fun τ hτ => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℤ := -⌊τ.re / n⌋ with hm
  set τ' : ℍ := ModularGroup.T ^ ((n : ℤ) * m) • τ with hτ'
  have hτ'v : τ' = ((((n : ℤ) * m : ℤ)) : ℝ) +ᵥ τ := modular_T_zpow_smul τ _
  have hre : τ'.re = τ.re + n * m := by
    rw [hτ'v]; simp [add_comm]
  have him : τ'.im = τ.im := by
    rw [hτ'v]; simp
  have hg := GlobalTheory.T.evalDiag_polyValued_invariant_translation_T_zpow_mul w n V hVdeg hVper m τ
  have hfl1 : (⌊τ.re / n⌋ : ℝ) ≤ τ.re / n := Int.floor_le _
  have hfl2 : τ.re / n < ⌊τ.re / n⌋ + 1 := Int.lt_floor_add_one _
  have hr1 : 0 ≤ τ'.re := by
    rw [hre, hm]; push_cast
    have := (le_div_iff₀ hnR).1 hfl1
    nlinarith
  have hr2 : τ'.re ≤ n := by
    rw [hre, hm]; push_cast
    have := (div_lt_iff₀ hnR).1 hfl2
    nlinarith
  have := hA τ' (him ▸ hτ) hr1 hr2
  rw [hg, him] at this
  simp only [Set.mem_setOf_eq, Real.dist_eq, sub_zero]
  rw [abs_of_nonneg (by positivity)]
  exact this

end GlobalTheory.HeckeFamilyMatrices.Decay
