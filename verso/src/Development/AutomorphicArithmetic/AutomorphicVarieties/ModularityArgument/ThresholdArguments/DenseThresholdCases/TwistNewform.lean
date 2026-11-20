import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.TwistNewform
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnramifiedAlgebraicWeights

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
open Polynomial Pointwise
namespace GlobalTheory.Ord2
open TwDet SrcForm
/- English proof (translation)
Establish `hl0 : 0 < l` using `hl.out.pos`. Take `⟨N, hN, hNk⟩` from `UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2) (Abelianization.commutator_subset_ker (dt W))`. Establish `hθN : KillsMu N (dt W)` using `fun s hs => hNk s hs`. Take `⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩` from `h.flag`. Use `set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef`.

Establish `hNl : 0 < N * l` using `Nat.mul_pos hN hl0`. Establish `hφ : KillsMu (N * l) φ` using `killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))`. Take `⟨g, hg⟩` from `hT l Ω ι e W hl2 he h (N * l) φ hNl hφ`. Establish `hVc : Continuous (tw W φ)` using `tw_cont h.cont (cont_of_kills hNl hφ)`. Establish `hVi : IsIrr (tw W φ)` using `irr_tw W φ _ h.irr`.

Establish `hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ)`. Take `⟨M, hM, hlev⟩` from `h.away`. Use `⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩` and prove the remaining obligations. Take `⟨B, hB, ψ, hψ, hd⟩` from `hlev w hw`. Conclude with `⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _)) (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩`.

Establish `hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ))`. Use `⟨N * l, hNl, ?_⟩` and prove the remaining obligations. Rewrite using `[dt_tw, pow_two]`. Conclude with `killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))`. Establish `hVf` using `flag_twist φ hfl`.

Establish `hVk : ∀ s : ↥(Dec (F` using `ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A → (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧ (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by`. Introduce `s hs`. Establish `h1 : dt W (s : G ℚ Ω) = 1` using `hine hs`. Take `⟨h0, h1'⟩` from `hk s hs`. Simplify using `only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one, one_mul, h0, h1', mul_inv_cancel_right, and_self]`.

Take `⟨π, hreg, hatt, hsat⟩` from `_root_.GlobalTheory.Ord2.SrcForm.exists_rep_alt P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg`. Take `⟨v, hv, hlv⟩` from `id hA`. Establish `hnv : normV v = l` using `normV_of_mem hl.out hlv`. Take `⟨Bs, hBs⟩` from `hS (N * l) φ hNl hφ A v _ hv hlv hVf hVk π hreg hatt`. Establish `hlev : ¬ l ∣ g.M` using `hnv ▸ _root_.GlobalTheory.NewLevel.not_dvd_level_of_satake_hecke_poly_cofinite P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs`.

Take `⟨σ, hσ⟩` from `exists_isFrob (Ω := Ω) hv`. Rewrite `hσ` using `[hnv]`. Take `⟨α, hroot, hα⟩` from `hF l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVd hA ⟨hVf, hVk⟩ hg hlev ⟨σ, hσ.1⟩ hσ`. Use `set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu`. Establish `hun : ‖(u : Qbar l)‖ = 1`.

Rewrite using `[hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]`. Establish `hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹` using `hα.imp id fun h => by rw [← h, inv_inv]`. Establish `hαn : ‖ι.symm α‖ = 1`. Break down `hα' with h1 | h1` into its components or cases. Rewrite using `[h1, RingEquiv.symm_apply_apply, hun]`.

Rewrite using `[h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]`. Take `⟨hal, hpow⟩` from `GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn`. Use `⟨⟨g, χ⁻¹, A, κ, hlev, hal, kills_inv hχ, ?_, hA, hfl, fun s hs => ?_⟩, fun A' κ' hA' hfl' => ?_⟩` and prove the remaining obligations. Rewrite `hg` using `[tw_tw]`. Rewrite using `[mul_assoc]`.

Conclude with `hg`. Establish `h1 : dt W (s : G ℚ Ω) = 1` using `hine hs`. Establish `h2 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ≠ 0` using `Units.ne_zero _`. Establish `h3 : (χ (s : G ℚ Ω) : Qbar l) ≠ 0` using `Units.ne_zero _`. Establish `h4 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) ≠ 0` using `zpow_ne_zero _ h2`.

Rewrite using `[(hk s hs).2, h1, MonoidHom.inv_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_one, inv_one, one_mul, zpow_neg]`. Clear the denominators using the available nonvanishing facts. Assume the negation of the conclusion as `hn push Not at hn`. Take `⟨m, hm, hχm⟩` from `pow_eq_one_of_kills hl0 hχ`. Take `⟨t, ht, htk⟩` from `cyc_inf hA`.

Take `⟨h0, h1⟩` from `hk ⟨t, Ine_le_Dec A ht⟩ ht`. Break down `eps_mem hA hA' hfl hfl' hn with hc | hc` into its components or cases. Rewrite `h0` using `[← hc]`. Simplify using `only at h0`. Establish `he1 : e = 1`.

Assume the negation of the conclusion as `hne`. Take `⟨d, rfl⟩ : ∃ d, e = d + 1` from `⟨e - 1, by omega⟩`. Use `htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_` and prove the remaining obligations. Establish `h2 : cycBar ℚ Ω l t ^ d * χ t = 1`. Rewrite `h0` using `[zpow_natCast, pow_succ', mul_assoc]`.

Conclude with `(left_eq_mul.1 h0)`. Rewrite using `[pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]`. Take `⟨m', hm', hφm⟩` from `pow_eq_one_of_kills hNl hφ`. Establish `hu' : u = φ σ`. Rewrite using `[hu, MonoidHom.mul_apply, ← hc, he1]`.

Simplify using `[mul_inv_cancel_comm]`. Establish `hu1 : ι (u : Qbar l) ^ m' = 1`. Rewrite using `[← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]`. Use `hpow m' hm' ?_` and prove the remaining obligations. Break down `hα' with h1 | h1` into its components or cases.

Rewrite using `[h1, hu1]`. Rewrite using `[h1, inv_pow, hu1, inv_one]`. Rewrite `h1` using `[← hc]`. Simplify using `only at h1`. Use `htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_` and prove the remaining obligations.

Establish `h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t`. Rewrite using `[pow_succ]`. Use `nth_rewrite 2 [h1]`. Rewrite using `[zpow_neg, zpow_natCast, mul_inv_cancel_left]`. Rewrite using `[pow_mul, h2, hχm]`.
-/
private theorem sources_of_spherical (P : _root_.UpperTheory.V.Af.HypothesesH') (hT : TwNewQ) (hF : UpperTheory.V.Z.Kato.WeilSphericalRecords.FrobRoot) (l : ℕ) [hl : Fact l.Prime] (Ω : Type) [Field Ω]
    [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l) (hl2 : l ≠ 2) (he : 1 ≤ e) (h : admitted ι e W)
    (hS : UpperTheory.V.Z.Kato.SphAt ι e W) : GlobalTheory.Ord2.SrcL ι e W := by
  have hl0 : 0 < l := hl.out.pos
  obtain ⟨N, hN, hNk⟩ := UpperTheory.V.CF.kwAbs Ω (dt W).ker (ker_open h.cont h.det2)
    (Abelianization.commutator_subset_ker (dt W))
  have hθN : KillsMu N (dt W) := fun s hs => hNk s hs
  obtain ⟨A, χ, κ, hA, hχ, hfl, hine, hk⟩ := h.flag
  set φ : G ℚ Ω →* (Qbar l)ˣ := (dt W)⁻¹ * χ⁻¹ with hφdef
  have hNl : 0 < N * l := Nat.mul_pos hN hl0
  have hφ : KillsMu (N * l) φ :=
    killsMu_mul (killsMu_dvd (kills_inv hθN) (dvd_mul_right N l)) (killsMu_dvd (kills_inv hχ) (dvd_mul_left l N))
  obtain ⟨g, hg⟩ := hT l Ω ι e W hl2 he h (N * l) φ hNl hφ
  have hVc : Continuous (tw W φ) := tw_cont h.cont (cont_of_kills hNl hφ)
  have hVi : IsIrr (tw W φ) := irr_tw W φ _ h.irr
  have hVa : ∃ M : ℕ, 1 ≤ M ∧ LevelAway l M (tw W φ) := by
    obtain ⟨M, hM, hlev⟩ := h.away
    refine ⟨M * (N * l), Nat.mul_pos hM hNl, fun w hw => ?_⟩
    obtain ⟨B, hB, ψ, hψ, hd⟩ := hlev w hw
    exact ⟨B, hB, fun i => ψ i * φ, fun i => killsMu_mul (killsMu_dvd (hψ i) (dvd_mul_right _ _))
      (killsMu_dvd hφ (dvd_mul_left _ _)), diag_twist φ hd⟩
  have hVd : ∃ M : ℕ, 1 ≤ M ∧ KillsMu M (dt (tw W φ)) := by
    refine ⟨N * l, hNl, ?_⟩
    rw [dt_tw, pow_two]
    exact killsMu_mul (killsMu_mul hφ hφ) (killsMu_dvd hθN (dvd_mul_right N l))
  have hVf := flag_twist φ hfl
  have hVk : ∀ s : ↥(Dec (F := ℚ) A), (s : G ℚ Ω) ∈ Ine (F := ℚ) A →
      (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (e : ℤ) ∧
      (κ 1 * φ.comp (Dec (F := ℚ) A).subtype) s = cycBar ℚ Ω l s ^ (-(e : ℤ)) := by
    intro s hs
    have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    obtain ⟨h0, h1'⟩ := hk s hs
    simp only [hφdef, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.inv_apply, Subgroup.coe_subtype, h1, inv_one,
      one_mul, h0, h1', mul_inv_cancel_right, and_self]
  obtain ⟨π, hreg, hatt, hsat⟩ := _root_.GlobalTheory.Ord2.SrcForm.exists_rep_alt P.toClassicalTheorems (by omega) g ι (tw W φ) (-(e : ℤ)) hg
  obtain ⟨v, hv, hlv⟩ := id hA
  have hnv : normV v = l := normV_of_mem hl.out hlv
  obtain ⟨Bs, hBs⟩ := hS (N * l) φ hNl hφ A v _ hv hlv hVf hVk π hreg hatt
  have hlev : ¬ l ∣ g.M := hnv ▸ _root_.GlobalTheory.NewLevel.not_dvd_level_of_satake_hecke_poly_cofinite P.toClassicalTheorems P.ssR _ (by omega) g _ π hsat v Bs hBs
  obtain ⟨σ, hσ⟩ := exists_isFrob (Ω := Ω) hv
  rw [hnv] at hσ
  obtain ⟨α, hroot, hα⟩ := hF l Ω ι e (tw W φ) A _ g hl2 he hVc hVi hVd hA ⟨hVf, hVk⟩ hg hlev ⟨σ, hσ.1⟩ hσ
  set u : (Qbar l)ˣ := (κ 0 * φ.comp (Dec (F := ℚ) A).subtype) ⟨σ, hσ.1⟩ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) with hu
  have hun : ‖(u : Qbar l)‖ = 1 := by
    rw [hu, Units.val_mul, norm_mul, norm_flag hVc hVf 0, Units.val_zpow_eq_zpow_val, norm_zpow, norm_cyc, one_zpow, one_mul]
  have hα' : α = ι (u : Qbar l) ∨ α = (ι (u : Qbar l))⁻¹ := hα.imp id fun h => by rw [← h, inv_inv]
  have hαn : ‖ι.symm α‖ = 1 := by
    rcases hα' with h1 | h1
    · rw [h1, RingEquiv.symm_apply_apply, hun]
    · rw [h1, map_inv₀, RingEquiv.symm_apply_apply, norm_inv, hun, inv_one]
  obtain ⟨hal, hpow⟩ := GlobalTheory.T.newform_unit_root_not_root_of_unity_odd_weight l ι e g α hl2 he hlev hroot hαn
  refine ⟨⟨g, χ⁻¹, A, κ, hlev, hal, kills_inv hχ, ?_, hA, hfl, fun s hs => ?_⟩, fun A' κ' hA' hfl' => ?_⟩
  · rw [tw_tw] at hg
    rw [mul_assoc]
    exact hg
  · have h1 : dt W (s : G ℚ Ω) = 1 := hine hs
    have h2 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h3 : (χ (s : G ℚ Ω) : Qbar l) ≠ 0 := Units.ne_zero _
    have h4 : (cycBar ℚ Ω l (s : G ℚ Ω) : Qbar l) ^ (e : ℤ) ≠ 0 := zpow_ne_zero _ h2
    rw [(hk s hs).2, h1, MonoidHom.inv_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
      Units.val_one, inv_one, one_mul, zpow_neg]
    field_simp
  · by_contra hn
    push Not at hn
    obtain ⟨m, hm, hχm⟩ := pow_eq_one_of_kills hl0 hχ
    obtain ⟨t, ht, htk⟩ := cyc_inf hA
    obtain ⟨h0, h1⟩ := hk ⟨t, Ine_le_Dec A ht⟩ ht
    rcases eps_mem hA hA' hfl hfl' hn with hc | hc
    · rw [← hc] at h0
      simp only at h0
      have he1 : e = 1 := by
        by_contra hne
        obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
        refine htk (d * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
        have h2 : cycBar ℚ Ω l t ^ d * χ t = 1 := by
          rw [zpow_natCast, pow_succ', mul_assoc] at h0
          exact (left_eq_mul.1 h0)
        rw [pow_mul, eq_inv_of_mul_eq_one_left h2, inv_pow, hχm, inv_one]
      obtain ⟨m', hm', hφm⟩ := pow_eq_one_of_kills hNl hφ
      have hu' : u = φ σ := by
        rw [hu, MonoidHom.mul_apply, ← hc, he1]
        simp [mul_inv_cancel_comm]
      have hu1 : ι (u : Qbar l) ^ m' = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, hu', hφm, Units.val_one, map_one]
      refine hpow m' hm' ?_
      rcases hα' with h1 | h1
      · rw [h1, hu1]
      · rw [h1, inv_pow, hu1, inv_one]
    · rw [← hc] at h1
      simp only at h1
      refine htk ((e + 1) * m) (Nat.mul_ne_zero (by omega) (by omega)) ?_
      have h2 : cycBar ℚ Ω l t ^ (e + 1) = χ t := by
        rw [pow_succ]
        nth_rewrite 2 [h1]
        rw [zpow_neg, zpow_natCast, mul_inv_cancel_left]
      rw [pow_mul, h2, hχm]
end GlobalTheory.Ord2
end
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win UpperTheory.V.Z.Kato UpperTheory.V.Z.Kato.WeilSphericalRecords UpperTheory.Zero.LLC
/- English proof (translation)
Introduce `P hT hF l _ Ω _ _ _ ι e W hl he hW hS` and use `GlobalTheory.Ord2.sources_of_spherical P hT hF l Ω ι e W hl he hW hS`.
-/
theorem UpperTheory.V.Z.Kato.WeilSphericalRecords.srcS_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → GlobalTheory.Ord2.TwNewQ → FrobRoot → SrcS :=
  fun P hT hF l _ Ω _ _ _ ι e W hl he hW hS => GlobalTheory.Ord2.sources_of_spherical P hT hF l Ω ι e W hl he hW hS
end
