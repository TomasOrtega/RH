import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoOfCoboundary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFineInvariantFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricChartsPolarizedModel
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.HodgeDominates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
Take `⟨φs, hs, -⟩` from `hS (max 1 (Module.finrank ℚ E * min Dw.p Dw.q)) (le_max_left _ _)`. Take `⟨φ, h₁, h₂, -⟩` from `GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)`. Take `⟨Y', BD, d, k, -, hk, hsm, -, hBD, -, hamp⟩` from `hF E H Dw hr φ h₁ h₂ l Xo c`. Establish `hY'` using `GlobalTheory.FanTheta.isLB_detOm_of_smooth Y' hr hsm`. Take `⟨N, _, _, u, p, p', hu, hu', hp, hpt, e⟩` from `exists_common_modification hE Y Y' hY hY'`.

Establish `e₁ : p (u w) = Y.j w` using `by rw [← hu]; rfl`. Establish `e₂ : p' (u w) = Y'.j w` using `by rw [← hu']; rfl`. Rewrite using `[← e₁]`. Use `exists_sec_of_common p p' hp (u w) (fun W hW => ⟨Y'.j ''ᵁ (Y.j ⁻¹ᵁ W), ⟨w, (show Y.j w ∈ W from e₁ ▸ hW), e₂.symm⟩, ?_⟩) hY hY' (hamp hY') BD.isLB_lb e hk ?_ BD.canonical ?_ hA` and prove the remaining obligations. Introduce and unpack `n ⟨w', hw', h⟩ show p n ∈ W`.

Rewrite using `[hpt n w' h.symm]`. Conclude with `hw'`. Establish `h` using `cls_tens (isLB_lbPow hY' k) (isLB_dual BD.isLB_lb) (hamp hY').isLB`. Rewrite `h` using `[cls_lbPow hY', cls_dual BD.isLB_lb]`. Conclude with `(congrArg (· + _) h).trans (by abel)`.

Rewrite using `[← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical, e₂]`. Use `fun h => hBD _ h ?_` and prove the remaining obligations. Establish `h' : Y'.jQ w ∈ pullback.fst Y'.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y'.t.G`. Rewrite using `[Y'.ab_gen]`. Conclude with `⟨w, rfl⟩`.

Conclude with `h'`.
-/
theorem exists_sec_detOm (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (hr : 1 ≤ Dw.p + Dw.q) (Y : Model Xo c (RingHom.id c.F))
    (hY : (FlagMod.detOm Y).IsLB) (w : Xo.XF c) {A : LB Y.X} (hA : A.IsLB) :
    ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow (FlagMod.detOm Y) m) A).Sec, Y.j w ∈ nonzeroLocus s := by
  obtain ⟨φs, hs, -⟩ := hS (max 1 (Module.finrank ℚ E * min Dw.p Dw.q)) (le_max_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hs (le_max_right _ _) ∅ (by simp)
  obtain ⟨Y', BD, d, k, -, hk, hsm, -, hBD, -, hamp⟩ := hF E H Dw hr φ h₁ h₂ l Xo c
  have hY' := GlobalTheory.FanTheta.isLB_detOm_of_smooth Y' hr hsm
  obtain ⟨N, _, _, u, p, p', hu, hu', hp, hpt, e⟩ := exists_common_modification hE Y Y' hY hY'
  have e₁ : p (u w) = Y.j w := by rw [← hu]; rfl
  have e₂ : p' (u w) = Y'.j w := by rw [← hu']; rfl
  rw [← e₁]
  refine exists_sec_of_common p p' hp (u w) (fun W hW => ⟨Y'.j ''ᵁ (Y.j ⁻¹ᵁ W), ⟨w, (show Y.j w ∈ W from e₁ ▸ hW), e₂.symm⟩, ?_⟩) hY hY'
    (hamp hY') BD.isLB_lb e hk ?_ BD.canonical ?_ hA
  · rintro n ⟨w', hw', h⟩
    show p n ∈ W
    rw [hpt n w' h.symm]
    exact hw'
  · have h := cls_tens (isLB_lbPow hY' k) (isLB_dual BD.isLB_lb) (hamp hY').isLB
    rw [cls_lbPow hY', cls_dual BD.isLB_lb] at h
    exact (congrArg (· + _) h).trans (by abel)
  · rw [← SetLike.mem_coe, BD.coe_nonzeroLocus_canonical, e₂]
    refine fun h => hBD _ h ?_
    have h' : Y'.jQ w ∈ pullback.fst Y'.s (spMap (RingHom.id c.F)) ⁻¹' abLocus Y'.t.G := by
      rw [Y'.ab_gen]; exact ⟨w, rfl⟩
    exact h'

/- English proof (translation)
Use `TF.smooth` as an intermediate fact. Break down `Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hr` into its components or cases. Establish `hd : Dw.dim = 0` using `by rw [Datum.dim, show Dw.q = 0 by omega, mul_zero]`. Rewrite `this` using `[hd]`. Establish `: Etale TF.Y.s` using `(Etale.iff_smoothOfRelativeDimension_zero _).2 this`.

Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver TF.Y.proj` as an intermediate fact. Use `GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified TF.Y.s` as an intermediate fact. Use `IsFinite.of_isProper_of_locallyQuasiFinite TF.Y.s` as an intermediate fact. Establish `: IsAffine TF.Y.X` using `isAffine_of_isAffineHom TF.Y.s`. Use `⟨_, LB.isLB_triv _, ?_, fun w A hA => ⟨1, one_pos, ?_⟩⟩` and prove the remaining obligations.

Establish `he : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = 0`. Rewrite using `[FlagMod.unitaryWeightExponentVector_signatureWeightMuZero]`. Use function extensionality and compare the values at `ix`. Break down `ix with _ | ⟨σ, i⟩` into its components or cases. Both sides reduce to the same expression.

Use `i.2` as an intermediate fact. Apply the tactic sequence `have : Dw.mult σ = 0 := by unfold Datum.mult; split_ifs <;> omega`. Use linear arithmetic over natural numbers and integers. Use `Eq.trans (b := 0) ((cls_eq_zero_iff _).2 ⟨⟨fun _ => 1⟩, fun k k' => ?_⟩) (map_zero _).symm` and prove the remaining obligations. Establish `hg : (TF.X.Llam (FlagMod.mu0 Dw)).g k k' = 1` using `Finset.prod_eq_one fun ix _ => by rw [he]; exact zpow_zero _`.

Rewrite using `[hg, map_one, map_one, mul_one]`. Take `⟨s, hs, -⟩` from `exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_div (isLB_lbPow (LB.isLB_triv _) 1) hA) (Set.finite_singleton (TF.Y.j w)) (U := ⊤) (Set.subset_univ _)`. Conclude with `⟨s, hs rfl⟩`. Establish `hY` using `GlobalTheory.FanTheta.isLB_detOm_of_smooth TF.Y hr ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) this)`. Use `⟨_, hY, ?_, fun w A hA => exists_sec_detOm hE hS hF hr TF.Y hY w hA⟩` and prove the remaining obligations.

Rewrite using `[← cls_pull hY _ (pull_isLB hY _), ← (cls_eq_iff TF.X.F.isLB_detOm _).2 (TF.X.F.detOm_iso_pull hY)]`. Conclude with `((cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)).symm`.
-/
theorem exists_lb_dominates (hE : GlobalTheory.Published.SemiAbelianHomExtension) (hS : GlobalTheory.Published.SiegelToroidalIntegral)
    (hF : GlobalTheory.Published.ToroidalChartsForFan) (TF : TorFlag Xo c) :
    ∃ (ω : LB TF.Y.X) (hω : ω.IsLB), cls _ (TF.X.isLB_Llam (FlagMod.mu0 Dw)) = CechPic.pull TF.X.π (cls ω hω) ∧
      ∀ (w : Xo.XF c) (A : LB TF.Y.X), A.IsLB →
        ∃ m : ℕ, 0 < m ∧ ∃ s : (LB.div (lbPow ω m) A).Sec, TF.Y.j w ∈ nonzeroLocus s := by
  have := TF.smooth
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hr
  · have hd : Dw.dim = 0 := by rw [Datum.dim, show Dw.q = 0 by omega, mul_zero]
    rw [hd] at this
    have : Etale TF.Y.s := (Etale.iff_smoothOfRelativeDimension_zero _).2 this
    have := GlobalTheory.ThetaDescent.isProper_of_isProjOver TF.Y.proj
    have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified TF.Y.s
    have := IsFinite.of_isProper_of_locallyQuasiFinite TF.Y.s
    have : IsAffine TF.Y.X := isAffine_of_isAffineHom TF.Y.s
    refine ⟨_, LB.isLB_triv _, ?_, fun w A hA => ⟨1, one_pos, ?_⟩⟩
    · have he : AllWt.exOf Dw (FlagMod.mu0 Dw) 0 = 0 := by
        rw [FlagMod.unitaryWeightExponentVector_signatureWeightMuZero]
        funext ix
        rcases ix with _ | ⟨σ, i⟩
        · rfl
        · have := i.2
          have : Dw.mult σ = 0 := by unfold Datum.mult; split_ifs <;> omega
          omega
      refine Eq.trans (b := 0) ((cls_eq_zero_iff _).2 ⟨⟨fun _ => 1⟩, fun k k' => ?_⟩) (map_zero _).symm
      have hg : (TF.X.Llam (FlagMod.mu0 Dw)).g k k' = 1 :=
        Finset.prod_eq_one fun ix _ => by rw [he]; exact zpow_zero _
      rw [hg, map_one, map_one, mul_one]
    · obtain ⟨s, hs, -⟩ := exists_sec_finite_subset_of_isQuasiAffine (LB.isLB_div (isLB_lbPow (LB.isLB_triv _) 1) hA)
        (Set.finite_singleton (TF.Y.j w)) (U := ⊤) (Set.subset_univ _)
      exact ⟨s, hs rfl⟩
  · have hY := GlobalTheory.FanTheta.isLB_detOm_of_smooth TF.Y hr
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) this)
    refine ⟨_, hY, ?_, fun w A hA => exists_sec_detOm hE hS hF hr TF.Y hY w hA⟩
    rw [← cls_pull hY _ (pull_isLB hY _), ← (cls_eq_iff TF.X.F.isLB_detOm _).2 (TF.X.F.detOm_iso_pull hY)]
    exact ((cls_eq_iff _ _).2 (FlagHodge.lbIso_detOm_Llam TF.X)).symm

/- English proof (translation)
Introduce `hP _ hS hF E _ _ _ H Dw l Xo c TF Z _`. Take `⟨ω, hω, e, h⟩` from `exists_lb_dominates hP.p22 hS hF TF`. Use `⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y` from `hy`. Take `⟨m, hm, s, hs⟩` from `h w A hA`.

Establish `hD` using `LB.isLB_div (isLB_lbPow hω m) hA`. Establish `hL` using `isLB_L₀ TF.X Z (FlagMod.mu0 Dw)`. Establish `hT` using `LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))`. Establish `e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω)`. Rewrite using `[CechPic.pull_comp, ← e]`.

Conclude with `cls_pull (TF.X.isLB_Llam _) _ _`. Take `⟨t, ht⟩` from `exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π)) ((cls_eq_iff hT (pull_isLB hD _)).1 (by`. Rewrite using `[cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD, cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)`. Use `⟨m, t, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[ht, nonzeroLocus_lbSecPull]`.

Conclude with `(hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)`.
-/
theorem exists_weight_dominates : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ χ : AllWt.Weight Dw, ∀ y ∈ U₀ TF.X Z, ∀ A : LB TF.Y.X, A.IsLB → ∃ (m : ℕ) (s : (LB.div (lbPow (L₀ TF.X Z χ) m) (A.pull (inc₀ TF.X Z ≫ TF.X.π))).Sec), 0 < m ∧ y ∈ nonzeroLocus s := by
  intro hP _ hS hF E _ _ _ H Dw l Xo c TF Z _
  obtain ⟨ω, hω, e, h⟩ := exists_lb_dominates hP.p22 hS hF TF
  refine ⟨FlagMod.mu0 Dw, fun y hy A hA => ?_⟩
  obtain ⟨w, hw⟩ : ∃ w, TF.Y.j w = (inc₀ TF.X Z ≫ TF.X.π) y := hy
  obtain ⟨m, hm, s, hs⟩ := h w A hA
  have hD := LB.isLB_div (isLB_lbPow hω m) hA
  have hL := isLB_L₀ TF.X Z (FlagMod.mu0 Dw)
  have hT := LB.isLB_div (isLB_lbPow hL m) (pull_isLB hA (inc₀ TF.X Z ≫ TF.X.π))
  have e' : cls _ hL = CechPic.pull (inc₀ TF.X Z ≫ TF.X.π) (cls ω hω) := by
    rw [CechPic.pull_comp, ← e]
    exact cls_pull (TF.X.isLB_Llam _) _ _
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso hT (pull_isLB hD (inc₀ TF.X Z ≫ TF.X.π))
    ((cls_eq_iff hT (pull_isLB hD _)).1 (by
      rw [cls_div (isLB_lbPow hL m) (pull_isLB hA _), cls_lbPow hL, cls_pull hA, cls_pull hD,
        cls_div (isLB_lbPow hω m) hA, cls_lbPow hω, map_sub, map_nsmul, e'])) (lbSecPull _ s _)
  refine ⟨m, t, hm, ?_⟩
  rw [ht, nonzeroLocus_lbSecPull]
  exact (hw ▸ hs : (inc₀ TF.X Z ≫ TF.X.π) y ∈ nonzeroLocus s)

end GlobalTheory.HodgeDominates
