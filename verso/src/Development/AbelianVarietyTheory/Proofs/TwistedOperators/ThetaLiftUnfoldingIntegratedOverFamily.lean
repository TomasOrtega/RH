import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldOverFlagUnipotentThetaLift
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftConvContGrowth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilMixedCoordinatesContinuousBoundedSupNorm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCoreOfExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SFiniteCovolumeOneMatrixUnitriangularMeasures
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExistStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittUnfoldedIntegralLeCoreQuotientHeightStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 400000 in

/- English proof (translation)
Take `⟨vT⟩` from `(GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 0 V₀.rank`. Establish `hmix` using `(GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W ρ 0 a.d (hypZero W) a.vS vT a.χV a.χW a.om ha.weil Φ hΦ).1`. Establish `hpos : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (⟨a.d.nB p.2.2 * a.d.levi p.2.1.1, mul_mem (a.d.nB_mem_NFlag _) (a.d.levi_mem_NFlag p.2.1.2)⟩ : flagN a.d)` using `((a.d.continuous_nB.comp continuous_snd.snd).mul ((a.d.continuous_levi.comp continuous_subtype_val).comp continuous_snd.fst)).subtype_mk _`. Establish `hTh : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.Th p.1.2 (a.d.nB p.2.2 * a.d.levi p.2.1.1)` using `ha.cont.comp (continuous_fst.snd.prodMk hpos)`. Establish `hM : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)`.

Use `by`. Establish `h1 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.emb0 (a.g p.1.2)` using `a.d.continuous_embed.comp (ha.g.comp continuous_fst.snd)`. Establish `h2 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1 : Mx D W.rank ρ)` using `continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd.fst))`. Establish `h3 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2 : WO V₀ W)` using `continuous_const.matrix_mul continuous_snd.snd`. Establish `hq : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => (((a.d.emb0 (a.g p.1.2), p.1.1), ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1, (rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)) : (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W)` using `(h1.prodMk continuous_fst.fst).prodMk (h2.prodMk h3)`.

Establish `hc` using `hmix.comp hq`. Conclude with `hc`. Establish `hfin` using `(hG.2.1.comp continuous_fst.fst).mul (hTh.mul hM)`. Conclude with `hfin`.
-/
theorem tot_continuous (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) : Continuous (a.tot G Φ) := by
  obtain ⟨vT⟩ := (GlobalTheory.T.unfoldingLevelsAndSteps_haarMeasures_exist D).2.2.1 0 V₀.rank
  have hmix := (GlobalTheory.MixCont.mixed_coords_continuous D ψ V V₀ W W ρ 0 a.d (hypZero W) a.vS vT a.χV a.χW a.om
    ha.weil Φ hΦ).1
  have hpos : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      (⟨a.d.nB p.2.2 * a.d.levi p.2.1.1, mul_mem (a.d.nB_mem_NFlag _) (a.d.levi_mem_NFlag p.2.1.2)⟩ : flagN a.d) :=
    ((a.d.continuous_nB.comp continuous_snd.snd).mul
      ((a.d.continuous_levi.comp continuous_subtype_val).comp continuous_snd.fst)).subtype_mk _
  have hTh : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.Th p.1.2 (a.d.nB p.2.2 * a.d.levi p.2.1.1) :=
    ha.cont.comp (continuous_fst.snd.prodMk hpos)
  have hM : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
      a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g p.1.2), p.1.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1)
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2) :=
by
    have h1 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank => a.d.emb0 (a.g p.1.2) :=
      a.d.continuous_embed.comp (ha.g.comp continuous_fst.snd)
    have h2 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1 : Mx D W.rank ρ) :=
      continuous_const.matrix_mul (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd.fst))
    have h3 : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2 : WO V₀ W) :=
      continuous_const.matrix_mul continuous_snd.snd
    have hq : Continuous fun p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank =>
        (((a.d.emb0 (a.g p.1.2), p.1.1), ((rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.1.1.1, (rat a.x₀ : Mx D W.rank ρ) ⬝ p.2.2)) :
          (GA D V × GA D W) × Mx D W.rank ρ × WO V₀ W) :=
      (h1.prodMk continuous_fst.fst).prodMk (h2.prodMk h3)
    have hc := hmix.comp hq
    exact hc
  have hfin := (hG.2.1.comp continuous_fst.fst).mul (hTh.mul hM)
  exact hfin

/- English proof (translation)
Establish `hD : Descent D` using `GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)`. Take `⟨om', hom'⟩` from `(hD ψ V W a.χV a.χW a.om ha.weil).1 V₀ ρ a.d`. Establish `hΦ'` using `ha.weil.om_pres (a.d.emb0 (a.g y), 1) Φ hΦ`. Take `⟨h1, h2⟩` from `GlobalTheory.Unf.unfold_over_N_lift D hD ψ V V₀ W ρ a.d a.χV a.χW a.om om' ha.weil hom' a.vS a.vN a.vb a.vU a.vW a.x₀ (a.Th y) ha.base (ha.th y) G (a.om (a.d.emb0 (a.g y), 1) Φ) hG hΦ' 𝓑 h𝓑`. Establish `hsplit : ∀ h, a.om (1, h) (a.om (a.d.emb0 (a.g y), 1) Φ) = a.om (a.d.emb0 (a.g y), h) Φ`.

Introduce `h`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]`. Establish `hlift : ∀ n, liftS a.om a.vW.μ a.vW.𝓕 G (a.om (a.d.emb0 (a.g y), 1) Φ) n = liftS a.om a.vW.μ a.vW.𝓕 G Φ (n * a.d.emb0 (a.g y))`. Introduce `n`. Establish `ht` using `(GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D ψ V W a.χV a.χW a.om ha.weil a.vW G Φ hG hΦ).2.2.2.2 (a.d.emb0 (a.g y)) 1`.

Establish `hr : rTrans (1 : GA D W) G = G` using `by funext x; simp [rTrans]`. Rewrite `ht` using `[hr]`. Rewrite using `[ht]`. Both sides reduce to the same expression. Simplify using `only [hsplit, hlift] at h1 h2`.

Conclude with `⟨h1, h2⟩`.
-/
theorem inner_unfold (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G)
    (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) (y : Y) :
    IntegrableOn (fun h => G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ)) 𝓑
      a.vW.μ ∧
    ∫ n in a.vN.𝓝, a.Th y n.1 * liftS a.om a.vW.μ a.vW.𝓕 G Φ (n.1 * a.d.emb0 (a.g y)) ∂a.vN.ν =
      ∫ h in 𝓑, G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ := by
  have hD : Descent D := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨om', hom'⟩ := (hD ψ V W a.χV a.χW a.om ha.weil).1 V₀ ρ a.d
  have hΦ' := ha.weil.om_pres (a.d.emb0 (a.g y), 1) Φ hΦ
  obtain ⟨h1, h2⟩ := GlobalTheory.Unf.unfold_over_N_lift D hD ψ V V₀ W ρ a.d a.χV a.χW a.om om' ha.weil hom' a.vS a.vN a.vb
    a.vU a.vW a.x₀ (a.Th y) ha.base (ha.th y) G (a.om (a.d.emb0 (a.g y), 1) Φ) hG hΦ' 𝓑 h𝓑
  have hsplit : ∀ h, a.om (1, h) (a.om (a.d.emb0 (a.g y), 1) Φ) = a.om (a.d.emb0 (a.g y), h) Φ := by
    intro h
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have hlift : ∀ n, liftS a.om a.vW.μ a.vW.𝓕 G (a.om (a.d.emb0 (a.g y), 1) Φ) n =
      liftS a.om a.vW.μ a.vW.𝓕 G Φ (n * a.d.emb0 (a.g y)) := by
    intro n
    have ht := (GlobalTheory.Unf.LiftRapid.lift_conv_cont_growth D ψ V W a.χV a.χW a.om ha.weil a.vW G Φ hG hΦ).2.2.2.2
      (a.d.emb0 (a.g y)) 1
    have hr : rTrans (1 : GA D W) G = G := by funext x; simp [rTrans]
    rw [hr] at ht
    rw [ht]; rfl
  simp only [hsplit, hlift] at h1 h2
  exact ⟨h1, h2⟩

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc.Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W : HSp D} {ρ : ℕ} {Y : Type} [TopologicalSpace Y]
  [MeasurableSpace Y]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Take `⟨b1, b2, b3, b4, b5, b6, b7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Take `⟨-, -, i3, -⟩` from `lattice_Mx D ρ V₀.rank`. Use `haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩`. Use `haveI : BorelSpace (UX D ρ) := ⟨rfl⟩`. Use `haveI := a.vW.haar`.

Use `haveI : SFinite a.vW.μ := inferInstance`. Use `haveI := ha.sfin`. Take `⟨sb, sU⟩` from `GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU`. Take `⟨C, A, hCA⟩` from `GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight D ψ V V₀ W ρ a.d a.χV a.χW a.om ha.weil a.vS a.vb a.vU a.vW a.x₀ ha.base G Φ hG hΦ 𝓑 h𝓑`. Take `⟨M, -, hMb, hMi⟩` from `ha.small`.

Establish `hM0 : ∀ y, 0 ≤ M y` using `fun y => (norm_nonneg _).trans (hMb y 1 (one_mem _))`. Use `set Bd : GA D V₀ → GA D W → ENNReal := fun g h => ∫⁻ u, ∫⁻ b in a.vb.𝓕, ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 g, h) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1) ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂a.vb.μ ∂a.vU.ν with hBd`. Use `set F : GA D W × Y → ENNReal := fun q => ENNReal.ofReal (M q.2) * (‖G q.1‖ₑ * Bd (a.g q.2) q.1) with hF`. Use `haveI : SecondCountableTopology (GA D W × Y) := inferInstance`. Use `haveI : OpensMeasurableSpace (GA D W × Y) := Prod.opensMeasurableSpace`.

Use `haveI : SecondCountableTopologyEither (UX D ρ) (Mx D ρ V₀.rank) := secondCountableTopologyEither_of_right _ _`. Use `haveI : OpensMeasurableSpace (UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace`. Use `haveI : SecondCountableTopologyEither (GA D W × Y) (UX D ρ × Mx D ρ V₀.rank) := secondCountableTopologyEither_of_left _ _`. Use `haveI : OpensMeasurableSpace ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace`. Establish `hmeas : Measurable (a.tot G Φ)` using `(tot_continuous a ha G Φ hG hΦ).measurable`.

Use `⟨hmeas.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Use `show ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) < ⊤`. Establish `hpt : ∀ q : GA D W × Y, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ≤ F q`. Introduce `q`. Establish `hc : ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ ≠ ⊤` using `ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top`.

Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun u => lintegral_mono fun b => ?_` and prove the remaining obligations. Establish `hmem : a.d.nB b * a.d.levi u.1 ∈ flagN a.d` using `mul_mem (a.d.nB_mem_NFlag b) (a.d.levi_mem_NFlag u.2)`. Establish `hth : ‖a.Th q.2 (a.d.nB b * a.d.levi u.1)‖ₑ ≤ ENNReal.ofReal (M q.2)`. Rewrite using `[← ofReal_norm_eq_enorm]`.

Conclude with `ENNReal.ofReal_le_ofReal (hMb _ _ hmem)`. Use `show ‖G q.1 * (a.Th q.2 (a.d.nB b * a.d.levi u.1) * a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1) ((rat a.x₀ : Mx D W.rank ρ) ⬝ b))‖ₑ ≤ _`. Rewrite using `[enorm_mul, enorm_mul, ← mul_assoc, mul_comm (‖G q.1‖ₑ), mul_assoc, mul_assoc]`. Use `gcongr`. Use `_ = ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ * Bd (a.g q.2) q.1 := by`.

Simplify using `only [hBd]`. Rewrite using `[← lintegral_const_mul' _ _ hc]`. Use `lintegral_congr fun u => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_const_mul' _ _ hc]`. Use `_ = F q := by simp only [hF, mul_assoc]`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `_ ≤ ∫⁻ y, ENNReal.ofReal (M y) * ENNReal.ofReal (C * quotHeight V₀ (a.g y) ^ A) ∂a.m := by`. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `hCA (a.g y)`. Use `_ = ∫⁻ y, ENNReal.ofReal (C * (M y * quotHeight V₀ (a.g y) ^ A)) ∂a.m := by`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (hM0 y)]`. Put the polynomial expressions in normal form.

Use `_ < ⊤ := ((hMi A).const_mul C).lintegral_lt_top`.
-/
theorem tot_integrable [SecondCountableTopology Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y) (ha : a.Is)
    (G : GA D W → ℂ) (Φ : WO V W → ℂ) (hG : RapidDec W G) (hΦ : IsThetaFunO ψ V W Φ) (𝓑 : Set (GA D W))
    (h𝓑 : IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ) :
    Integrable (a.tot G Φ) (a.totMeas 𝓑) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, -, i3, -⟩ := lattice_Mx D ρ V₀.rank
  haveI : BorelSpace (Mx D ρ V₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  obtain ⟨C, A, hCA⟩ := GlobalTheory.T.wittUnfoldedIntegral_le_coreQuotientHeight D ψ V V₀ W ρ a.d a.χV a.χW a.om ha.weil a.vS a.vb a.vU a.vW a.x₀ ha.base G Φ
    hG hΦ 𝓑 h𝓑
  obtain ⟨M, -, hMb, hMi⟩ := ha.small
  have hM0 : ∀ y, 0 ≤ M y := fun y => (norm_nonneg _).trans (hMb y 1 (one_mem _))
  set Bd : GA D V₀ → GA D W → ENNReal := fun g h => ∫⁻ u, ∫⁻ b in a.vb.𝓕,
    ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 g, h) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
      ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂a.vb.μ ∂a.vU.ν with hBd
  set F : GA D W × Y → ENNReal := fun q => ENNReal.ofReal (M q.2) * (‖G q.1‖ₑ * Bd (a.g q.2) q.1) with hF
  haveI : SecondCountableTopology (GA D W × Y) := inferInstance
  haveI : OpensMeasurableSpace (GA D W × Y) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (UX D ρ) (Mx D ρ V₀.rank) := secondCountableTopologyEither_of_right _ _
  haveI : OpensMeasurableSpace (UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  haveI : SecondCountableTopologyEither (GA D W × Y) (UX D ρ × Mx D ρ V₀.rank) :=
    secondCountableTopologyEither_of_left _ _
  haveI : OpensMeasurableSpace ((GA D W × Y) × UX D ρ × Mx D ρ V₀.rank) := Prod.opensMeasurableSpace
  have hmeas : Measurable (a.tot G Φ) := (tot_continuous a ha G Φ hG hΦ).measurable
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  show ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) < ⊤
  have hpt : ∀ q : GA D W × Y, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ≤ F q := by
    intro q
    have hc : ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top
    calc ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))
        ≤ ∫⁻ u, ∫⁻ b, ‖a.tot G Φ (q, (u, b))‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := lintegral_prod_le _
      _ ≤ ∫⁻ u, ∫⁻ b, ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ *
            ‖a.d.mixS W ψ a.vS.μ a.vS.𝓕 (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b)‖ₑ ∂(a.vb.μ.restrict a.vb.𝓕) ∂a.vU.ν := by
          refine lintegral_mono fun u => lintegral_mono fun b => ?_
          have hmem : a.d.nB b * a.d.levi u.1 ∈ flagN a.d := mul_mem (a.d.nB_mem_NFlag b) (a.d.levi_mem_NFlag u.2)
          have hth : ‖a.Th q.2 (a.d.nB b * a.d.levi u.1)‖ₑ ≤ ENNReal.ofReal (M q.2) := by
            rw [← ofReal_norm_eq_enorm]; exact ENNReal.ofReal_le_ofReal (hMb _ _ hmem)
          show ‖G q.1 * (a.Th q.2 (a.d.nB b * a.d.levi u.1) * a.d.mixS W ψ a.vS.μ a.vS.𝓕
            (a.om (a.d.emb0 (a.g q.2), q.1) Φ) ((rat a.x₀ : Mx D W.rank ρ) ⬝ u.1.1)
              ((rat a.x₀ : Mx D W.rank ρ) ⬝ b))‖ₑ ≤ _
          rw [enorm_mul, enorm_mul, ← mul_assoc, mul_comm (‖G q.1‖ₑ), mul_assoc, mul_assoc]
          gcongr
      _ = ENNReal.ofReal (M q.2) * ‖G q.1‖ₑ * Bd (a.g q.2) q.1 := by
          simp only [hBd]
          rw [← lintegral_const_mul' _ _ hc]
          refine lintegral_congr fun u => ?_
          rw [← lintegral_const_mul' _ _ hc]
      _ = F q := by simp only [hF, mul_assoc]
  calc ∫⁻ p, ‖a.tot G Φ p‖ₑ ∂(((a.vW.μ.restrict 𝓑).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)))
      ≤ ∫⁻ q, ∫⁻ r, ‖a.tot G Φ (q, r)‖ₑ ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)) ∂((a.vW.μ.restrict 𝓑).prod a.m) :=
        lintegral_prod_le _
    _ ≤ ∫⁻ q, F q ∂((a.vW.μ.restrict 𝓑).prod a.m) := lintegral_mono hpt
    _ = ∫⁻ z, F z.swap ∂(a.m.prod (a.vW.μ.restrict 𝓑)) := (lintegral_prod_swap F).symm
    _ ≤ ∫⁻ y, ∫⁻ h, F (h, y) ∂(a.vW.μ.restrict 𝓑) ∂a.m := lintegral_prod_le _
    _ = ∫⁻ y, ENNReal.ofReal (M y) * ∫⁻ h in 𝓑, ‖G h‖ₑ * Bd (a.g y) h ∂a.vW.μ ∂a.m := by
        simp only [hF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (M y) * ENNReal.ofReal (C * quotHeight V₀ (a.g y) ^ A) ∂a.m := by
        refine lintegral_mono fun y => ?_
        gcongr
        exact hCA (a.g y)
    _ = ∫⁻ y, ENNReal.ofReal (C * (M y * quotHeight V₀ (a.g y) ^ A)) ∂a.m := by
        refine lintegral_congr fun y => ?_
        rw [← ENNReal.ofReal_mul (hM0 y)]
        ring_nf
    _ < ⊤ := ((hMi A).const_mul C).lintegral_lt_top

/- English proof (translation)
Take `⟨b1, b2, b3, b4, b5, b6, b7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Use `haveI := a.vW.haar`. Use `haveI : SFinite a.vW.μ := inferInstance`. Use `haveI := ha.sfin`. Take `⟨sb, sU⟩` from `GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU`.

Establish `hI' : Integrable (a.tot G Φ) (((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕)))` using `hI`. Use `set K : GA D W × Y → ℂ := fun q => G q.1 * fl ψ a.d W a.vS a.vb a.vU (a.Th q.2) (rat a.x₀) (a.om (a.d.emb0 (a.g q.2), q.1) Φ) with hK`. Establish `hae : (fun q => ∫ r, a.tot G Φ (q, r) ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) =ᵐ[(a.vW.μ.restrict B₀).prod a.m] K` using `by filter_upwards [hI'.prod_right_ae] with q hq`. Rewrite using `[integral_prod _ hq]`. Simplify using `only [Gen.tot, integral_const_mul, hK, fl]`.

Establish `hKi : Integrable K ((a.vW.μ.restrict B₀).prod a.m)` using `hI'.integral_prod_left.congr hae`. Establish `hker : ∀ h, ∫ y, K (h, y) ∂a.m = a.ker G Φ h`. Introduce `h`. Simplify using `only [hK, Gen.ker, integral_const_mul]`. Establish `htot : ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ q, K q ∂((a.vW.μ.restrict B₀).prod a.m)` using `by show ∫ p, a.tot G Φ p ∂(((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) = _`.

Rewrite using `[integral_prod _ hI']`. Conclude with `integral_congr_ae hae`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `hKi.integral_prod_left` as an intermediate fact. Simplify using `only [hker] at this`.

Conclude with `this`. Rewrite using `[htot, integral_prod _ hKi]`. Simplify using `only [hker]`. Rewrite using `[htot, integral_prod_symm _ hKi]`.
-/
theorem fubini_tot (a : Gen ψ V V₀ W ρ Y) (ha : a.Is) (G : GA D W → ℂ) (Φ : WO V W → ℂ) (B₀ : Set (GA D W))
    (hI : Integrable (a.tot G Φ) (a.totMeas B₀)) :
    IntegrableOn (a.ker G Φ) B₀ a.vW.μ ∧ ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ h in B₀, a.ker G Φ h ∂a.vW.μ ∧
    ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ y, ∫ h in B₀,
      G h * fl ψ a.d W a.vS a.vb a.vU (a.Th y) (rat a.x₀) (a.om (a.d.emb0 (a.g y), h) Φ) ∂a.vW.μ ∂a.m := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI' : Integrable (a.tot G Φ) (((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) :=
    hI
  set K : GA D W × Y → ℂ := fun q =>
    G q.1 * fl ψ a.d W a.vS a.vb a.vU (a.Th q.2) (rat a.x₀) (a.om (a.d.emb0 (a.g q.2), q.1) Φ) with hK
  have hae : (fun q => ∫ r, a.tot G Φ (q, r) ∂(a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) =ᵐ[(a.vW.μ.restrict B₀).prod a.m]
      K := by
    filter_upwards [hI'.prod_right_ae] with q hq
    rw [integral_prod _ hq]
    simp only [Gen.tot, integral_const_mul, hK, fl]
  have hKi : Integrable K ((a.vW.μ.restrict B₀).prod a.m) := hI'.integral_prod_left.congr hae
  have hker : ∀ h, ∫ y, K (h, y) ∂a.m = a.ker G Φ h := by
    intro h
    simp only [hK, Gen.ker, integral_const_mul]
  have htot : ∫ p, a.tot G Φ p ∂(a.totMeas B₀) = ∫ q, K q ∂((a.vW.μ.restrict B₀).prod a.m) := by
    show ∫ p, a.tot G Φ p ∂(((a.vW.μ.restrict B₀).prod a.m).prod (a.vU.ν.prod (a.vb.μ.restrict a.vb.𝓕))) = _
    rw [integral_prod _ hI']
    exact integral_congr_ae hae
  refine ⟨?_, ?_, ?_⟩
  · have := hKi.integral_prod_left
    simp only [hker] at this
    exact this
  · rw [htot, integral_prod _ hKi]
    simp only [hker]
  · rw [htot, integral_prod_symm _ hKi]

end GlobalTheory.Asc.Gen

namespace GlobalTheory.Asc

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ V V₀ W ρ Y _ _ _ _ a ha G Φ hG hΦ 𝓑 h𝓑`. Take `⟨b1, b2, b3, b4, b5, b6, b7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Use `haveI := a.vW.haar`. Use `haveI : SFinite a.vW.μ := inferInstance`. Use `haveI := ha.sfin`.

Take `⟨sb, sU⟩` from `GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU`. Establish `hI` using `Gen.tot_integrable a ha G Φ hG hΦ 𝓑 h𝓑`. Take `⟨hker, -, hE⟩` from `Gen.fubini_tot a ha G Φ 𝓑 hI`. Use `⟨hI, hker, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hE, Gen.lhs]`.

Conclude with `integral_congr_ae (ae_of_all _ fun y => (Gen.inner_unfold a ha G Φ hG hΦ 𝓑 h𝓑 y).2)`. Introduce `S hS`. Establish `hset : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} = (S ×ˢ (Set.univ : Set Y)) ×ˢ (Set.univ : Set (UX D ρ × Mx D ρ V₀.rank))`. Use extensionality with `p`. Simplify using the standard rewrite rules.

Establish `hres : (a.totMeas 𝓑).restrict {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} = a.totMeas (𝓑 ∩ S)`. Simplify using `only [Gen.totMeas]`. Rewrite using `[hset, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ, Measure.restrict_restrict hS, Set.inter_comm]`. Establish `hI' : Integrable (a.tot G Φ) (a.totMeas (𝓑 ∩ S))`. Rewrite using `[← hres]`.

Conclude with `hI.restrict`. Rewrite using `[hres]`. Conclude with `((Gen.fubini_tot a ha G Φ (𝓑 ∩ S) hI').2.1).symm`.
-/
theorem unfold_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) := by
  intro D ψ V V₀ W ρ Y _ _ _ _ a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  haveI := a.vW.haar
  haveI : SFinite a.vW.μ := inferInstance
  haveI := ha.sfin
  obtain ⟨sb, sU⟩ := GlobalTheory.Unf.sFinite_vol D ρ V₀.rank a.vb a.vU
  have hI := Gen.tot_integrable a ha G Φ hG hΦ 𝓑 h𝓑
  obtain ⟨hker, -, hE⟩ := Gen.fubini_tot a ha G Φ 𝓑 hI
  refine ⟨hI, hker, ?_, ?_⟩
  · rw [hE, Gen.lhs]
    exact integral_congr_ae (ae_of_all _ fun y => (Gen.inner_unfold a ha G Φ hG hΦ 𝓑 h𝓑 y).2)
  · intro S hS
    have hset : {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        (S ×ˢ (Set.univ : Set Y)) ×ˢ (Set.univ : Set (UX D ρ × Mx D ρ V₀.rank)) := by
      ext p; simp
    have hres : (a.totMeas 𝓑).restrict {p : (GA D W × Y) × UX D ρ × Mx D ρ V₀.rank | p.1.1 ∈ S} =
        a.totMeas (𝓑 ∩ S) := by
      simp only [Gen.totMeas]
      rw [hset, ← Measure.prod_restrict, ← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_univ,
        Measure.restrict_restrict hS, Set.inter_comm]
    have hI' : Integrable (a.tot G Φ) (a.totMeas (𝓑 ∩ S)) := by
      rw [← hres]; exact hI.restrict
    rw [hres]
    exact ((Gen.fubini_tot a ha G Φ (𝓑 ∩ S) hI').2.1).symm

end GlobalTheory.Asc

/- English proof (translation)
The claim follows from `GlobalTheory.Asc.unfold_family`.
-/
example : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (a : Gen ψ V V₀ W ρ Y), a.Is → ∀ (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∀ 𝓑 : Set (GA D W), IsFundamentalDomain (GQ W ⊓ Rgrp W (rat a.x₀) : Subgroup (GA D W)) 𝓑 a.vW.μ → Integrable (a.tot G Φ) (a.totMeas 𝓑) ∧ IntegrableOn (a.ker G Φ) 𝓑 a.vW.μ ∧ a.lhs G Φ = ∫ p, a.tot G Φ p ∂(a.totMeas 𝓑) ∧ ∀ S : Set (GA D W), MeasurableSet S → ∫ h in 𝓑 ∩ S, a.ker G Φ h ∂a.vW.μ = ∫ p in {p | p.1.1 ∈ S}, a.tot G Φ p ∂(a.totMeas 𝓑) :=
  GlobalTheory.Asc.unfold_family
