import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinLoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.WeilQuotientGlobalAssumptions
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpWinGlob
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitW

open Formalism.L2.SG.Pf.AmpWinLoc Formalism.L2.SG.Pf.Choice

/- English proof (translation)
Substitute `hv` using the available equality. Take `⟨β, hβm, hβ1⟩` from `bruhat_mulMap C u τ`. Conclude with `⟨sf_muNl C τ one_pos, sf_muHl C u τ, (invOn_mulMap C u τ).2.2.1, β, hβm, hβ1, loc_id C u τ hβm hβ1⟩`.
-/
theorem loc_at {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) (τ : D.what₂.Tau)
    (v : InfinitePlace X.B.I.F) (hv : vOf X τ = v) :
    SigmaFinite (muNl C τ v) ∧ SigmaFinite (muHl C u τ v) ∧
    QPK.mulMap (muNl C τ v) (muHl C u τ v)
      (QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v))ᶜ = 0 ∧
    ∃ β : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable β ∧
      (∀ x, ∫⁻ s, β (s * x) ∂(QPK.mulMap (muNl C τ v) (muHl C u τ v)) = 1) ∧
      ∫⁻ y, β y * ‖X.Wloc u v y‖ₑ ^ 2 ∂(Formalism.REAL.muG (X.B.I.ε v)) = l2SG (C.nuS u τ) (wT C u τ) := by
  subst hv
  obtain ⟨β, hβm, hβ1⟩ := bruhat_mulMap C u τ
  exact ⟨sf_muNl C τ one_pos, sf_muHl C u τ, (invOn_mulMap C u τ).2.2.1, β, hβm, hβ1, loc_id C u τ hβm hβ1⟩

/- English proof (translation)
Establish `hPemb : MeasurableEmbedding (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _)` using `(Topology.IsClosedEmbedding.piMap fun τ => Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding`. Establish `htr : trI C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘ (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm`. Use function extensionality and compare the values at `x τ`. Both sides reduce to the same expression. Use `haveI : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u v) := fun v => by`.

Establish `key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muHl C u τ w)`. Introduce and unpack `τ w rfl`. Conclude with `sf_muHl C u τ`. Conclude with `key (X.pl v) v (X.pl.symm_apply_apply v)`. Rewrite using `[htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]`.

Establish `h1 : (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm = Measure.pi (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ))` using `((measurePreserving_piCongrLeft (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u) X.pl.symm).symm _).map_eq`. Establish `h2 : (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) = fun τ => muHl C u τ (X.pl.symm τ)`. Use function extensionality and compare the values at `τ`. Use `show muHl C u (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muHl C u τ (X.pl.symm τ)`. Rewrite using `[Equiv.apply_symm_apply]`.

Rewrite using `[h1, h2]`. Establish `hmap : ∀ τ, (muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = C.muW u τ` using `fun τ => map_muHl C u τ`. Establish `: ∀ τ, SigmaFinite ((muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)))` using `fun τ => by`. Rewrite using `[hmap τ]`. Conclude with `(C.muW_haar u τ).1`.

Use `(Measure.pi_map_pi (μ := fun τ => muHl C u τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ)) (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_` and prove the remaining obligations. Repeatedly rewrite using `[hmap]`.
-/
theorem map_trI_H {D : D7} {X : HidaSetting D} (C : Choice X 1) (u : D.what₂.Word) :
    (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map (trI C) = Measure.pi (C.muW u) := by
  have hPemb : MeasurableEmbedding
      (Pi.map (fun τ => eT C τ (X.pl.symm τ)) : (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) :=
    (Topology.IsClosedEmbedding.piMap fun τ =>
      Formalism.L2.SG.Pf.BaseOf.trG_closedEmb (n_eq' X) (X.B.I.ε (X.pl.symm τ)) (C.isT τ).2.1).measurableEmbedding
  have htr : trI C = (Pi.map (fun τ => eT C τ (X.pl.symm τ)) :
      (∀ τ : D.what₂.Tau, Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))) → _) ∘
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
    funext x τ
    rfl
  haveI : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u v) := fun v => by
    have key : ∀ (τ : D.what₂.Tau) (w : InfinitePlace X.B.I.F), vOf X τ = w → SigmaFinite (muHl C u τ w) := by
      rintro τ w rfl; exact sf_muHl C u τ
    exact key (X.pl v) v (X.pl.symm_apply_apply v)
  rw [htr, ← Measure.map_map hPemb.measurable (MeasurableEquiv.measurable _)]
  have h1 : (Measure.pi (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u)).map
      (MeasurableEquiv.piCongrLeft (fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm =
      Measure.pi (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) :=
    ((measurePreserving_piCongrLeft (Formalism.L2.SG.Pf.AmpWinGlob.muHv C u) X.pl.symm).symm _).map_eq
  have h2 : (fun τ => Formalism.L2.SG.Pf.AmpWinGlob.muHv C u (X.pl.symm τ)) = fun τ => muHl C u τ (X.pl.symm τ) := by
    funext τ
    show muHl C u (X.pl (X.pl.symm τ)) (X.pl.symm τ) = muHl C u τ (X.pl.symm τ)
    rw [Equiv.apply_symm_apply]
  rw [h1, h2]
  have hmap : ∀ τ, (muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ)) = C.muW u τ := fun τ => map_muHl C u τ
  have : ∀ τ, SigmaFinite ((muHl C u τ (X.pl.symm τ)).map (eT C τ (X.pl.symm τ))) := fun τ => by
    rw [hmap τ]; exact (C.muW_haar u τ).1
  refine (Measure.pi_map_pi (μ := fun τ => muHl C u τ (X.pl.symm τ)) (f := fun τ => eT C τ (X.pl.symm τ))
    (fun τ => (eT_emb C τ (X.pl.symm τ)).measurable.aemeasurable)).trans ?_
  simp_rw [hmap]

/- English proof (translation)
Introduce `D X C hB _ u cN cH hN0 hNt hH0 hHt hN hH`. Establish `hv : ∀ v, vOf X (X.pl v) = v` using `fun v => X.pl.symm_apply_apply v`. Establish `loc` using `fun v => loc_at C u (X.pl v) v (hv v)`. Use `choose hsN hsH hconc β hβm hβ1 hβl using loc`. Use `set μN : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muNl C (X.pl v) v with hμN`.

Use `set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muHl C u (X.pl v) v with hμH`. Use `haveI : ∀ v, SigmaFinite (μN v) := hsN`. Use `haveI : ∀ v, SigmaFinite (μH v) := hsH`. Use `haveI : SigmaFinite (muNB D 1) := (muNB_haar (D := D) one_pos).1`. Use `haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1`.

Take `⟨hemb0, hmapN⟩` from `Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsN v) one_pos`. Establish `hemb : MeasurableEmbedding (trI C)` using `hemb0`. Establish `hmapH` using `map_trI_H C u`. Establish `eN : X.muN u = cN • Measure.pi μN`. Use extensionality with `A hA`.

Establish `hc : Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) = Measure.pi μN A`. Rewrite using `[← show (Measure.pi μN).map (trI C) = Measure.pi (fun _ : D.what₂.Tau => muNB D 1) from hmapN, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]`. Rewrite using `[hN A hA, hc, Measure.smul_apply, smul_eq_mul]`. Establish `eH : X.muH u = cH • Measure.pi μH`. Use extensionality with `A hA`.

Establish `hc : Measure.pi (C.muW u) (trI C '' A) = Measure.pi μH A`. Rewrite using `[← show (Measure.pi μH).map (trI C) = Measure.pi (C.muW u) from hmapH, hemb.map_apply, Set.preimage_image_eq _ hemb.injective]`. Rewrite using `[hH A hA, hc, Measure.smul_apply, smul_eq_mul]`. Use `set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hFdef`. Establish `hFm : ∀ v, Measurable (F v)` using `fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2`.

Use `set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef`. Establish `hfm : Measurable f` using `Finset.measurable_prod _ fun v _ => ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))`. Establish `key` using `X.nuQ_weil u f hfm`. Establish `hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∏ τ, l2SG (C.nuS u τ) (wT C u τ)`. Rewrite using `[hfdef, Formalism.L2.SG.ProjRows.muInf, QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]`.

Rewrite using `[← Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (wT C u (X.pl v))) _ (fun v => rfl)]`. Conclude with `Finset.prod_congr rfl fun v _ => hβl v`. Establish `hin : ∀ x, ∫⁻ s, f (s * x) ∂((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) = (cN * cH) * ‖X.Wu u x‖ₑ ^ 2`. Introduce `x`. Rewrite using `[lintegral_map (f := fun s => f (s * x)) (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul, eN, eH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, lintegral_smul_measure]`.

Establish `h1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf, f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v)` using `fun p => rfl`. Repeatedly rewrite using `[h1]`. Rewrite using `[QPK.lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v)) (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]`. Establish `h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (μN v) (μH v)) = F v (x v)`. Introduce `v`.

Establish `hae : ∀ᵐ s ∂(QPK.mulMap (μN v) (μH v)), s ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v)` using `mem_ae_iff.mpr (hconc v)`. Rewrite using `[lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by`. Take `⟨m, hm, h, hh, rfl⟩` from `hs`. Establish `hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u v` using `by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh`. Establish `hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v` using `Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm) (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')`.

Use `show β v (m * h * x v) * ‖X.Wloc u v (m * h * x v)‖ₑ ^ 2 = β v (m * h * x v) * ‖X.Wloc u v (x v)‖ₑ ^ 2`. Rewrite using `[← enorm_norm (X.Wloc u v (m * h * x v)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm])]`. Rewrite using `[lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]`. Repeatedly rewrite using `[h2]`. Establish `h3 : ∏ v, F v (x v) = ‖X.Wu u x‖ₑ ^ 2`.

Rewrite using `[Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]`. Rewrite using `[h3, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[hin]`. Establish `hW1 : ∫⁻ x, ‖X.Wu u x‖ₑ ^ 2 ∂(X.nuQ u) = 1` using `(X.Wu_spec u).2.2.2.2`.

Rewrite `key` using `[lintegral_const_mul' _ _ (ENNReal.mul_ne_top hNt hHt), hW1, mul_one, hL1]`. Conclude with `key`.
-/
theorem prod_l2SG_eq : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ (u : D.what₂.Word) (cN cH : ℝ≥0∞), cN ≠ 0 → cN ≠ ⊤ → cH ≠ 0 → cH ≠ ⊤ →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muN u A = cN * Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A)) →
    (∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = cH * Measure.pi (C.muW u) (trI C '' A)) →
    ∏ τ, l2SG (C.nuS u τ) (wT C u τ) = cN * cH := by
  intro D X C hB _ u cN cH hN0 hNt hH0 hHt hN hH
  have hv : ∀ v, vOf X (X.pl v) = v := fun v => X.pl.symm_apply_apply v
  have loc := fun v => loc_at C u (X.pl v) v (hv v)
  choose hsN hsH hconc β hβm hβ1 hβl using loc
  set μN : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muNl C (X.pl v) v with hμN
  set μH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => muHl C u (X.pl v) v with hμH
  haveI : ∀ v, SigmaFinite (μN v) := hsN
  haveI : ∀ v, SigmaFinite (μH v) := hsH
  haveI : SigmaFinite (muNB D 1) := (muNB_haar (D := D) one_pos).1
  haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1
  obtain ⟨hemb0, hmapN⟩ := Formalism.L2.SG.Pf.AmpWinGlob.map_trInf C (fun v => hsN v) one_pos
  have hemb : MeasurableEmbedding (trI C) := hemb0
  have hmapH := map_trI_H C u
  have eN : X.muN u = cN • Measure.pi μN := by
    ext A hA
    have hc : Measure.pi (fun _ : D.what₂.Tau => muNB D 1) (trI C '' A) = Measure.pi μN A := by
      rw [← show (Measure.pi μN).map (trI C) = Measure.pi (fun _ : D.what₂.Tau => muNB D 1) from hmapN,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hN A hA, hc, Measure.smul_apply, smul_eq_mul]
  have eH : X.muH u = cH • Measure.pi μH := by
    ext A hA
    have hc : Measure.pi (C.muW u) (trI C '' A) = Measure.pi μH A := by
      rw [← show (Measure.pi μH).map (trI C) = Measure.pi (C.muW u) from hmapH,
        hemb.map_apply, Set.preimage_image_eq _ hemb.injective]
    rw [hH A hA, hc, Measure.smul_apply, smul_eq_mul]
  set F : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞ := fun v y => ‖X.Wloc u v y‖ₑ ^ 2 with hFdef
  have hFm : ∀ v, Measurable (F v) := fun v => (X.Wloc_cont u v).enorm.measurable.pow_const 2
  set f : X.B.I.Ginf → ℝ≥0∞ := fun x => ∏ v, β v (x v) * F v (x v) with hfdef
  have hfm : Measurable f :=
    Finset.measurable_prod _ fun v _ =>
      ((hβm v).comp (measurable_pi_apply v)).mul ((hFm v).comp (measurable_pi_apply v))
  have key := X.nuQ_weil u f hfm
  have hL1 : ∫⁻ x, f x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∏ τ, l2SG (C.nuS u τ) (wT C u τ) := by
    rw [hfdef, Formalism.L2.SG.ProjRows.muInf,
      QPK.lintegral_fintype_prod (fun v y => β v y * F v y) (fun v => (hβm v).mul (hFm v))]
    rw [← Fintype.prod_equiv X.pl (fun v => l2SG (C.nuS u (X.pl v)) (wT C u (X.pl v))) _ (fun v => rfl)]
    exact Finset.prod_congr rfl fun v _ => hβl v
  have hin : ∀ x, ∫⁻ s, f (s * x) ∂((X.muN u).prod (X.muH u)).map (fun p => p.1 * p.2) =
      (cN * cH) * ‖X.Wu u x‖ₑ ^ 2 := by
    intro x
    rw [lintegral_map (f := fun s => f (s * x))
      (show Measurable (fun s => f (s * x)) from hfm.comp (measurable_mul_const x)) measurable_mul,
      eN, eH, Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure,
      lintegral_smul_measure]
    have h1 : ∀ p : X.B.I.Ginf × X.B.I.Ginf,
        f (p.1 * p.2 * x) = ∏ v, (fun v z => β v (z * x v) * F v (z * x v)) v (p.1 v * p.2 v) :=
      fun p => rfl
    simp_rw [h1]
    rw [QPK.lintegral_pi_prod_mul μN μH (fun v z => β v (z * x v) * F v (z * x v))
      (fun v => ((hβm v).comp (measurable_mul_const _)).mul ((hFm v).comp (measurable_mul_const _)))]
    have h2 : ∀ v, ∫⁻ s, β v (s * x v) * F v (s * x v) ∂(QPK.mulMap (μN v) (μH v)) = F v (x v) := by
      intro v
      have hae : ∀ᵐ s ∂(QPK.mulMap (μN v) (μH v)),
          s ∈ QPK.prodSet (Formalism.L2.SG.Pf.WuDec.Nloc X u v) (Formalism.L2.SG.Pf.WuDec.Hfix X u v) :=
        mem_ae_iff.mpr (hconc v)
      rw [lintegral_congr_ae (g := fun s => β v (s * x v) * F v (x v)) (hae.mono fun s hs => by
        obtain ⟨m, hm, h, hh, rfl⟩ := hs
        have hh' : h ∈ Formalism.L2.SG.Pf.WuDec.Hloc X u v := by rw [Formalism.L2.SG.Pf.WuDec.Hloc_eq]; exact hh
        have hs : m * h ∈ Formalism.L2.SG.Pf.WuDec.Sloc X u v :=
          Formalism.L2.SG.Pf.WuDec.mul_mem_Sloc X u _ (Formalism.L2.SG.Pf.WuDec.Nloc_sub X u _ hm)
            (Formalism.L2.SG.Pf.WuDec.Hloc_sub X u _ hh')
        show β v (m * h * x v) * ‖X.Wloc u v (m * h * x v)‖ₑ ^ 2 = β v (m * h * x v) * ‖X.Wloc u v (x v)‖ₑ ^ 2
        rw [← enorm_norm (X.Wloc u v (m * h * x v)), Formalism.L2.SG.Pf.WuDec.norm_Wloc_inv X u _ hs, enorm_norm])]
      rw [lintegral_mul_const _ (show Measurable (fun s => β v (s * x v)) from
        (hβm v).comp (measurable_mul_const _)), hβ1 v, one_mul]
    simp_rw [h2]
    have h3 : ∏ v, F v (x v) = ‖X.Wu u x‖ₑ ^ 2 := by
      rw [Formalism.L2.SG.Pf.WuDec.enorm_Wu X u x, Finset.prod_pow]
    rw [h3, smul_eq_mul, smul_eq_mul]
    ring
  simp_rw [hin] at key
  have hW1 : ∫⁻ x, ‖X.Wu u x‖ₑ ^ 2 ∂(X.nuQ u) = 1 := (X.Wu_spec u).2.2.2.2
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top hNt hHt), hW1, mul_one, hL1] at key
  exact key

end GlobalTheory.UnitW
