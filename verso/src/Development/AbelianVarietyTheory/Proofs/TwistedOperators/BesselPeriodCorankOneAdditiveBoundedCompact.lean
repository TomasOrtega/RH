import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusLaws

/- English proof (translation)
Unfold `besChar`. Use `split_ifs with h`. Take `⟨a, b, -, -, hv⟩` from `h.choose_spec`. Rewrite using `[hv]`. Conclude with `hψ _`.

Simplify using the standard rewrite rules.
-/
private theorem norm_besChar_eq_one {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (d : BesDat A B ι) (n : GA D B) :
    ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, hv⟩ := h.choose_spec
    rw [hv]
    exact hψ _
  · simp

/- English proof (translation)
Establish `hV` using `GlobalTheory.FunObj.isV_Xp G`. Take `⟨C, hC, hcov⟩` from `GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ => GlobalTheory.DefiniteQuotient.posDef_of_signature (by`. Establish `h1` using `hV.sigOK (tauE D τ)`. Rewrite `h1` using `[hV.sig (tauE D τ)]`. Conclude with `h1)`.

Use `⟨C, hC, fun g => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, c, hc, rfl⟩` from `hcov g`. Conclude with `⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩`.
-/
private theorem coCpt_gridData_V_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.Unf.CoCpt (G.V (.top 0)) := by
  have hV := GlobalTheory.FunObj.isV_Xp G
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (by
      have h1 := hV.sigOK (tauE D τ)
      rw [hV.sig (tauE D τ)] at h1
      exact h1)
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩

/- English proof (translation)
Establish `hψ : ∀ x, ‖W.ψ x‖ = 1` using `W.ψ_std.1.2.1`. Take `⟨-, -, hBor, -⟩` from `GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso`. Use `haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))`. Establish `hemb : Continuous (embTop G)` using `GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)`. Establish `hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _)` using `GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _`.

Establish `hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besInt W φ F q.1 q.2`. Unfold `besInt`. Use `((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)` and prove the remaining obligations. Conclude with `(continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)`. Establish `hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K`.

Introduce `h n`. Unfold `besInt`. Rewrite using `[norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]`. Conclude with `mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))`. Establish `hNlt : M.νN M.fdN < ⊤` using `by rw [hM.unip.2.2]; exact ENNReal.one_lt_top`.

Use `⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩` and prove the remaining obligations. Conclude with `(hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable`. Establish `hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n` using `GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd`. Establish `hcont` using `GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT`. Conclude with `Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)`.
-/
private theorem integrableOn_besInt_of_bounded {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (M : Vol G) (hM : M.IsRow) {φ : GA D (G.V (.top 0)) → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hCφ : ∀ g, ‖φ g‖ ≤ Cφ) (hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤)
    {F : GA D (G.V (.grid D.R.m 0)) → ℂ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K) :
    (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
      IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
  have hψ : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  obtain ⟨-, -, hBor, -⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))
  have hemb : Continuous (embTop G) :=
    GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
      (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)
  have hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _) :=
    GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _
  have hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e =>
      besInt W φ F q.1 q.2 := by
    unfold besInt
    refine ((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)
    exact (continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)
  have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
    intro h n
    unfold besInt
    rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]
    exact mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
  have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
  refine ⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩
  · exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n :=
      GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd
    have hcont := GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT
    exact Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable
      (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)

/- English proof (translation)
Introduce `D T L sc G W M hM Ω hΩc hΩ φ hφ`. Establish `hcpt` using `coCpt_gridData_V_zero G`. Take `⟨haar, fund⟩` from `GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top`. Establish `hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤` using `GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩`. Establish `hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K`.

Introduce `F hF K hK h n`. Take `⟨γ, hγ, hmem⟩` from `hΩ h n`. Rewrite using `[← hF.2 γ hγ]`. Conclude with `hK _ hmem`. Establish `hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧ IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0))`.

Introduce `ψ hψ F hF`. Take `⟨Cψ, hCψ⟩` from `GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩`. Take `⟨K, hK⟩` from `hΩc.exists_bound_of_continuousOn hF.1.continuousOn`. Conclude with `integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)`. Take `⟨Cφ, hCφ⟩` from `GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩`.

Use `⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `F hF F' hF'`. Unfold `Bplus`. Use `GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_` and prove the remaining obligations. Unfold `besInt`.

Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `φ' hφ' F hF`. Unfold `Bplus`. Use `GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_` and prove the remaining obligations.

Unfold `besInt`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree. Introduce `F hF K hK`. Establish `hK'` using `hOrb F hF K hK`.

Establish `hNlt : M.νN M.fdN < ⊤` using `by rw [hM.unip.2.2]; exact ENNReal.one_lt_top`. Establish `hNr : M.νN.real M.fdN = 1` using `by simp [Measure.real, hM.unip.2.2]`. Establish `hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K`. Introduce `h n`. Unfold `besInt`.

Rewrite using `[norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]`. Conclude with `mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))`. Unfold `Bplus`. Combine the equalities or inequalities in the displayed calculation. Use `norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_` and prove the remaining obligations.

Use `norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n` as an intermediate fact. Rewrite `this` using `[hNr, mul_one]`. Then use the resulting hypothesis. Use `_ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring`.
-/
theorem bplus_add_bound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  intro D T L sc G W M hM Ω hΩc hΩ φ hφ
  have hcpt := coCpt_gridData_V_zero G
  obtain ⟨haar, fund⟩ := GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top
  have hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤ := GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩
  have hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) →
      ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K := by
    intro F hF K hK h n
    obtain ⟨γ, hγ, hmem⟩ := hΩ h n
    rw [← hF.2 γ hγ]
    exact hK _ hmem
  have hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)),
      (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧
        IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
    intro ψ hψ F hF
    obtain ⟨Cψ, hCψ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hF.1.continuousOn
    exact integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩
  refine ⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩
  · intro F hF F' hF'
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro φ' hφ' F hF
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro F hF K hK
    have hK' := hOrb F hF K hK
    have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
    have hNr : M.νN.real M.fdN = 1 := by simp [Measure.real, hM.unip.2.2]
    have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
      intro h n
      unfold besInt
      rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]
      exact mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
    unfold Bplus
    calc ‖∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)‖
        ≤ (Cφ * K) * (M.ν (.top 0)).real (M.fd (.top 0)) := by
          refine norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_
          have := norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n
          rwa [hNr, mul_one] at this
      _ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring

end GlobalTheory.BplusLaws

end
