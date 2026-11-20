import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WithMuEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.PlaceSupp

/- English proof (translation)
Introduce `D c v hc hv hG t ht Gi hch j σ h F₁ hF₁ F₂ hF₂ x hx hne`. Establish `hs` using `Gi.hs`. Take `⟨μ, hμ, hμu, -, h2⟩` from `hch`. Take `⟨hPhi, hLev⟩` from `GlobalTheory.SeeSaw.MuUnits.withMu_eq Gi.k _ _ Gi.S (Fin D.R.t) μ hμ hμu`. Establish `a₀ : j + (2 * σ + 1 + 1 + 1) = Gi.s + 1` using `by omega`.

Establish `a₁ : j + 1 + (2 * σ + 1 + 1) = Gi.s + 1` using `by omega`. Establish `a₂ : j + 1 + 1 + (2 * σ + 1) = Gi.s + 1` using `by omega`. Establish `b₀ : j + (2 * σ + 1 + 1) = Gi.s` using `by omega`. Establish `b₁ : j + 1 + (2 * σ + 1) = Gi.s` using `by omega`. Take `⟨T₁, hT₁, hO₁⟩` from `(GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1)) (Gi.FY j _ a₀) (Gi.FY (j + 1) _ a₁) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ a₀) (Gi.latY (j …`.

Take `⟨T₂, hT₂, hO₂⟩` from `(GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V (j + 1)) (c.V (j + 1 + 1)) (Gi.FY (j + 1) _ a₁) (Gi.FY (j + 1 + 1) _ a₂) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N (j + 1)) (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) ( …`. Take `⟨O₁, h1⟩` from `GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1)) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))`. Take `⟨O₂, h1'⟩` from `GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1)) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))`. Establish `m₁ : (Gi.S.T (Fin D.R.t)).Phi j _ b₀ ∈ GlobalTheory.SplitWeil.SB _` using `(GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ b₀`. Establish `m₂ : (Gi.S.T (Fin D.R.t)).Phi (j + 1) _ b₁ ∈ GlobalTheory.SplitWeil.SB _` using `(GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 (j + 1) _ b₁`.

Establish `e₁` using `(Gi.eg_is j _ b₀).2 T₁ hT₁ O₁ ⟨_, m₁⟩ h1 rfl`. Establish `e₂` using `(Gi.eg_is (j + 1) _ b₁).2 T₂ hT₂ O₂ ⟨_, m₂⟩ h1' rfl`. Rewrite `e₁` using `[hO₁ O₁ h1]`. Rewrite `e₂` using `[hO₂ O₂ h1']`. Rewrite `hne` using `[← e₁, ← e₂, ← (ht.sFB j σ h).1]`.

Set `F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1)) (GlobalTheory.StepData.XIx (Fin D. …` to `{ s := Gi.sc j s_ne := fun h0 => by`. Establish `h3` using `Gi.sc_unit j`. Rewrite `h3` using `[h0, map_zero]`. Conclude with `zero_ne_one h3`. Use `F₀ := Gi.FX j (by omega)`.

Use `F₁ := Gi.FX (j + 1) (by omega)`. Use `F₂ := Gi.FX (j + 1 + 1) (by omega)`. Use `G₀ := Gi.FY j _ a₀`. Use `G₁ := Gi.FY (j + 1) _ a₁`. Use `G₂ := Gi.FY (j + 1 + 1) _ a₂`.

Use `bes := Gi.bes j (σ + 1) h _ a₀`. Use `jac := Gi.jac j (σ + 1) h _ a₁`. Use the proof step `bes' := by`. Rewrite using `[← Gi.sc_step j]`. Conclude with `Gi.bes (j + 1 + 1) σ (idx_step h) _ a₂ }`.

Take `⟨r, hr, hrs, u, uk, hu, huk, hxr⟩` from `hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμ) (Fin D.R.t) c.ψ Gi.char j (2 * σ) (by omega) σ _ _ _ F (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (h2 j σ h).1 T₁ T₂ hT₁ hT₂ ⟨_, m₁⟩ ⟨_, m₂⟩ (hPhi j _ b₀).symm (hPhi (j + 1) _ b₁).symm x hx …`. Rewrite `huk` using `[(hLev (j + 1 + 1) _ a₂).1]`. Conclude with `⟨r, hr, hrs, u, uk, hu, huk, hxr⟩`.
-/
theorem supp_ctr : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F₁ hF₁ F₂ hF₂ x hx hne
  have hs := Gi.hs
  obtain ⟨μ, hμ, hμu, -, h2⟩ := hch
  obtain ⟨hPhi, hLev⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq Gi.k _ _ Gi.S (Fin D.R.t) μ hμ hμu
  have a₀ : j + (2 * σ + 1 + 1 + 1) = Gi.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = Gi.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = Gi.s + 1 := by omega
  have b₀ : j + (2 * σ + 1 + 1) = Gi.s := by omega
  have b₁ : j + 1 + (2 * σ + 1) = Gi.s := by omega
  obtain ⟨T₁, hT₁, hO₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1)) (Gi.FY j _ a₀) (Gi.FY (j + 1) _ a₁)
    c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (Gi.latY j _ a₀) (Gi.latY (j + 1) _ a₁)).2 F₁ hF₁
  obtain ⟨T₂, hT₂, hO₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V (j + 1)) (c.V (j + 1 + 1)) (Gi.FY (j + 1) _ a₁)
    (Gi.FY (j + 1 + 1) _ a₂) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N (j + 1)) (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega))
    (hv.sd (j + 1 + 1) (by omega)) (Gi.latY (j + 1) _ a₁) (Gi.latY (j + 1 + 1) _ a₂)).2 F₂ hF₂
  obtain ⟨O₁, h1⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, h1'⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have m₁ : (Gi.S.T (Fin D.R.t)).Phi j _ b₀ ∈ GlobalTheory.SplitWeil.SB _ := (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ b₀
  have m₂ : (Gi.S.T (Fin D.R.t)).Phi (j + 1) _ b₁ ∈ GlobalTheory.SplitWeil.SB _ :=
    (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 (j + 1) _ b₁
  have e₁ := (Gi.eg_is j _ b₀).2 T₁ hT₁ O₁ ⟨_, m₁⟩ h1 rfl
  have e₂ := (Gi.eg_is (j + 1) _ b₁).2 T₂ hT₂ O₂ ⟨_, m₂⟩ h1' rfl
  rw [hO₁ O₁ h1] at e₁
  rw [hO₂ O₂ h1'] at e₂
  rw [← e₁, ← e₂, ← (ht.sFB j σ h).1] at hne
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by
        have h3 := Gi.sc_unit j
        rw [h0, map_zero] at h3
        exact zero_ne_one h3
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j _ a₀
      G₁ := Gi.FY (j + 1) _ a₁
      G₂ := Gi.FY (j + 1 + 1) _ a₂
      bes := Gi.bes j (σ + 1) h _ a₀
      jac := Gi.jac j (σ + 1) h _ a₁
      bes' := by
        rw [← Gi.sc_step j]
        exact Gi.bes (j + 1 + 1) σ (idx_step h) _ a₂ }
  obtain ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμ) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ F (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (h2 j σ h).1
    T₁ T₂ hT₁ hT₂ ⟨_, m₁⟩ ⟨_, m₂⟩ (hPhi j _ b₀).symm (hPhi (j + 1) _ b₁).symm x hx hne
  rw [(hLev (j + 1 + 1) _ a₂).1] at huk
  exact ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩

end GlobalTheory.SeeSaw.PlaceSupp

end
