import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomFinal
import Formalism.SharpRestriction.CuspSpanNormBounds.FamilyDoubleCosetBesselBoundOfGap
import Formalism.SharpRestriction.CuspSpanNormBounds.ExpansionFromLemmaB
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.BesselNVGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.MomNorm

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace Formalism.L2.S.Pv.Mom

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Bridge Formalism.MainNotions.CayleySignature

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ParamTie (D : D7) (Cn : ℝ) : Prop :=
  ∀ (τ : D.what₂.Tau) (w : D.what₂.Word) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    0 < kaS D ∧ (∃ h : ℝ, GapAtLeast (epsSH D.R) lam' h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK D.R.k D.R.rS h) ∧
      2 ≤ D.R.k ∧ Even D.R.k ∧ eps48 D.R.k D.R.rS = epsSH D.R ∧ IsHCParam (fun i => ((D.hcW w τ).u i : ℝ)) ∧
      ∃ (v : Fin (D.R.k - 1) → ℝ) (b : Fin (2 * D.R.rS + 2) → ℝ), lam' = lam48 D.R.k D.R.rS v b ∧
        InterlacingCondition D.R.k D.R.rS (fun i => ((D.hcW w τ).u i : ℝ)) v b ∧
        HalfIntegralDifference D.R.k D.R.rS (fun i => ((D.hcW w τ).u i : ℝ)) v b ∧ GapBig D.R.k D.R.rS b

def ParamTieF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ Cn, Formalism.MainNotions.S.OwnEv Fm fun C' Cl x i =>
    Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 → ParamTie (Fm.D x i) Cn

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `psiGen psi ell ellA`. Rewrite using `[Finset.mul_sum]`.
-/
theorem psiGen_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold psiGen psi ell ellA
  rw [Finset.mul_sum]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA psi ell`. Rewrite using `[Finset.mul_sum]`.
-/
theorem psiGenPI_const {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) :
    PI.BesselMapUniq.psiGen k r z (fun _ => c) = psi k r z c := by
  funext g
  unfold PI.BesselMapUniq.psiGen PI.BesselMapUniq.ellA psi ell
  rw [Finset.mul_sum]

variable [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in
/- English proof (translation)
Introduce `hH τ w w' θ W hW lam' hl A hA hTw v hv`. Take `⟨hka, ⟨h, hgap, hok⟩, hk2, hkev, heps, huHC, vv, bb, hlam, hint, hhalf, hgb⟩` from `hT hH τ w lam' hl hA.1`. Establish `hW'` using `hW`. Take `⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩` from `hW'`. Establish `hTpos : 0 < Tz D.R.k D.R.rS W.z` using `by rw [hTz]; exact hTw`.

Establish `hA'` using `hA`. Take `⟨hHC, hDSH, hB, -, hv0s, hv0ne, -, hcN, hl2, -, -⟩` from `hA'`. Establish `hκtop : kapN D θ ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hκ0 : kapN D θ ≠ 0`. Introduce `h0`.

Establish `hμN : W.μN = 0` using `by rw [hN, h0]; unfold haarLie; rw [zero_smul]`. Establish `hS0 : muS W.μW W.μN = 0` using `by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]`. Establish `h1` using `hq (fun _ => 1) measurable_const`. Rewrite `h1` using `[hS0]`. Simplify using `at h1`.

Conclude with `hG.2.1 h1`. Establish `hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN`. Rewrite using `[hN]`. Conclude with `Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκtop`. Use `set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def`.

Establish `hc1ne : c1 ≠ 0`. Establish `e : (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) = 2 * kaS D`. Unfold `kaS gg`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc1def, e]`.

Conclude with `Complex.ofReal_ne_zero.mpr (by positivity)`. Establish `hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B` using `hB`. Establish `hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ` using `Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hDSH`. Establish `hDSH2` using `hDSH`. Take `⟨PD, hPD, hDSd⟩` from `hDSH2`.

Take `⟨S, hS⟩` from `hDSd.2.2.2.2.2.1`. Take `⟨v1, hv1S, hv10, -⟩` from `hS.2.2.2.1`. Use `set w0 : A.H := ((‖v1‖⁻¹ : ℝ) : ℂ) • v1 with hw0def`. Establish `hw0 : IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0`. Use `⟨PD, hPD, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]`. Conclude with `inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv10)`. Conclude with `(le_sSup (show S ∈ {S | IsKTypeOf (epsSH D.R) _ (lowK (epsSH D.R) lam') S} from hS)) (S.smul_mem _ hv1S)`. Establish `hw0sm : IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ w0 := hI.2.2.1 _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH w0 ⟨S, hS.1, S.smul_mem _ hv1S, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hPD hS.2.1⟩`. Establish `hsmx : ∀ x ∈ UH (Hpk D.R.k D.R.rS), IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ (A.σ x w0) := fun x hx => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw0sm hx`.

Establish `hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam' h A.σ w0 W.z c1 (fun i => ((D.hcW w τ).u i : ℝ)) W.π W.μW W.μN W.μG W.νS` using `⟨hHC, hDSH, hgap, hok, hw0, hz, hTpos, hc1ne, hc1, hUW, hNH, hG, hq⟩`. Take `⟨l, hlB, hla, hlb⟩` from `hAt hI _ _ _ _ h A.H A.σ w0 W.Wp W.z c1 _ W.π W.μW W.μN W.μG W.νS hSide`. Establish `hNV` using `Formalism.L2.SG.LitS.PfNVG.besselNVG D.R.k D.R.rS W.z (fun _ => c1) _ vv bb hk2 hkev hz hTpos (fun _ => hc1ne) huHC (by rw [← hlam]; exact hHC) hint hhalf hgb A.H A.σ (by rw [heps, ← hlam]; exact hDSH) W.Wp W.π hc1 w0 (by rw [heps, ← hlam]; exact hw0) W.μW W.μN hUW hNH`. Take `⟨x, x₀, hx, hx₀, hne⟩` from `hNV`. Rewrite `hne` using `[psiGen_const]`.

Establish `hadm : Formalism.FourierDecayAlt.ThreeDimData.IsAdm A.σ w0 (A.σ x₀ w0)` using `Or.inl (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)`. Take `⟨-, heq⟩` from `hla (A.σ x w0) (hsmx x hx) (A.σ x₀ w0) hadm`. Establish `hlv : l (A.σ x₀ w0) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Rewrite using `[heq, h0]`. Use extensionality with `y`. Simplify using the standard rewrite rules. Take `⟨d, hd, hSch⟩` from `Formalism.MainNotions.DiscreteSeriesInnerProducts.schurH A.σ hDSH hG`. Establish `hfd : ∀ u : A.H, u ≠ 0 → fdegH W.μG A.σ u = d` using `fun u hu => Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegH_eq hd (fun v w v' w' => (hSch v w v' w').2) hu`.

Establish `hl0 : l 0 = 0`. Use `hlB.2.1 0 0 (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero)` as an intermediate fact. Simplify using `using this`. Establish `hlp : 0 < ‖l (A.σ x₀ w0)‖ ^ 2` using `by positivity`. Establish `hl2l : ∀ u, IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ u → l2SG W.νS (fun g => l (A.σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / d) := by`.

Introduce `u hu`. Distinguish the cases in `hu0 : u = 0`. Substitute `hu0` using the available equality. Unfold `l2SG`. Simplify using `[hl0]`.

Establish `e` using `hlb u hu hu0 _ hadm`. Establish `e2 : ENNReal.ofReal (‖u‖ ^ 2 * ‖l (A.σ x₀ w0)‖ ^ 2 / fdegH W.μG A.σ u) = ENNReal.ofReal (‖l (A.σ x₀ w0)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d)`. Rewrite using `[hfd u hu0, ← ENNReal.ofReal_mul hlp.le]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Use `erw [e2] at e`. Conclude with `(ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hlp).ne' ENNReal.ofReal_ne_top).1 e`. Take `⟨α, β, hαβ, hrel⟩` from `hI.2.2.2 _ _ (epsSH D.R) lam' A.H A.σ W.z (fun _ => c1) _ W.Wp W.π hHC hDSH hz hTpos (fun _ => hc1ne) hc1 A.B l (by rw [psiGenPI_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mp hB1) (by rw [psiGenPI_const]; exact hlB)`. Establish `hα : α ≠ 0`. Introduce `h0`.

Break down `hαβ with h1 | h1` into its components or cases. Conclude with `h1 h0`. Establish `e` using `hrel _ (hsmx x₀ hx₀)`. Rewrite `e` using `[h0, zero_smul, zero_add]`. Conclude with `hlv ((smul_eq_zero.1 e).resolve_left h1)`.

Establish `hBl : ∀ u, IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ u → A.B u = (-(β / α)) • l u := by`. Introduce `u hu`. Establish `e` using `hrel u hu`. Establish `e2 : α • A.B u = -(β • l u)` using `eq_neg_of_add_eq_zero_left e`. Combine the equalities or inequalities in the displayed calculation.

Establish `hS'` using `Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW`. Establish `hae : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS)`. Rewrite using `[ae_iff]`. Conclude with `Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS' hq`. Establish `hl2B : ∀ u, IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ u → l2SG W.νS (fun g => A.B (A.σ g u)) = ENNReal.ofReal (‖-(β / α)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by`.

Introduce `u hu`. Rewrite using `[← hl2l u hu]`. Unfold `l2SG`. Rewrite using `[← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with y hy`. Rewrite using `[hBl _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hu hy), nnnorm_smul, ENNReal.coe_mul, mul_pow, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]`. Establish `hΦ : l2SG W.νS A.Φ = l2SG W.νS (fun g => A.B (A.σ g A.v0))` using `rfl`. Rewrite using `[hΦ, hl2B v hv, hl2B A.v0 hv0s, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq A.v0, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq v, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), …`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem besselSchur'_of_tie (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne)
    (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hT : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ParamTie D Cn) :
    Formalism.MainNotions.S.Pv.Mom.BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hTw v hv
  obtain ⟨hka, ⟨h, hgap, hok⟩, hk2, hkev, heps, huHC, vv, bb, hlam, hint, hhalf, hgb⟩ := hT hH τ w lam' hl hA.1
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hTw
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, -, hcN, hl2, -, -⟩ := hA'

  have hκtop : kapN D θ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hκ0 : kapN D θ ≠ 0 := by
    intro h0
    have hμN : W.μN = 0 := by rw [hN, h0]; unfold haarLie; rw [zero_smul]
    have hS0 : muS W.μW W.μN = 0 := by unfold muS; rw [hμN, Measure.prod_zero, Measure.map_zero]
    have h1 := hq (fun _ => 1) measurable_const
    rw [hS0] at h1
    simp at h1
    exact hG.2.1 h1
  have hNH : IsHaarOn (Nset D.R.k D.R.rS) W.μN := by
    rw [hN]; exact Formalism.MainNotions.BridgeCSB.haarLieN _ _ _ hκ0 hκtop

  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hc1ne : c1 ≠ 0 := by
    have e : (2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) = 2 * kaS D := by
      unfold kaS gg; ring
    rw [hc1def, e]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hDSH

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDSd⟩ := hDSH2
  obtain ⟨S, hS⟩ := hDSd.2.2.2.2.2.1
  obtain ⟨v1, hv1S, hv10, -⟩ := hS.2.2.2.1
  set w0 : A.H := ((‖v1‖⁻¹ : ℝ) : ℂ) • v1 with hw0def
  have hw0 : IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := by
    refine ⟨PD, hPD, ?_, ?_⟩
    · rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv10)
    · exact (le_sSup (show S ∈ {S | IsKTypeOf (epsSH D.R) _ (lowK (epsSH D.R) lam') S} from hS)) (S.smul_mem _ hv1S)
  have hw0sm : IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ w0 :=
    hI.2.2.1 _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH w0
      ⟨S, hS.1, S.smul_mem _ hv1S, Formalism.MainNotions.LowestKTypeMultiplicity.kstable_Hpk hPD hS.2.1⟩
  have hsmx : ∀ x ∈ UH (Hpk D.R.k D.R.rS), IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ (A.σ x w0) :=
    fun x hx => Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hw0sm hx

  have hSide : Formalism.FourierDecayAlt.ThreeDimData.Side D.R.k D.R.rS (epsSH D.R) lam' h A.σ w0 W.z c1 (fun i => ((D.hcW w τ).u i : ℝ))
      W.π W.μW W.μN W.μG W.νS :=
    ⟨hHC, hDSH, hgap, hok, hw0, hz, hTpos, hc1ne, hc1, hUW, hNH, hG, hq⟩
  obtain ⟨l, hlB, hla, hlb⟩ := hAt hI _ _ _ _ h A.H A.σ w0 W.Wp W.z c1 _ W.π W.μW W.μN W.μG W.νS hSide

  have hNV := Formalism.L2.SG.LitS.PfNVG.besselNVG D.R.k D.R.rS W.z (fun _ => c1) _ vv bb hk2 hkev hz hTpos
    (fun _ => hc1ne) huHC (by rw [← hlam]; exact hHC) hint hhalf hgb A.H A.σ (by rw [heps, ← hlam]; exact hDSH)
    W.Wp W.π hc1 w0 (by rw [heps, ← hlam]; exact hw0) W.μW W.μN hUW hNH
  obtain ⟨x, x₀, hx, hx₀, hne⟩ := hNV
  rw [psiGen_const] at hne
  have hadm : Formalism.FourierDecayAlt.ThreeDimData.IsAdm A.σ w0 (A.σ x₀ w0) := Or.inl (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
  obtain ⟨-, heq⟩ := hla (A.σ x w0) (hsmx x hx) (A.σ x₀ w0) hadm
  have hlv : l (A.σ x₀ w0) ≠ 0 := by
    intro h0
    apply hne
    rw [heq, h0]
    ext y
    simp

  obtain ⟨d, hd, hSch⟩ := Formalism.MainNotions.DiscreteSeriesInnerProducts.schurH A.σ hDSH hG
  have hfd : ∀ u : A.H, u ≠ 0 → fdegH W.μG A.σ u = d :=
    fun u hu => Formalism.MainNotions.DiscreteSeriesInnerProducts.fdegH_eq hd (fun v w v' w' => (hSch v w v' w').2) hu
  have hl0 : l 0 = 0 := by
    have := hlB.2.1 0 0 (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_zero)
    simpa using this
  have hlp : 0 < ‖l (A.σ x₀ w0)‖ ^ 2 := by positivity
  have hl2l : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => l (A.σ g u)) = ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    by_cases hu0 : u = 0
    · subst hu0
      unfold l2SG
      simp [hl0]
    · have e := hlb u hu hu0 _ hadm
      have e2 : ENNReal.ofReal (‖u‖ ^ 2 * ‖l (A.σ x₀ w0)‖ ^ 2 / fdegH W.μG A.σ u) =
          ENNReal.ofReal (‖l (A.σ x₀ w0)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
        rw [hfd u hu0, ← ENNReal.ofReal_mul hlp.le]
        congr 1
        ring
      erw [e2] at e
      exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hlp).ne' ENNReal.ofReal_ne_top).1 e

  obtain ⟨α, β, hαβ, hrel⟩ := hI.2.2.2 _ _ (epsSH D.R) lam' A.H A.σ W.z (fun _ => c1) _ W.Wp W.π hHC hDSH hz hTpos
    (fun _ => hc1ne) hc1 A.B l (by rw [psiGenPI_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).mp hB1)
    (by rw [psiGenPI_const]; exact hlB)
  have hα : α ≠ 0 := by
    intro h0
    rcases hαβ with h1 | h1
    · exact h1 h0
    · have e := hrel _ (hsmx x₀ hx₀)
      rw [h0, zero_smul, zero_add] at e
      exact hlv ((smul_eq_zero.1 e).resolve_left h1)
  have hBl : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → A.B u = (-(β / α)) • l u := by
    intro u hu
    have e := hrel u hu
    have e2 : α • A.B u = -(β • l u) := eq_neg_of_add_eq_zero_left e
    calc A.B u = α⁻¹ • (α • A.B u) := by rw [smul_smul, inv_mul_cancel₀ hα, one_smul]
      _ = α⁻¹ • (-(β • l u)) := by rw [e2]
      _ = (-(β / α)) • l u := by rw [smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]

  have hS' := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  have hae : ∀ᵐ y ∂W.νS, Matrix.of y ∈ UH (Hpk D.R.k D.R.rS) := by
    rw [ae_iff]; exact Formalism.MainNotions.BesselShellMomentBounds.quot_conc W.z W.μG _ W.νS hG hS' hq
  have hl2B : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u →
      l2SG W.νS (fun g => A.B (A.σ g u)) = ENNReal.ofReal (‖-(β / α)‖ ^ 2) * ENNReal.ofReal (‖u‖ ^ 2 / d) := by
    intro u hu
    rw [← hl2l u hu]
    unfold l2SG
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with y hy
    rw [hBl _ (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hu hy), nnnorm_smul, ENNReal.coe_mul, mul_pow,
      Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
  have hΦ : l2SG W.νS A.Φ = l2SG W.νS (fun g => A.B (A.σ g A.v0)) := rfl
  rw [hΦ, hl2B v hv, hl2B A.v0 hv0s, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq A.v0, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq v,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

variable [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

/- English proof (translation)
Introduce `Cn` and use `Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => besselSchur'_of_tie hI hAt _ _ _ _ _ _ _ _ _ _ Cn h) (hT Cn)`.
-/
theorem besselSchurF'_of_tie (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne)
    {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) (hT : ParamTieF Fm Cg cb Cu cT CT C0) :
    Formalism.MainNotions.S.Pv.Mom.BesselSchurF' Fm Cg cb Cu cT CT C0 :=
  fun Cn => Formalism.MainNotions.S.OwnEv.mono (fun C' Cl x i h => besselSchur'_of_tie hI hAt _ _ _ _ _ _ _ _ _ _ Cn h) (hT Cn)

variable [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

/- English proof (translation)
The claim follows from `momF' Fm Cg cb Cu cT CT C0 (besselSchurF'_of_tie hI hAt Fm Cg cb Cu cT CT C0 hT) hM1`.
-/
theorem momF'_of_tie (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Cg cb Cu cT CT C0 : ℝ) (hT : ParamTieF Fm Cg cb Cu cT CT C0) :
    Formalism.MainNotions.S.Pv.Mom.MomF' Fm Cg cb Cu cT CT C0 :=
  momF' Fm Cg cb Cu cT CT C0 (besselSchurF'_of_tie hI hAt Fm Cg cb Cu cT CT C0 hT) hM1

end Formalism.L2.S.Pv.Mom
