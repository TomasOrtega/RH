import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FamilyMomentBoundOfHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomInt2
import Formalism.SharpRestriction.CuspSpanNormBounds.DiscreteSeriesWeylDimension

set_option linter.unusedVariables false

open Matrix MeasureTheory
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open NumberField Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.S.Bridge Formalism.MainNotions.LowestKTypeMultiplicity

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Unfold `cOfDpsi kaS gg`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem scale_turn (D : D7) :
    ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) * -Complex.I = cOfDpsi ((kaS D : ℝ) : ℂ) := by
  unfold cOfDpsi kaS gg
  push_cast
  ring

def LowKOneAt (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) : Prop :=
  Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ (τ : D.what₂.Tau) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ),
    l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → IsHCParam lam' →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
      IsDS (epsSH D.R) lam' σ → ∀ S S' : Submodule ℂ H,
        IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S → IsKTypeOf (epsSH D.R) σ (lowK (epsSH D.R) lam') S' → S = S'

/- English proof (translation)
Introduce `_ τ lam' _ hHC H _ _ σ hDS S S' h1 h2` and use `h _ _ _ H σ hHC hDS S S' h1 h2`.
-/
theorem lowKOneAt_of_mult (h : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne) (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ) :
    LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  fun _ τ lam' _ hHC H _ _ σ hDS S S' h1 h2 => h _ _ _ H σ hHC hDS S S' h1 h2

/- English proof (translation)
Introduce `hH τ w w' θ W hW lam' hl A hA hT hT'`. Establish `hW'` using `hW`. Take `⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩` from `hW'`. Establish `hTpos : 0 < Tz D.R.k D.R.rS W.z` using `by rw [hTz]; exact hT`. Establish `hA'` using `hA`.

Take `⟨hHC, hDSH, hB, -, hv0s, hv0ne, ⟨PS, hPS, hv0low⟩, hcN, hl2, -, -⟩` from `hA'`. Take `⟨-, hπiso, -⟩` from `rp_repOfHC _ _ W.z _ W.Wp W.π hz hTpos hc1`. Establish `hNt : Nontrivial W.Wp` using `by obtain ⟨g, -, hU⟩ := hc1; exact hU.1`. Establish `hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ` using `urep_of_DS hDSH`. Take `⟨hone, hmul, hiso⟩` from `Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hDSH`.

Establish `hS : IsHaarOn (Sset D.R.k D.R.rS W.z) (muS W.μW W.μN)` using `Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW`. Use `set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def`. Establish `hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B` using `hB`. Establish `hDSH2` using `hDSH`. Take `⟨PD, hPD, hDS'⟩` from `hDSH2`.

Take `⟨hκ, hκe⟩` from `cayley_change hPS hPD`. Establish `hDS : IsDS (epsSH D.R) lam' (fun g => A.σ (PS⁻¹ * g * PS))`. Use `dsConjK_proved _ (epsSH D.R) lam' A.H _ _ hκ hDS'` as an intermediate fact. Simplify using `only [hκe] at this`. Conclude with `this`.

Take `⟨S0, hS0⟩` from `hDS.2.2.2.2.2.1`. Establish `hset : {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (PS⁻¹ * g * PS)) (lowK (epsSH D.R) lam') S} = {S0}`. Use extensionality with `S`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `hM1 hH τ lam' hl hHC A.H _ hDS S S0 h hS0`. Introduce `h`. Rewrite using `[Set.mem_singleton_iff.1 h]`. Conclude with `hS0`. Establish `hv0S : A.v0 ∈ S0`.

Establish `h` using `hv0low`. Unfold `lowKSub at h`. Rewrite `h` using `[hset, sSup_singleton]`. Conclude with `h`. Take `⟨hfd, hst, hirr, ⟨w0, hw0S, hw0ne, hwt⟩, -⟩` from `id hS0`.

Use `hfd` as an intermediate fact. Establish `hsm : ∀ u ∈ S0, IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ u := fun u hu => hSm _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH u ⟨S0, hfd, hu, kstable_Hpk hPS hst⟩`. Establish `hS0ne : S0 ≠ ⊥`. Introduce `hb; rw [hb] at hw0S; exact hw0ne (by simpa using hw0S)`. Use `set m : ℝ := A.cN * (Module.finrank ℂ W.Wp : ℝ) with hm`.

Establish `hm0 : 0 < m` using `mul_pos hcN (by exact_mod_cast Module.finrank_pos)`. Use `set a : ℝ := ‖A.v0‖ / Real.sqrt m with ha`. Establish `hαsq : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = ((‖A.v0‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal m)⁻¹`. Rewrite using `[← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← ENNReal.ofReal_inv_of_pos hm0, ← ENNReal.ofReal_mul (sq_nonneg _)]`. Use `congr 1`.

Rewrite using `[Complex.norm_real, Real.norm_eq_abs, sq_abs, ha, div_pow, Real.sq_sqrt hm0.le, div_eq_mul_inv]`. Establish `hM0 : ENNReal.ofReal m ≠ 0` using `(ENNReal.ofReal_pos.2 hm0).ne'`. Establish `hMt : ENNReal.ofReal m ≠ ⊤` using `ENNReal.ofReal_ne_top`. Establish `hαt : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤` using `ENNReal.pow_ne_top ENNReal.coe_ne_top`. Establish `hN'` using `hN`.

Rewrite `hS`, `hq` using `[hN']`. Establish `tw : ∀ u, IsSmoothVec (k` using `D.R.k) (r := D.R.rS) A.σ u → ∀ Φ0 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable Φ0 → ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS = ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 * ∫⁻ x, Φ0 (fun i => lA D.R. …`. Introduce `u hu Φ0 hΦ0`. Rewrite using `[← twist_lintegral hLN hσ hz hTpos c1 hπiso hB1 (kapN D θ) hG hUW hS hq hu hΦ0, ← lintegral_const_mul' _ _ hαt]`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[nnnorm_smul, ENNReal.coe_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun v => (a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) v), PS, w0, ?_, ?_, hPS, ?_, hw0ne, ?_⟩` and prove the remaining obligations. Rewrite using `[← scale_turn D]`. Conclude with `bessel_smul (bessel_twist A.σ hone hmul hiso hz hB1) _`.

Introduce `v hv`. Establish `h1` using `tw v hv (fun _ => 1) measurable_const`. Simplify using `only [one_mul] at h1`. Unfold `l2SG`. Rewrite using `[h1]`.

Establish `h2` using `hBS hH τ w w' θ W hW lam' hl A hA hT v hv`. Unfold `l2SG at h2 hl2`. Rewrite `h2` using `[hl2]`. Use `beta_reduce at h2`. Rewrite using `[hαsq]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hl0 : l1 (lowK (epsSH D.R) lam') (lowK (epsSH D.R) lam') ≤ ((0 : ℕ) : ℝ)` using `by simp [l1]`. Conclude with `Submodule.subset_span ⟨_, _, _, hS0, hw0S, hwt, hl0, hl0⟩`. Introduce `F hF`. Take `⟨CF, hCF⟩` from `kinv_form hQ laLeftS_proved laRightK_proved hPS hσ hz hTpos c1 hπiso hB1 hG (by rw [hN'] at *; exact hS) (by rw [hN'] at *; exact hq) S0 hS0ne hst hirr hsm hF`.

Establish `eL : ∫⁻ x, F (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS = ENNReal.ofReal (‖A.v0‖ ^ 2) * CF` using `hCF A.v0 hv0S`. Rewrite using `[eL]`. Unfold `Emom`. Establish `ew` using `tw w0 (hsm w0 hw0S) F hF`. Establish `e2 : ∫⁻ x, (fun g => F (fun i => lA D.R.k D.R.rS W.z g i)) (Matrix.of x) * (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) w0))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS = ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal (‖w0‖ ^ 2) * CF)`.

Rewrite using `[ew, hCF w0 hw0S]`. Use `erw [e2]`. Rewrite using `[hl2]`. Establish `hw0p : ENNReal.ofReal (‖w0‖ ^ 2) ≠ 0` using `(ENNReal.ofReal_pos.2 (by positivity)).ne'`. Establish `key : ∀ (M Wn V CF : ℝ≥0∞), M ≠ 0 → M ≠ ⊤ → Wn ≠ 0 → Wn ≠ ⊤ → V * CF = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF)))`.

Introduce `M Wn V CF h1 h2 h3 h4`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[ENNReal.mul_inv_cancel h1 h2, ENNReal.inv_mul_cancel h3 h4]`. Simplify using the standard rewrite rules. Use `_ = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by ring`.

Rewrite using `[hαsq, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]`. Conclude with `key _ _ _ _ hM0 hMt hw0p ENNReal.ofReal_ne_top`.
-/
theorem momNorm'_of_at (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : LowKOneAt D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn := by
  intro hH τ w w' θ W hW lam' hl A hA hT hT'
  have hW' := hW
  obtain ⟨hc1, -, hz, -, hTz, -, hG, hUW, -, -, -, hN, hq, -⟩ := hW'
  have hTpos : 0 < Tz D.R.k D.R.rS W.z := by rw [hTz]; exact hT
  have hA' := hA
  obtain ⟨hHC, hDSH, hB, -, hv0s, hv0ne, ⟨PS, hPS, hv0low⟩, hcN, hl2, -, -⟩ := hA'
  obtain ⟨-, hπiso, -⟩ := rp_repOfHC _ _ W.z _ W.Wp W.π hz hTpos hc1
  have hNt : Nontrivial W.Wp := by obtain ⟨g, -, hU⟩ := hc1; exact hU.1
  have hσ : IsURepOn (UH (Hpk D.R.k D.R.rS)) A.σ := urep_of_DS hDSH
  obtain ⟨hone, hmul, hiso⟩ := Formalism.MainNotions.LeviCoordinates.discrete_series_unitary_rep hDSH
  have hS : IsHaarOn (Sset D.R.k D.R.rS W.z) (muS W.μW W.μN) := Formalism.MainNotions.BridgeCSB.muSHaar_of D τ w w' θ W hW
  set c1 : ℂ := ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) with hc1def
  have hB1 : IsBesselMapSm W.z (psi D.R.k D.R.rS W.z c1) A.σ W.π A.B := hB

  have hDSH2 := hDSH
  obtain ⟨PD, hPD, hDS'⟩ := hDSH2
  obtain ⟨hκ, hκe⟩ := cayley_change hPS hPD
  have hDS : IsDS (epsSH D.R) lam' (fun g => A.σ (PS⁻¹ * g * PS)) := by
    have := dsConjK_proved _ (epsSH D.R) lam' A.H _ _ hκ hDS'
    simp only [hκe] at this
    exact this
  obtain ⟨S0, hS0⟩ := hDS.2.2.2.2.2.1
  have hset : {S | IsKTypeOf (epsSH D.R) (fun g => A.σ (PS⁻¹ * g * PS)) (lowK (epsSH D.R) lam') S} = {S0} := by
    ext S
    constructor
    · intro h; exact hM1 hH τ lam' hl hHC A.H _ hDS S S0 h hS0
    · intro h; rw [Set.mem_singleton_iff.1 h]; exact hS0
  have hv0S : A.v0 ∈ S0 := by
    have h := hv0low
    unfold lowKSub at h
    rw [hset, sSup_singleton] at h
    exact h
  obtain ⟨hfd, hst, hirr, ⟨w0, hw0S, hw0ne, hwt⟩, -⟩ := id hS0
  have := hfd
  have hsm : ∀ u ∈ S0, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u :=
    fun u hu => hSm _ _ (epsSH D.R) lam' A.H A.σ hHC hDSH u ⟨S0, hfd, hu, kstable_Hpk hPS hst⟩
  have hS0ne : S0 ≠ ⊥ := by
    intro hb; rw [hb] at hw0S; exact hw0ne (by simpa using hw0S)

  set m : ℝ := A.cN * (Module.finrank ℂ W.Wp : ℝ) with hm
  have hm0 : 0 < m := mul_pos hcN (by exact_mod_cast Module.finrank_pos)
  set a : ℝ := ‖A.v0‖ / Real.sqrt m with ha
  have hαsq : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 = ((‖A.v0‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal m)⁻¹ := by
    rw [← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq, ← ENNReal.ofReal_inv_of_pos hm0,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, ha, div_pow, Real.sq_sqrt hm0.le, div_eq_mul_inv]
  have hM0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.2 hm0).ne'
  have hMt : ENNReal.ofReal m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hαt : ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 ≠ ⊤ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hN' := hN
  rw [hN'] at hS hq

  have tw : ∀ u, IsSmoothVec (k := D.R.k) (r := D.R.rS) A.σ u → ∀ Φ0 : (Fin (D.R.rS + 1) → ℝ) → ℝ≥0∞, Measurable Φ0 →
      ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) *
          (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) u))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 *
          ∫⁻ x, Φ0 (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.B (A.σ (Matrix.of x) u)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS := by
    intro u hu Φ0 hΦ0
    rw [← twist_lintegral hLN hσ hz hTpos c1 hπiso hB1 (kapN D θ) hG hUW hS hq hu hΦ0, ← lintegral_const_mul' _ _ hαt]
    refine lintegral_congr fun x => ?_
    rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]
    ring
  refine ⟨fun v => (a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) v), PS, w0, ?_, ?_, hPS, ?_, hw0ne, ?_⟩
  · rw [← scale_turn D]
    exact bessel_smul (bessel_twist A.σ hone hmul hiso hz hB1) _
  · intro v hv
    have h1 := tw v hv (fun _ => 1) measurable_const
    simp only [one_mul] at h1
    unfold l2SG
    rw [h1]
    have h2 := hBS hH τ w w' θ W hW lam' hl A hA hT v hv
    unfold l2SG at h2 hl2
    rw [hl2] at h2
    beta_reduce at h2
    rw [hαsq]
    calc (‖A.v0‖₊ : ℝ≥0∞) ^ 2 * (ENNReal.ofReal m)⁻¹ *
          ∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS
        = (ENNReal.ofReal m)⁻¹ * ((∫⁻ x, (‖A.B (A.σ (Matrix.of x) v)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS) *
            (‖A.v0‖₊ : ℝ≥0∞) ^ 2) := by ring
      _ = (ENNReal.ofReal m)⁻¹ * (ENNReal.ofReal m * (‖v‖₊ : ℝ≥0∞) ^ 2) := by rw [h2]
      _ = (‖v‖₊ : ℝ≥0∞) ^ 2 := ENNReal.inv_mul_cancel_left hM0 hMt
  · have hl0 : l1 (lowK (epsSH D.R) lam') (lowK (epsSH D.R) lam') ≤ ((0 : ℕ) : ℝ) := by simp [l1]
    exact Submodule.subset_span ⟨_, _, _, hS0, hw0S, hwt, hl0, hl0⟩
  · intro F hF
    obtain ⟨CF, hCF⟩ := kinv_form hQ laLeftS_proved laRightK_proved hPS hσ hz hTpos c1 hπiso hB1 hG
      (by rw [hN'] at *; exact hS) (by rw [hN'] at *; exact hq) S0 hS0ne hst hirr hsm hF
    have eL : ∫⁻ x, F (fun i => lA D.R.k D.R.rS W.z (Matrix.of x) i) * (‖A.Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ENNReal.ofReal (‖A.v0‖ ^ 2) * CF := hCF A.v0 hv0S
    rw [eL]
    unfold Emom
    have ew := tw w0 (hsm w0 hw0S) F hF
    have e2 : ∫⁻ x, (fun g => F (fun i => lA D.R.k D.R.rS W.z g i)) (Matrix.of x) *
        (‖(a : ℂ) • A.B (A.σ (twT D.R.k D.R.rS) (A.σ (Matrix.of x) w0))‖₊ : ℝ≥0∞) ^ 2 ∂W.νS =
        ((‖(a : ℂ)‖₊ : ℝ≥0∞)) ^ 2 * (ENNReal.ofReal (‖w0‖ ^ 2) * CF) := by
      rw [ew, hCF w0 hw0S]
    erw [e2]
    rw [hl2]
    have hw0p : ENNReal.ofReal (‖w0‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
    have key : ∀ (M Wn V CF : ℝ≥0∞), M ≠ 0 → M ≠ ⊤ → Wn ≠ 0 → Wn ≠ ⊤ →
        V * CF = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by
      intro M Wn V CF h1 h2 h3 h4
      calc V * CF = (M * M⁻¹) * ((Wn⁻¹ * Wn) * (V * CF)) := by
            rw [ENNReal.mul_inv_cancel h1 h2, ENNReal.inv_mul_cancel h3 h4]; simp
        _ = M * (Wn⁻¹ * (V * M⁻¹ * (Wn * CF))) := by ring
    rw [hαsq, Formalism.MainNotions.BesselShellMomentBounds.ofReal_norm_sq]
    exact key _ _ _ _ hM0 hMt hw0p ENNReal.ofReal_ne_top

/- English proof (translation)
The claim follows from `momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS (lowKOneAt_of_mult hM1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn) hSm hQ hLN`.
-/
theorem momNorm'_of (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 Cn : ℝ)
    (hBS : BesselSchur' D large₂ C' Cl Cg cb Cu cT CT C0 Cn) (hM1 : Formalism.MainNotions.DiscreteSeriesWeylDimension.LowKMultOne)
    (hSm : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth) (hQ : Formalism.MainNotions.LowestKTypeMultiplicity.QuotRightInv)
    (hLN : Formalism.MainNotions.S.Pv.QuotUniq.QuotLeftNorm) :
    MomNorm' D large₂ C' Cl Cg cb Cu cT CT C0 Cn :=
  momNorm'_of_at D large₂ C' Cl Cg cb Cu cT CT C0 Cn hBS (lowKOneAt_of_mult hM1 D large₂ C' Cl Cg cb Cu cT CT C0 Cn) hSm hQ hLN

end Formalism.MainNotions.S.Pv.Mom
