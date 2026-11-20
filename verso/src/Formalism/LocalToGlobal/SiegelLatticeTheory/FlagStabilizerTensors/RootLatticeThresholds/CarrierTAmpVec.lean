import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.AmpOrbCoef
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AmpOrbClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTCoef

open MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.AmpOrbPf

/- English proof (translation)
Take `⟨h, hg, hok, hcell⟩` from `hGap hH τ lam' hl`. Use `set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL`. Use `set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def`. Take `⟨l, l', hl1, hl1', hOP⟩` from `ls_pair hI hAt hW hA hT hT' hg hok`. Establish `hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0` using `lowest_K_type_unit hA`.

Establish `hKS : PI.KFinSmooth` using `hI.2.2.1`. Establish `hJ : PI.BesselMapUniq.BesselMapUniq` using `hI.2.2.2`. Establish `hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG` using `hW.2.2.2.2.2.2.1`. Establish `hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k` using `D.R.k) (r := D.R.rS) A.σ := Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0`. Take `⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩` from `hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0`.

Establish `hlx : l x ≠ 0`. Introduce `h0`. Apply `hxy` to reduce the goal to its premises. Establish `e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x)` using `hOP.1.2.2.2.2.2.1 x hx y hy`. Rewrite using `[e, h0]`.

Use `ext`. Simplify using the standard rewrite rules. Establish `hlx' : l' x' ≠ 0`. Introduce `h0`. Apply `hxy'` to reduce the goal to its premises.

Establish `e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x')` using `hOP.1.2.2.2.2.2.2 x' hx' y' hy'`. Rewrite using `[e, h0]`. Use `ext`. Simplify using the standard rewrite rules. Establish `hB : PI.BesselMapUniq.IsBesselMapSm (k` using `D.R.k) (r := D.R.rS) W.z (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by`.

Rewrite using `[psiGen_const]`. Conclude with `(Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1`. Establish `hB' : PI.BesselMapUniq.IsBesselMapSm (k` using `D.R.k) (r := D.R.rS) W.z' (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by`. Rewrite using `[psiGen_const]`. Conclude with `(Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1`.

Establish `hlG : PI.BesselMapUniq.IsBesselMapSm (k` using `D.R.k) (r := D.R.rS) W.z (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by`. Rewrite using `[psiGen_const]`. Conclude with `hl1`. Establish `hlG' : PI.BesselMapUniq.IsBesselMapSm (k` using `D.R.k) (r := D.R.rS) W.z' (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by`. Rewrite using `[psiGen_const]`.

Conclude with `hl1'`. Take `⟨c0, hc0⟩` from `Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG ⟨x, hDDs x hx, hlx⟩`. Take `⟨c0', hc0'⟩` from `Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG' ⟨x', hDDs x' hx', hlx'⟩`. Establish `has : a ∈ PI.UpqRep.smoothVecs (k` using `D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 a hka`. Establish `hbs : b ∈ PI.UpqRep.smoothVecs (k` using `D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 b hkb`.

Establish `hBa : A.B a = c0 • l a` using `hc0 a has`. Establish `hBb : A.B' b = c0' • l' b` using `hc0' b hbs`. Rewrite `hn` using `[hBa, hBb, inner_smul_left, inner_smul_right]`. Establish `hc0ne : c0 ≠ 0`. Introduce `h0`.

Apply `hn` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Establish `hc0ne' : c0' ≠ 0`. Introduce `h0`.

Apply `hn` to reduce the goal to its premises. Rewrite using `[h0]`. Simplify using the standard rewrite rules. Use `set s : ℂ := ⟪l a, ξ⟫_ℂ * ⟪ξ', l' b⟫_ℂ with hs`. Establish `hs0 : s ≠ 0`.

Introduce `h0`. Apply `hn` to reduce the goal to its premises. Establish `: (starRingEnd ℂ) c0 * ⟪l a, ξ⟫_ℂ * (c0' * ⟪ξ', l' b⟫_ℂ) = (starRingEnd ℂ) c0 * c0' * s`. Rewrite using `[hs]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, h0, mul_zero]`. Use `set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht`. Establish `hv0ne : A.v0 ≠ 0` using `hA.2.2.2.2.2.1`. Establish `hv0 : A.v0 = t • w0`. Rewrite using `[hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne), Complex.ofReal_one, one_smul]`.

Establish `hw0s : w0 ∈ PI.UpqRep.smoothVecs (k` using `D.R.k) (r := D.R.rS) A.σ := Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1`. Establish `hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0)`. Introduce `g hg'`. Use `show A.B (A.σ g A.v0) = _`. Rewrite using `[hv0]`.

Conclude with `orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'`. Establish `hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0)`. Introduce `g hg'`. Use `show A.B' (A.σ g A.v0) = _`. Rewrite using `[hv0]`.

Conclude with `orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'`. Establish `ht0 : t ≠ 0`. Rewrite using `[ht]`. Conclude with `(norm_ne_zero_iff.mpr hv0ne)` after adjusting the coercions. Establish `hcN : (A.cN : ℂ) ≠ 0` using `by exact_mod_cast (ne_of_gt hA.2.2.2.2.2.2.2.1)`.

Use `set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1`. Establish `hK10 : K1 ≠ 0`. Rewrite using `[hK1]`. Use `mul_ne_zero (mul_ne_zero (inv_ne_zero hcN) (mul_ne_zero hc0ne ht0)) ?_` and prove the remaining obligations. Conclude with `(map_ne_zero _).mpr (mul_ne_zero hc0ne' ht0)`.

Establish `hw1 : ‖w0‖ = 1`. Rewrite using `[hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]`. Conclude with `inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)`. Use `set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg`. Establish `hdg0 : dg ≠ 0`.

Rewrite using `[hdg]`. Conclude with `(ne_of_gt (Formalism.L2.S.Pv.AmpOrbCoef.fdegH_pos hA.1 hA.2.1 hG hw1))` after adjusting the coercions. Use `⟨dg * s * K1⁻¹, mul_ne_zero (mul_ne_zero hdg0 hs0) (inv_ne_zero hK10), ?_⟩` and prove the remaining obligations. Introduce `γ μR νR ν hCD`. Take `⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩` from `hCD`.

Establish `hCD' : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν` using `⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩`. Take `⟨bb, hb0, hbm, hbi⟩` from `hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD' hMono`. Establish `hAmp` using `hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD' bb hb0 hbm hbi a b hka hkb ξ ξ'`. Establish `hae` using `ae_UH_conj hγ hG hRH hqR`. Establish `hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ` using `ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae`.

Establish `hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν` using `hAmp`. Establish `e1 : OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν = dg • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ)`. Rewrite using `[hAmp']`. Conclude with `(smul_inv_smul₀ hdg0 _).symm`. Establish `e2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = K1⁻¹ • A.J νR γ`.

Rewrite using `[hJ1, smul_smul, inv_mul_cancel₀ hK10, one_smul]`. Rewrite using `[e1, e2]`. Simplify using `only [smul_smul, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem ampVec_gen (hI : Formalism.FourierDecayAlt.ThreeDimData.Inputs) (hAt : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOne) (hAKF : Formalism.MainNotions.S.Pv.AmpDD.AmpKF)
    (hCC : Formalism.MainNotions.S.Pv.AmpDD.CellConv) {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT C0 Cn : ℝ}
    (hGap : Formalism.MainNotions.S.Pv.AmpDD.GapOfHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hNV : Formalism.MainNotions.S.Pv.AmpDD.NVHyp D large₂ C' Cl Cg cb Cu cT CT C0 Cn)
    (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0) (τ : D.what₂.Tau) (w w' : D.what₂.Word) (hTT : HypTT D w w')
    (θ : ℝ) (W : LocW D.R.k D.R.rS) (hW : GoodW D τ w w' θ W) (lam' : Fin (2 * D.R.rS + D.R.k + 1) → ℝ)
    (hl : l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3) (A : LocS W) (hA : GoodS D lam' A)
    (hT : 0 < Tr D w) (hT' : 0 < Tr D w') (a b : A.H) (ξ : W.Wp) (ξ' : W.Wq)
    (hka : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ a)
    (hkb : PI.UpqRep.IsKFinHpk (k := D.R.k) (r := D.R.rS) A.σ b)
    (hn : ⟪A.B a, ξ⟫_ℂ * ⟪ξ', A.B' b⟫_ℂ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ w w' θ W lam' A hW hA hT hT') W.μG γ μR νR ν →
      OrbInt (toBessel D τ w w' θ W lam' A hW hA hT hT')
        (Formalism.MainNotions.S.Pv.AmpDD.coefF (toBessel D τ w w' θ W lam' A hW hA hT hT') a b ξ ξ') γ ν = κ • A.J νR γ := by
  obtain ⟨h, hg, hok, hcell⟩ := hGap hH τ lam' hl
  set L := toBessel D τ w w' θ W lam' A hW hA hT hT' with hL
  set w0 : A.H := (((‖A.v0‖⁻¹ : ℝ) : ℂ) • A.v0) with hw0def
  obtain ⟨l, l', hl1, hl1', hOP⟩ := ls_pair hI hAt hW hA hT hT' hg hok
  have hw0 : PI.UpqRep.IsLowUnitH D.R.k D.R.rS (epsSH D.R) lam' A.σ w0 := lowest_K_type_unit hA
  have hKS : PI.KFinSmooth := hI.2.2.1
  have hJ : PI.BesselMapUniq.BesselMapUniq := hI.2.2.2
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  have hDDs : ∀ x ∈ Formalism.FourierDecayAlt.ThreeDimData.DDsp A.σ w0, x ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.DD_smooth hKS hA.1 hA.2.1 hw0
  obtain ⟨⟨x, hx, y, hy, hxy⟩, ⟨x', hx', y', hy', hxy'⟩⟩ :=
    hNV hH τ w w' hTT θ W hW lam' hl A hA hT hT' w0 hw0
  have hlx : l x ≠ 0 := by
    intro h0; apply hxy
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z L.c W.π A.σ W.μW L.μN x y = (innerSL ℂ (l y)).smulRight (l x) :=
      hOP.1.2.2.2.2.2.1 x hx y hy
    rw [e, h0]; ext; simp
  have hlx' : l' x' ≠ 0 := by
    intro h0; apply hxy'
    have e : Formalism.FourierDecayAlt.ThreeDimData.be W.z' L.c W.π' A.σ W.μW' L.μN x' y' = (innerSL ℂ (l' y')).smulRight (l' x') :=
      hOP.1.2.2.2.2.2.2 x' hx' y' hy'
    rw [e, h0]; ext; simp
  have hB : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π A.B := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.1
  have hB' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' A.B' := by
    rw [psiGen_const]; exact (Formalism.MainNotions.BridgeCS3d.isBesselMapSm_iff _ _ _ _ _).1 hA.2.2.2.1
  have hlG : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z (fun _ => L.c)) A.σ W.π l := by
    rw [psiGen_const]; exact hl1
  have hlG' : PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z'
      (PI.BesselMapUniq.psiGen D.R.k D.R.rS W.z' (fun _ => L.c)) A.σ W.π' l' := by
    rw [psiGen_const]; exact hl1'
  obtain ⟨c0, hc0⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz.1 L.hz.2 (fun _ => c_ne_zero D) L.hπ hB hlG
    ⟨x, hDDs x hx, hlx⟩
  obtain ⟨c0', hc0'⟩ := Formalism.MainNotions.S.Pv.AIsL.aIsL hJ hA.1 hA.2.1 L.hz'.1 L.hz'.2 (fun _ => c_ne_zero D) L.hπ' hB' hlG'
    ⟨x', hDDs x' hx', hlx'⟩

  have has : a ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 a hka
  have hbs : b ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ := hKS _ _ _ _ _ A.σ hA.1 hA.2.1 b hkb
  have hBa : A.B a = c0 • l a := hc0 a has
  have hBb : A.B' b = c0' • l' b := hc0' b hbs
  rw [hBa, hBb, inner_smul_left, inner_smul_right] at hn
  have hc0ne : c0 ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  have hc0ne' : c0' ≠ 0 := by
    intro h0; apply hn; rw [h0]; simp
  set s : ℂ := ⟪l a, ξ⟫_ℂ * ⟪ξ', l' b⟫_ℂ with hs
  have hs0 : s ≠ 0 := by
    intro h0; apply hn
    have : (starRingEnd ℂ) c0 * ⟪l a, ξ⟫_ℂ * (c0' * ⟪ξ', l' b⟫_ℂ) = (starRingEnd ℂ) c0 * c0' * s := by
      rw [hs]; ring
    rw [this, h0, mul_zero]

  set t : ℂ := ((‖A.v0‖ : ℝ) : ℂ) with ht
  have hv0ne : A.v0 ≠ 0 := hA.2.2.2.2.2.1
  have hv0 : A.v0 = t • w0 := by
    rw [hw0def, ht, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv0ne),
      Complex.ofReal_one, one_smul]
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := D.R.k) (r := D.R.rS) A.σ :=
    Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ hA.2.2.2.2.1
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ g = (c0 * t) • l (A.σ g w0) := by
    intro g hg'
    show A.B (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0 hc0 hl1.2.1 hw0s t hg'
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' g = (c0' * t) • l' (A.σ g w0) := by
    intro g hg'
    show A.B' (A.σ g A.v0) = _
    rw [hv0]
    exact orbit_mul hA.2.1 c0' hc0' hl1'.2.1 hw0s t hg'

  have ht0 : t ≠ 0 := by
    rw [ht]; exact_mod_cast (norm_ne_zero_iff.mpr hv0ne)
  have hcN : (A.cN : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hA.2.2.2.2.2.2.2.1)
  set K1 : ℂ := ((A.cN : ℂ)⁻¹) * (c0 * t) * (starRingEnd ℂ) (c0' * t) with hK1
  have hK10 : K1 ≠ 0 := by
    rw [hK1]
    refine mul_ne_zero (mul_ne_zero (inv_ne_zero hcN) (mul_ne_zero hc0ne ht0)) ?_
    exact (map_ne_zero _).mpr (mul_ne_zero hc0ne' ht0)
  have hw1 : ‖w0‖ = 1 := by
    rw [hw0def, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0ne)
  set dg : ℂ := (PI.BesselPeriodGGP.fdegH W.μG A.σ w0 : ℂ) with hdg
  have hdg0 : dg ≠ 0 := by
    rw [hdg]
    exact_mod_cast (ne_of_gt (Formalism.L2.S.Pv.AmpOrbCoef.fdegH_pos hA.1 hA.2.1 hG hw1))
  refine ⟨dg * s * K1⁻¹, mul_ne_zero (mul_ne_zero hdg0 hs0) (inv_ne_zero hK10), ?_⟩
  intro γ μR νR ν hCD
  obtain ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩ := hCD
  have hCD' : Formalism.MainNotions.S.Pv.AmpDD.CellData L W.μG γ μR νR ν := ⟨hγ, hGf, hMono, hRel, hRH, hOQ, hqR⟩
  obtain ⟨bb, hb0, hbm, hbi⟩ := hCC _ _ L h W.μG γ μR νR ν ENNReal.ofReal_ne_top hok hcell hCD' hMono
  have hAmp := hAKF hI _ _ L h W.μG w0 l l' hOP γ μR νR ν hCD' bb hb0 hbm hbi a b hka hkb ξ ξ'
  have hae := ae_UH_conj hγ hG hRH hqR
  have hJ1 : A.J νR γ = K1 • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ :=
    ampJ_mul νR A.cN A.Φ _ A.Φ' _ (c0 * t) (c0' * t) γ hγ hΦ hΦ' hae

  have hAmp' : s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ =
      dg⁻¹ • OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν := hAmp
  have e1 : OrbInt L (Formalism.MainNotions.S.Pv.AmpDD.coefF L a b ξ ξ') γ ν =
      dg • (s • ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ) := by
    rw [hAmp']; exact (smul_inv_smul₀ hdg0 _).symm
  have e2 : ampJ νR 1 (fun g => l (A.σ g w0)) (fun g => l' (A.σ g w0)) γ = K1⁻¹ • A.J νR γ := by
    rw [hJ1, smul_smul, inv_mul_cancel₀ hK10, one_smul]
  rw [e1, e2]
  simp only [smul_smul, mul_assoc]
  rfl

variable [Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow] [Fact Formalism.L2.SG.LitS.PfNVG.BesselNVG] in

/- English proof (translation)
Take `⟨hka, hkb, hn1, -⟩` from `hpin`. Establish `hn : ⟪(Formalism.L2.SG.LocWSOf.locS hB u u' τ).B a, ξ⟫_ℂ * ⟪ξ', (Formalism.L2.SG.LocWSOf.locS hB u u' τ).B' b⟫_ℂ ≠ 0` using `by show ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.sclOf hB u u' τ • Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ ≠ 0`. Rewrite using `[inner_smul_right]`. Establish `e : ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * (Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) = Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * (⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ)` using `by ring`. Rewrite using `[e, hn1, mul_one]`.

Conclude with `hscl`. Establish `hl : l1dist (lamD D τ) (lamD D τ) ≤ (0 : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3`. Simplify using `[l1dist]`. Conclude with `ampVec_gen (Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ) Formalism.FourierDecayAlt.P.admissible_atomic_form_one Formalism.L2.SG.AmpOrbClosed.amplitude_K_finite Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence (Formalism.MainN …`.
-/
theorem ampVec_carrier (hJ : PI.BesselMapUniq.BesselMapUniq) {D : D7} (large₂ : SizeData₂ D) {C' Cl Cg cb Cu cT CT C0 : ℝ}
    (hCl : 1000 ≤ Cl) (hH : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0)
    {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} {C : Formalism.L2.SG.LocWSOf.Choice X θ} (hB : Formalism.L2.SG.LocWSOf.WuBessel C)
    (u u' : D.what₂.Word) (τ : D.what₂.Tau) (hTT : HypTT D u u')
    (hW : GoodW D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ))
    (hA : GoodS D (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)) (hT : 0 < Tr D u) (hT' : 0 < Tr D u')
    (a b : X.B.H (Formalism.L2.SG.LocWSOf.vOf X τ)) (ξ : X.Vloc u (Formalism.L2.SG.LocWSOf.vOf X τ))
    (ξ' : X.Vloc u' (Formalism.L2.SG.LocWSOf.vOf X τ)) (c : ℂ) (hpin : CoefPin hB u u' τ a b ξ ξ' c)
    (hscl : Formalism.L2.SG.LocWSOf.sclOf hB u u' τ ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ)
        (Formalism.L2.SG.LocWSOf.locS hB u u' τ) hW hA hT hT') (Formalism.L2.SG.LocWSOf.locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (Formalism.L2.SG.LocWSOf.locW C u u' τ) (lamD D τ) (Formalism.L2.SG.LocWSOf.locS hB u u' τ)
          hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (Formalism.L2.SG.LocWSOf.sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν =
        κ • (Formalism.L2.SG.LocWSOf.locS hB u u' τ).J νR γ := by
  obtain ⟨hka, hkb, hn1, -⟩ := hpin
  have hn : ⟪(Formalism.L2.SG.LocWSOf.locS hB u u' τ).B a, ξ⟫_ℂ * ⟪ξ', (Formalism.L2.SG.LocWSOf.locS hB u u' τ).B' b⟫_ℂ ≠ 0 := by
    show ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
      ⟪ξ', Formalism.L2.SG.LocWSOf.sclOf hB u u' τ • Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ ≠ 0
    rw [inner_smul_right]
    have e : ⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ *
        (Formalism.L2.SG.LocWSOf.sclOf hB u u' τ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) =
        Formalism.L2.SG.LocWSOf.sclOf hB u u' τ *
          (⟪Formalism.L2.SG.LocWSOf.bOf hB u τ a, ξ⟫_ℂ * ⟪ξ', Formalism.L2.SG.LocWSOf.bOf hB u' τ b⟫_ℂ) := by ring
    rw [e, hn1, mul_one]
    exact hscl
  have hl : l1dist (lamD D τ) (lamD D τ) ≤ (0 : ℝ) * D.R.k * (D.R.m : ℝ) ^ 3 := by
    simp [l1dist]
  exact ampVec_gen (Formalism.MainNotions.BridgeCS3dClosed.inputs_of Formalism.L2.SG.BesselDiscreteSeries.decInf hJ) Formalism.FourierDecayAlt.P.admissible_atomic_form_one
    Formalism.L2.SG.AmpOrbClosed.amplitude_K_finite Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
    (Formalism.MainNotions.S.Pv.AmpDDPf.gap_of_hypotheses D large₂ C' Cl Cg cb Cu cT CT C0 0 hCl (by linarith))
    (Formalism.L2.S.Pv.NonVacuity.nvHyp0 D large₂ C' Cl Cg cb Cu cT CT C0 (by linarith)) hH τ u u' hTT θ _ hW (lamD D τ) hl _ hA
    hT hT' a b ξ ξ' hka hkb hn

end Formalism.L2.SG.Pf.CarrierT
