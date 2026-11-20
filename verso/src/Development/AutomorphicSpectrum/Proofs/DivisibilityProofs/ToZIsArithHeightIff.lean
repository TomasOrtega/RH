import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ArFormExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegersStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumLogNormEqSumEmbeddingsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WOverRestrPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

/- English proof (translation)
Establish `hv : IsArithVar (i ≫ p) 0` using `hX.of_isClosedImmersion i hc (by simpa using hd)`. Establish `e` using `GlobalTheory.T.sum_logNorm_eq_sum_embeddings k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) hv (L.restr i) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ)) (wOver_restr_pow k X Z p t i L hL _).1 r hr`. Unfold `HermLB.curveDeg`. Use `congrArg (_ - ·) ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (RingHom.ext_int _ _) h]`.

Conclude with `e`.
-/
theorem curveDeg_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] [IsLocallyNoetherian Z] (hc : CharZero Γ(Z, ⊤)) (hd : topologicalKrullDim Z = 1)
    (r : (L.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (L.restr i).B r) :
    HermLB.curveDeg ((toZ L t hL).restr i) (r := r) hr = HermLB.curveDeg (L.restr i) hr := by
  have hv : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc (by simpa using hd)
  have e := GlobalTheory.T.sum_logNorm_eq_sum_embeddings k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) hv (L.restr i)
    (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    (wOver_restr_pow k X Z p t i L hL _).1 r hr
  unfold HermLB.curveDeg
  refine congrArg (_ - ·) ?_
  rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (RingHom.ext_int _ _) h]
  exact e

/- English proof (translation)
Establish `hv : IsArithVar (i ≫ p) e` using `hX.of_isClosedImmersion i hc hd`. Establish `hw` using `wOver_restr_pow k X Z p t i L hL (Int.castRingHom ℂ)`. Take `⟨e₁, e₂⟩` from `GlobalTheory.T.archIntegrable_iff_over_integers k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) e hv (L.restr i) ((L.restr i).pow m) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ)) ((((toZ L t hL).restr i).pow m).φ (Int.castRingHom ℂ)) hw.1 (hw.2 m) (((toZ L t hL).restr i).cInf _) e r hr`. Establish `hτ (τ : ℤ →+* ℂ) : τ = Int.castRingHom ℂ` using `RingHom.ext_int _ _`. Use `⟨⟨fun H => e₁.1 (H _), fun H τ => ?_⟩, fun H => ?_⟩` and prove the remaining obligations.

Rewrite using `[hτ τ]`. Conclude with `e₁.2 H`. Unfold `HermLB.archInt`. Rewrite using `[finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (hτ τ) h]`. Conclude with `e₂ H`.
-/
theorem arch_toZ {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (t : X ⟶ Sp ℤ) {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (i : Z ⟶ X) [IsClosedImmersion i]
    [IsIntegral Z] (hc : CharZero Γ(Z, ⊤)) (e : ℕ) (hd : topologicalKrullDim Z = (e + 1 : ℕ)) (m : ℕ)
    (r : ((L.restr i).pow m).B.ι → Z.functionFieldˣ) (hr : IsRatSec ((L.restr i).pow m).B r) :
    (HermLB.ArchIntegrable ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr ↔
      HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr) ∧
    (HermLB.ArchIntegrable (L.restr i) ((L.restr i).pow m) e hr →
      HermLB.archInt ((toZ L t hL).restr i) ((toZ L t hL).restr i |>.pow m) (r := r) e hr =
        HermLB.archInt (L.restr i) ((L.restr i).pow m) e hr) := by
  have hv : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc hd
  have hw := wOver_restr_pow k X Z p t i L hL (Int.castRingHom ℂ)
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.archIntegrable_iff_over_integers k Z (i ≫ p) (i ≫ t) (Int.castRingHom ℂ) e hv (L.restr i)
    ((L.restr i).pow m) (((toZ L t hL).restr i).φ (Int.castRingHom ℂ))
    ((((toZ L t hL).restr i).pow m).φ (Int.castRingHom ℂ)) hw.1 (hw.2 m)
    (((toZ L t hL).restr i).cInf _) e r hr
  have hτ (τ : ℤ →+* ℂ) : τ = Int.castRingHom ℂ := RingHom.ext_int _ _
  refine ⟨⟨fun H => e₁.1 (H _), fun H τ => ?_⟩, fun H => ?_⟩
  · rw [hτ τ]
    exact e₁.2 H
  · unfold HermLB.archInt
    rw [finsum_eq_single _ (Int.castRingHom ℂ) fun τ h => absurd (hτ τ) h]
    exact e₂ H

/- English proof (translation)
Introduce `k _ X p t D hX L hL h`. Use `⟨fun H => ⟨H.vertical, ?_, ?_⟩, fun H => ⟨H.vertical, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `Z i _ _ _ hc hd r hr`. Conclude with `(H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr)`. Introduce `Z i _ _ _ hc e he hd m r hr`.

Take `⟨e₁, e₂⟩` from `arch_toZ t hX L hL i hc e hd m r hr`. Take `⟨h₁, h₂⟩` from `H.recursion Z i hc e he hd m r hr`. Establish `h₃` using `e₁.1 h₁`. Conclude with `⟨h₃, h₂.trans (congrArg (_ - ·) (e₂ h₃))⟩`. Introduce `Z i _ _ _ hc hd r hr`.

Conclude with `(H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr).symm`. Introduce `Z i _ _ _ hc e he hd m r hr`. Take `⟨e₁, e₂⟩` from `arch_toZ t hX L hL i hc e hd m r hr`. Take `⟨h₁, h₂⟩` from `H.recursion Z i hc e he hd m r hr`. Conclude with `⟨e₁.2 h₁, h₂.trans (congrArg (_ - ·) (e₂ h₁).symm)⟩`.
-/
theorem isArithHeight_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (hL : ∀ τ, (wZ L t τ).IsCInf) (h : X → ℝ), (toZ L t hL).IsArithHeight h ↔ L.IsArithHeight h := by
  intro k _ X p t D hX L hL h
  refine ⟨fun H => ⟨H.vertical, ?_, ?_⟩, fun H => ⟨H.vertical, ?_, ?_⟩⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr)
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    have h₃ := e₁.1 h₁
    exact ⟨h₃, h₂.trans (congrArg (_ - ·) (e₂ h₃))⟩
  · intro Z i _ _ _ hc hd r hr
    exact (H.point Z i hc hd r hr).trans (curveDeg_toZ t hX L hL i hc hd r hr).symm
  · intro Z i _ _ _ hc e he hd m r hr
    obtain ⟨e₁, e₂⟩ := arch_toZ t hX L hL i hc e hd m r hr
    obtain ⟨h₁, h₂⟩ := H.recursion Z i hc e he hd m r hr
    exact ⟨e₁.2 h₁, h₂.trans (congrArg (_ - ·) (e₂ h₁).symm)⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
