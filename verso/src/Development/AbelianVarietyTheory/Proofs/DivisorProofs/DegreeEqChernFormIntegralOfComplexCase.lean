import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GenericOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AnalyticWeightLinearComb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyHomologyEquiv

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.ChernDegreeBaseChange

/- English proof (translation)
Establish `H` using `IsPullback.of_hasPullback Y.str (spMap ρ)`. Generalize the expression as in `Limits.pullback.fst Y.str (spMap ρ) = r at H`. Generalize the expression as in `Limits.pullback.snd Y.str (spMap ρ) = q at H`. Establish `hs : SmoothOfRelativeDimension Y.dim q`. Use `smoothOfRelativeDimension_isStableUnderBaseChange Y.dim` as an intermediate fact.

Use the proof step `MorphismProperty.of_isPullback H Y.smooth_str`. Establish `hg : GeometricallyIntegral q` using `MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str`. Establish `hc : GeometricallyConnected q` using `⟨fun _ _ y _ fst snd h =>`. Use `GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h` as an intermediate fact. Use the proof step `inferInstance⟩`.

Take `⟨Y', e, hd, he⟩` from `Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)`. Use `⟨Y', e.inv ≫ r, hd, ?_⟩` and prove the remaining obligations. Use `H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `using he.symm`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem exists_baseChange {F E : Type} [Field F] [Field E] (ρ : F →+* E) (Y : Var F) :
    ∃ (Y' : Var E) (r : Y'.X ⟶ Y.X), Y'.dim = Y.dim ∧ IsPullback r Y'.str Y.str (spMap ρ) := by
  have H := IsPullback.of_hasPullback Y.str (spMap ρ)
  generalize Limits.pullback.fst Y.str (spMap ρ) = r at H
  generalize Limits.pullback.snd Y.str (spMap ρ) = q at H
  have hs : SmoothOfRelativeDimension Y.dim q :=
    have := smoothOfRelativeDimension_isStableUnderBaseChange Y.dim
    MorphismProperty.of_isPullback H Y.smooth_str
  have hg : GeometricallyIntegral q :=
    MorphismProperty.of_isPullback (P := @GeometricallyIntegral) H Y.geometricallyIntegral_str
  have hc : GeometricallyConnected q :=
    ⟨fun _ _ y _ fst snd h =>
      have := GeometricallyIntegral.geometrically_isIntegral (f := q) y fst snd h
      inferInstance⟩
  obtain ⟨Y', e, hd, he⟩ := Var.exists_iso q Y.dim (ProjSpace.isProjOver_of_isPullback_spMap ρ H Y.isProjOver)
  refine ⟨Y', e.inv ≫ r, hd, ?_⟩
  refine H.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simpa using he.symm
  · simp
  · simp

/- English proof (translation)
Introduce `F _ Y σ Δ L r hr φ hφ`. Take `⟨Y', π, hd, H⟩` from `exists_baseChange σ Y`. Use `CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver` as an intermediate fact. Use `CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver` as an intermediate fact. Use `CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver` as an intermediate fact.

Use `CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver` as an intermediate fact. Take `⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧ Function.Bijective m` from `⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩`. Set `Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ` to `Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)`. Establish `hΦ : ∀ z, (Φ z).1 = z.1 ≫ π` using `hm`. Establish `hL'` using `LB.isLB_pull hr.isLB π`.

Take `⟨s, hs⟩` from `exists_isRatSec hL'`. Establish `hp` using `presents_divOfRatSec hL' hs`. Take `⟨h₁, h₂⟩` from `h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)`. Establish `hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ`. Use `letI := σ.toAlgebra`.

Rewrite using `[Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq), Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]`. Conclude with `FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB`. Establish `hsm : SmoothOfRelativeDimension Y.dim Y'.str` using `hd ▸ Y'.smooth_str`. Establish `e (ε)` using `ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε`. Rewrite `h₂` using `[hi]`.

Rewrite `h₁`, `h₂` using `[hd]`. Simplify using `only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e, integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢`. Conclude with `⟨h₁, h₂⟩`.
-/
theorem chernDegree_of_complex (h : GlobalTheory.Published.ChernDegreeComplex) : GlobalTheory.Published.ChernDegree := by
  intro F _ Y σ Δ L r hr φ hφ
  obtain ⟨Y', π, hd, H⟩ := exists_baseChange σ Y
  have := CxPts.compactSpace (RingHom.id ℂ) Y'.isProjOver
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver σ Y.isProjOver
  have := CxPts.secondCountableTopology_of_isProjOver (RingHom.id ℂ) Y'.isProjOver
  obtain ⟨m, hm, hb⟩ : ∃ m : CxPts Y'.str (RingHom.id ℂ) → CxPts Y.str σ, (∀ z, (m z).1 = z.1 ≫ π) ∧
      Function.Bijective m := ⟨bcMap H.w (RingHom.id ℂ), fun _ => rfl, bijective_bcMap H _⟩
  let Φ : CxPts Y'.str (RingHom.id ℂ) ≃ₜ CxPts Y.str σ :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective m hb) (continuous_of_comp hm)
  have hΦ : ∀ z, (Φ z).1 = z.1 ≫ π := hm
  have hL' := LB.isLB_pull hr.isLB π
  obtain ⟨s, hs⟩ := exists_isRatSec hL'
  have hp := presents_divOfRatSec hL' hs
  obtain ⟨h₁, h₂⟩ := h Y' _ _ s hp (ChernTransfer.pullW hΦ φ) (ChernTransfer.isCInf_pullW hΦ hφ)
  have hi : Y'.inter (fun _ => divOfRatSec hL' hs) = Y.inter fun _ => Δ := by
    letI := σ.toAlgebra
    rw [Var.inter_eq_of_toPic_eq (fun _ => hL') (fun _ => hp.toPic_eq),
      Var.inter_eq_of_toPic_eq (fun _ => hr.isLB) (fun _ => hr.toPic_eq), hd]
    exact FieldChangeInter.interNum_pull (f := Y.str) (f' := Y'.str) H (L := fun _ => L) fun _ => hr.isLB
  have hsm : SmoothOfRelativeDimension Y.dim Y'.str := hd ▸ Y'.smooth_str
  have e (ε) := ChernTransfer.chernPart_pullW hΦ (AnRead.all _ _ Y.dim) (AnRead.all _ _ Y.dim) hφ ε
  rw [hi] at h₂
  rw [hd] at h₁ h₂
  simp only [Weight.ChernIntegrableOn, Weight.chernInt, integrableOn_univ, Measure.restrict_univ, e,
    integral_map_equiv, integrable_map_equiv] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

end GlobalTheory.ChernDegreeBaseChange
