import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InfPowConjDiagUnits
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open scoped Classical

/- English proof (translation)
Introduce `E _ _ ψ m ho hk`. Take `⟨f, hf, hfe⟩` from `exists_infPow_hom E m`. Set `p : Neutral.B1.Ideles E →* (Af E)ˣ` to `Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)`. Establish `hpc : Continuous p` using `Continuous.units_map _ continuous_snd`. Establish `hψ : Continuous ψ` using `continuous_of_isOpen_ker' ψ ho`.

Establish `hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k` using `fun k => Units.ext rfl`. Establish `hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y` using `fun w y => Units.ext rfl`. Establish `hi : ∀ k : Eˣ, p (infDiag k) = 1` using `fun k => by`. Rewrite using `[infDiag_eq]`. Conclude with `Units.ext rfl`.

Set `θ : Neutral.B1.Ideles E →* ℂˣ` to `ψ.comp p * f`. Establish `hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x` using `fun x => by`. Rewrite using `[← hfe]`. Both sides reduce to the same expression. Use `⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩` and prove the remaining obligations.

Rewrite using `[hθ, hd, hk, infPow_diagUnits, Units.val_one]`. Conclude with `inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))`. Use `show ((θ (infDiag k) : ℂˣ) : ℂ) = _`. Rewrite using `[hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]`. Use `show θ (Neutral.B1.localIdele E w y) = _`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hθ, hl, infPow_localIdele, mul_one]`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.pFinToHecke_of :
    UpperTheory.Gal.CertificateRingHomMap.FinToHecke := by
  intro E _ _ ψ m ho hk
  obtain ⟨f, hf, hfe⟩ := exists_infPow_hom E m
  let p : Neutral.B1.Ideles E →* (Af E)ˣ :=
    Units.map (MonoidHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E) : _ →* _)
  have hpc : Continuous p := Continuous.units_map _ continuous_snd
  have hψ : Continuous ψ := continuous_of_isOpen_ker' ψ ho
  have hd : ∀ k : Eˣ, p (Neutral.B1.diagUnits E k) = diagF E k := fun k => Units.ext rfl
  have hl : ∀ (w : Plc E) y, p (Neutral.B1.localIdele E w y) = sgl w y := fun w y => Units.ext rfl
  have hi : ∀ k : Eˣ, p (infDiag k) = 1 := fun k => by
    rw [infDiag_eq]
    exact Units.ext rfl
  let θ : Neutral.B1.Ideles E →* ℂˣ := ψ.comp p * f
  have hθ : ∀ x, ((θ x : ℂˣ) : ℂ) = ((ψ (p x) : ℂˣ) : ℂ) * infPow m x := fun x => by
    rw [← hfe]
    rfl
  refine ⟨⟨θ, (hψ.comp hpc).mul hf, fun k => Units.ext ?_⟩, fun k _ => ?_, fun w y => ?_⟩
  · rw [hθ, hd, hk, infPow_diagUnits, Units.val_one]
    exact inv_mul_cancel₀ (Finset.prod_ne_zero_iff.mpr fun φ _ => zpow_ne_zero _ (by simp))
  · show ((θ (infDiag k) : ℂˣ) : ℂ) = _
    rw [hθ, hi, infPow_infDiag, infPow_diagUnits, map_one, Units.val_one, one_mul]
  · show θ (Neutral.B1.localIdele E w y) = _
    refine Units.ext ?_
    rw [hθ, hl, infPow_localIdele, mul_one]
