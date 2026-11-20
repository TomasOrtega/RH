import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeUnifVal

open Formalism.L2.Host

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localIdele_eq_locM {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (x : (v.adicCompletion E)ˣ) :
    localIdele E v x = Units.map (Formalism.L2.NC.locM v) x := by
  rfl

/- English proof (translation)
Introduce `E _ _ χ h hχ v`. Establish `hloc : ∀ x : (v.adicCompletion E)ˣ, χ.loc v x = h.χ (Units.map (Formalism.L2.NC.locM v) x)`. Introduce `x`. Rewrite using `[hχ, ← localIdele_eq_locM]`. Both sides reduce to the same expression.

Establish `hiff : χ.UnrAt v ↔ h.Unr v`. Prove the components needed by the constructor for the conclusion. Introduce `hu u hu1`. Rewrite using `[← hloc]`. Conclude with `hu u hu1`.

Introduce `hu u hu1`. Rewrite using `[hloc]`. Conclude with `hu u hu1`. Use `⟨fun hu => ⟨hiff.1 hu, fun ϖ hϖ => ?_⟩, hiff⟩` and prove the remaining obligations. Establish `hs` using `unif_spec v`.

Unfold `IsUnifAt at hs`. Establish `hq : IsUnitAt v (ϖ * (atFin v (unif v))⁻¹)`. Unfold `IsUnitAt`. Rewrite using `[Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hs, hϖ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]`. Establish `h1` using `hu _ hq`.

Rewrite `h1` using `[map_mul, map_inv, mul_inv_eq_one]`. Rewrite using `[← hloc, h1]`. Both sides reduce to the same expression.
-/
theorem at_val_and_unr_iff : ∀ {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : Formalism.L2.NC.HC E), h.χ = (χ : Ideles E →* ℂˣ) → ∀ (v : HeightOneSpectrum (𝓞 E)), (χ.UnrAt v → h.At v (χ.val v)) ∧ (χ.UnrAt v ↔ h.Unr v) := by
  intro E _ _ χ h hχ v
  have hloc : ∀ x : (v.adicCompletion E)ˣ, χ.loc v x = h.χ (Units.map (Formalism.L2.NC.locM v) x) := by
    intro x
    rw [hχ, ← localIdele_eq_locM]
    rfl
  have hiff : χ.UnrAt v ↔ h.Unr v := by
    constructor
    · intro hu u hu1
      rw [← hloc]
      exact hu u hu1
    · intro hu u hu1
      rw [hloc]
      exact hu u hu1
  refine ⟨fun hu => ⟨hiff.1 hu, fun ϖ hϖ => ?_⟩, hiff⟩
  have hs := unif_spec v
  unfold IsUnifAt at hs
  have hq : IsUnitAt v (ϖ * (atFin v (unif v))⁻¹) := by
    unfold IsUnitAt
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hs, hϖ, mul_inv_cancel₀ (WithZero.exp_ne_zero)]
  have h1 := hu _ hq
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  rw [← hloc, h1]
  rfl

end GlobalTheory.HeckeUnifVal
