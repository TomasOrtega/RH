import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevAtZ
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FractionalIdealCompletionLocallyPrincipalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D v 𝔞 h𝔞`. Take `⟨x, hx0, hx⟩` from `GlobalTheory.T.fractionalIdealCompletion_locally_principal D v 𝔞 h𝔞`. Take `⟨ε, hεε, -, hεint, hεid, -⟩` from `(GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1`. Establish `hεI : ε ∈ idAt D (· = v)` using `hεint.1`. Establish `hxx : incA D x⁻¹ * incA D x = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hx0, map_one]`. Use `⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx]`. Use `⟨?_, Ideal.mul_mem_left _ _ hεI⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc, hxx, one_mul]`.

Conclude with `hεint`. Introduce `s hs`. Establish `: incA D x⁻¹ * ε * (incA D x * ε) = ε * ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this, hεε]`.

Conclude with `(hεid s).1 hs`. Introduce `s`. Rewrite using `[hx]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨h2, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_assoc, (hεid s).1 h2]`. Conclude with `h1`. Introduce and unpack `⟨h2, h1⟩`. Use `⟨?_, h2⟩` and prove the remaining obligations.

Rewrite `h1` using `[mul_assoc, (hεid s).1 h2]`. Conclude with `h1`.
-/
theorem GlobalTheory.FinPl.idV_principal_at : ∀ (D : D7) (v : Pl D) (𝔞 : FI D), 𝔞 ≠ 0 → ∃ g ∈ idV 𝔞 v, ∃ g' ∈ idAt D (· = v), (∀ s ∈ idAt D (· = v), g' * g * s = s) ∧ ∀ s, s ∈ idV 𝔞 v ↔ s ∈ idAt D (· = v) ∧ g' * s ∈ intAt D (· = v) := by
  intro D v 𝔞 h𝔞
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.fractionalIdealCompletion_locally_principal D v 𝔞 h𝔞
  obtain ⟨ε, hεε, -, hεint, hεid, -⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hεI : ε ∈ idAt D (· = v) := hεint.1
  have hxx : incA D x⁻¹ * incA D x = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
  refine ⟨incA D x * ε, ?_, incA D x⁻¹ * ε, Ideal.mul_mem_left _ _ hεI, ?_, ?_⟩
  · rw [hx]
    refine ⟨?_, Ideal.mul_mem_left _ _ hεI⟩
    rw [← mul_assoc, hxx, one_mul]; exact hεint
  · intro s hs
    have : incA D x⁻¹ * ε * (incA D x * ε) = ε * ε := by
      calc incA D x⁻¹ * ε * (incA D x * ε) = (incA D x⁻¹ * incA D x) * (ε * ε) := by ring
        _ = ε * ε := by rw [hxx, one_mul]
    rw [this, hεε]; exact (hεid s).1 hs
  · intro s
    rw [hx]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [mul_assoc, (hεid s).1 h2]; exact h1
    · rintro ⟨h2, h1⟩
      refine ⟨?_, h2⟩
      rw [mul_assoc, (hεid s).1 h2] at h1; exact h1
