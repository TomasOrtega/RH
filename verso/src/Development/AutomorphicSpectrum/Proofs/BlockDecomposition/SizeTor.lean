import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleCoordinatesBoundedRise
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFacts

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.Desc
open GroundTheory.Automorphic.Reduction (adelicBorel maxCompact posIdele diagUnits)
open scoped ENNReal
attribute [local instance] borelH

namespace GlobalTheory.CompanionTheory.PiVec

/- English proof (translation)
Introduce `E _ _ _ n ω hω`. Take `⟨hcpt, -, -, c, hc⟩` from `GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n`. Take `⟨r₁, h₁⟩` from `hcpt ω hω`. Take `⟨r₂, h₂⟩` from `hcpt _ (GroundTheory.Automorphic.Reduction.isCompact_maxCompact (K := E) (n := n))`. Establish `htor` using `GlobalTheory.CompanionTheory.TorNorm.torNorm GlobalTheory.CompanionTheory.LogAbs.logAbsBasic E`.

Use `⟨|r₁| + |r₂| + 2 * |c|, by positivity, fun b hb x k hk => ?_⟩` and prove the remaining obligations. Establish `e₁` using `hc (b * An.tor E x) k`. Establish `e₂` using `hc b (An.tor E x)`. Establish `e₃` using `((htor.2 n x).2)`. Establish `a₁` using `(h₁ b hb).trans (le_abs_self r₁)`.

Establish `a₂` using `(h₂ k hk).trans (le_abs_self r₂)`. Establish `a₃` using `le_abs_self c`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sizeTor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (ω : Set (GA E n)), IsCompact ω → ∃ A : ℝ, 0 ≤ A ∧
    ∀ b ∈ ω, ∀ x : Fin n → ℝ, ∀ k ∈ maxCompact (K := E) (n := n),
      logSize (b * An.tor E x * k) ≤ A + 2 * Module.finrank ℚ E * ‖x‖ := by
  intro E _ _ _ n ω hω
  obtain ⟨hcpt, -, -, c, hc⟩ :=
    GlobalTheory.CompanionTheory.Size.sizeBasic GlobalTheory.CompanionTheory.Dblock.SzFinProof.szFin GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces E n
  obtain ⟨r₁, h₁⟩ := hcpt ω hω
  obtain ⟨r₂, h₂⟩ := hcpt _ (GroundTheory.Automorphic.Reduction.isCompact_maxCompact (K := E) (n := n))
  have htor := GlobalTheory.CompanionTheory.TorNorm.torNorm GlobalTheory.CompanionTheory.LogAbs.logAbsBasic E
  refine ⟨|r₁| + |r₂| + 2 * |c|, by positivity, fun b hb x k hk => ?_⟩
  have e₁ := hc (b * An.tor E x) k
  have e₂ := hc b (An.tor E x)
  have e₃ := ((htor.2 n x).2)
  have a₁ := (h₁ b hb).trans (le_abs_self r₁)
  have a₂ := (h₂ k hk).trans (le_abs_self r₂)
  have a₃ := le_abs_self c
  linarith

end GlobalTheory.CompanionTheory.PiVec

end
