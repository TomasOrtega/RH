import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Formalism.LocalToGlobal.ProjectiveLattices.UnifLeaves
import Formalism.LocalToGlobal.ProjectiveLattices.ReadLeaves
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsInfEmb
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
open NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AdTh
variable {D : D7} {r g : ℕ}

/- English proof (translation)
Establish `hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ`. Introduce `τ`. Use `⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩` and prove the remaining obligations. Establish `h1` using `(X.cmType τ).1 h`. Take `⟨ρ, hρ⟩` from `(GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))`.

Conclude with `⟨ρ, hρ.symm⟩`. Choose the witnesses or unpack the hypotheses as in `⟨ρ⟩ : Nonempty D.what₂.Tau := by`. Assume the negation of the conclusion as `hne`. Establish `h` using `GlobalTheory.StdRat.tauE_cm D D.host.φ₀`. Take `⟨ρ, -⟩` from `h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)`.

Conclude with `hne ⟨ρ⟩`. Use `⟨hm, hpsi, ?_⟩` and prove the remaining obligations. Establish `h1` using `X.κ0_sign ⟨tauE D ρ, hp ρ⟩`. Establish `h2` using `xi_zero_im_pos D ρ`. Break down `X.κ0_xi with h | h` into its components or cases.

Rewrite using `[h, hm.2]`. Expand and normalize the polynomial expressions, which then agree. It suffices to derive a contradiction. Rewrite `h1` using `[h, hm.2]`. Simplify using `[map_ofNat] at h1`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isMod_of (W : HSp D) (hr : W.rank = r) (X : Data D.host.E r) (hm : Formalism.L2.Pj.ModelW W hr X)
    (hp : ∀ ρ, tauE D ρ ∈ X.Ψ) : IsMod W hr X := by
  have hpsi : ∀ τ : D.host.E →+* ℂ, τ ∈ X.Ψ ↔ ∃ ρ, τ = tauE D ρ := by
    intro τ
    refine ⟨fun h => ?_, fun ⟨ρ, h⟩ => h ▸ hp ρ⟩
    have h1 := (X.cmType τ).1 h
    obtain ⟨ρ, hρ⟩ := (GlobalTheory.StdRat.tauE_cm D τ).2 (fun ⟨ρ, hρ⟩ => h1 (hρ ▸ hp ρ))
    exact ⟨ρ, hρ.symm⟩
  obtain ⟨ρ⟩ : Nonempty D.what₂.Tau := by
    by_contra hne
    have h := GlobalTheory.StdRat.tauE_cm D D.host.φ₀
    obtain ⟨ρ, -⟩ := h.2 (fun ⟨ρ, _⟩ => hne ⟨ρ⟩)
    exact hne ⟨ρ⟩
  refine ⟨hm, hpsi, ?_⟩
  have h1 := X.κ0_sign ⟨tauE D ρ, hp ρ⟩
  have h2 := xi_zero_im_pos D ρ
  rcases X.κ0_xi with h | h
  · rw [h, hm.2]; ring
  · exfalso
    rw [h, hm.2] at h1
    simp [map_ofNat] at h1
    linarith

end GlobalTheory.AdTh
