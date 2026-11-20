import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantLatticePrincipal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDeterminantLatticePrincipal.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.determinant_lattice_principal : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h N : ℕ), v.Integers O → ∀ (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → Module.finrank C (eig C ρ τ) = N → Module.finrank C (detLine C ρ τ N) = 1 ∧ ∃ w : detLine C ρ τ N, w ≠ 0 ∧ detLattice C ρ τ N = Submodule.span O {w} := by
  first | exact @GlobalTheory.detLattice_eq_span_singleton | exact GlobalTheory.detLattice_eq_span_singleton | (intros; apply GlobalTheory.detLattice_eq_span_singleton <;> assumption)
