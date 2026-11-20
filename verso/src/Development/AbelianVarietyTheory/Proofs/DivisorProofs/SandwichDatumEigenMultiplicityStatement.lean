import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicity
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSandwichDatumEigenMultiplicity.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.sandwich_datum_eigen_multiplicity : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), (iSupIndep (fun σ : Λ →+* O => eig C (actT D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actT D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actT D) τ) = N) ∧ (iSupIndep (fun σ : Λ →+* O => eig C (actH D) σ) ∧ (⨆ σ : Λ →+* O, eig C (actH D) σ) = ⊤ ∧ ∀ τ : Λ →+* O, Module.finrank C (eig C (actH D) τ) = N) := by
  first | exact @GlobalTheory.eig_decomp_T_H | exact GlobalTheory.eig_decomp_T_H | (intros; apply GlobalTheory.eig_decomp_T_H <;> assumption)
