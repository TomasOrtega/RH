import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationTprodOfIsIrreducibleAl
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIsSemisimpleRepresentationTprodOfIsIrreducibleAl.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_tprod_of_isIrreducible' : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ' : Representation ℂ G W) [FiniteDimensional ℂ V] [FiniteDimensional ℂ W], ρ.IsIrreducible → ρ'.IsIrreducible → (ρ.tprod ρ').IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_tprod_of_isIrreducible <;> assumption)
