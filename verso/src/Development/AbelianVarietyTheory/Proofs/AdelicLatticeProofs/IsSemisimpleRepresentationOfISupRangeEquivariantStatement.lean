import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSemisimpleRepresentationOfISupRangeEquivariant
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIsSemisimpleRepresentationOfISupRangeEquivariant.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isSemisimpleRepresentation_of_iSup_range_equivariant : ∀ (G : Type) [Group G] (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (J : Type) (V : J → Type) [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)] (r : ∀ j, Representation ℂ G (V j)) (p : ∀ j, V j →ₗ[ℂ] W), (∀ j, (r j).IsSemisimpleRepresentation) → (∀ j g v, p j (r j g v) = ρ g (p j v)) → (⨆ j, LinearMap.range (p j)) = ⊤ → ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | exact GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range | (intros; apply GlobalTheory.ClassFin.isSemisimpleRepresentation_of_iSup_range <;> assumption)
