import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantDoubleCosetSectionMemEquivariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPtHomApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TraceBlocks
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEquivariantDoubleCosetSectionMemEquivariant.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.equivariantDoubleCosetSection_mem_equivariant : ∀ (G H V : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ι : H →* G) (ρ : Representation ℂ H V) (K' : Subgroup G) (x : G) (v : V), secM ι ρ K' x v ∈ eqvM ι ρ K' := by
  first | exact @GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM | exact GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM | (intros; apply GlobalTheory.BCT.TraceBlocks.secM_mem_eqvM <;> assumption)
