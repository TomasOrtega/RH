import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterTrivialUnitIdeles
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuadraticCharacterTrivialUnitIdeles.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.quadratic_character_trivial_unit_ideles : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ b : Neutral.B1.Ideles (maximalRealSubfield E),
    b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (GlobalTheory.GalOfCusp.quadChar E).1 (GlobalTheory.Mem.Chr.finPartI _ b) = 1 := by
  first | exact @GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one | exact GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one | (intros; apply GlobalTheory.EtaFinUnit.quadChar_finPartI_eq_one <;> assumption)
