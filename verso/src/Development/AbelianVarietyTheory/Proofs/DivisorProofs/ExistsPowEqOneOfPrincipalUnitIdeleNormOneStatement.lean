import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
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

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPowEqOneOfPrincipalUnitIdeleNormOne.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  first | exact @GlobalTheory.UnitTorsion.principal_unit_idele_torsion | exact GlobalTheory.UnitTorsion.principal_unit_idele_torsion | (intros; apply GlobalTheory.UnitTorsion.principal_unit_idele_torsion <;> assumption)
