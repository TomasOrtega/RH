import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOfClassOfFixedUnitsEq
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNormOfClassOfFixedUnitsEq.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.exists_norm_of_classOfFixedUnits_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq | exact GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq | (intros; apply GlobalTheory.UnitLemma.InvAlg.ClRel.eq_of_mk_eq <;> assumption)
