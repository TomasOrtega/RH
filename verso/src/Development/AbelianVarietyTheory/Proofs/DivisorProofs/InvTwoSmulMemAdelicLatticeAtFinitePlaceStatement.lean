import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvTwoSmulMemAdelicLatticeAtFinitePlace
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertSph.invTwo_smul_mem_latAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInvTwoSmulMemAdelicLatticeAtFinitePlace.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.inv_two_smul_mem_adelicLatticeAtFinitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (W : Spc F E d)
    (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal → ∀ z ∈ GlobalTheory.InertSph.latAt W v, (⅟(2 : AF F)) • z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.InertSph.invTwo_smul_mem_latAt | exact GlobalTheory.InertSph.invTwo_smul_mem_latAt | (intros; apply GlobalTheory.InertSph.invTwo_smul_mem_latAt <;> assumption)
