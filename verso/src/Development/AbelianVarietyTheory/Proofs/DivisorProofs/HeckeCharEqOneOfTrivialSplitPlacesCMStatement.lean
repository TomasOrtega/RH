import Mathlib
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOneOfTrivialSplitPlacesCM
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

/- English proof (citation)
Apply `GlobalTheory.HeckeSplitGen.heckeChar_eq_one_of_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeCharEqOneOfTrivialSplitPlacesCM.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.heckeChar_eq_one_of_trivial_splitPlaces_CM : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ ν : (AF F ⊗[F] E)ˣ →* Circle, IsHeckeCharF ν →
      (∀ e, IsSplitIdemF σ e → ∀ x : (AF F ⊗[F] E)ˣ, (e + cAF σ e) * ((x : AF F ⊗[F] E) - 1) = (x : AF F ⊗[F] E) - 1 → ν x = 1) →
      ∀ x, ν x = 1 := by
  first | exact @GlobalTheory.HeckeSplitGen.heckeChar_eq_one_of_split | exact GlobalTheory.HeckeSplitGen.heckeChar_eq_one_of_split | (intros; apply GlobalTheory.HeckeSplitGen.heckeChar_eq_one_of_split <;> assumption)
