import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterDecompose
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTracePairingBilinearNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiFinRat

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical
open GlobalTheory.BoxLattice GlobalTheory.EvAdm

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FStandardCharacterDecompose.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.standard_character_decompose : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (x : κ → AF F) (z : κ → F), ψ (x ⬝ᵥ fun i => algebraMap F (AF F) (z i)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (GlobalTheory.VacLn.trPair F κ (fun i => evI F (x i)) (ratInf F κ z) : ℂ)) *
        ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ ratFin F κ z)) := by
  first | exact @GlobalTheory.PsiSplit.psi_split | exact GlobalTheory.PsiSplit.psi_split | (intros; apply GlobalTheory.PsiSplit.psi_split <;> assumption)
