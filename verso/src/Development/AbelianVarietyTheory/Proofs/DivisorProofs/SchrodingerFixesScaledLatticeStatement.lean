import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerFixesScaledLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneHermitianIdealCoprime

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerFixesScaledLattice.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.schrodinger_fixes_scaled_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Ψ ∈ schA F κ, ∀ (m : ℕ) (y z : Fin m → κ → Af F), ∃ N : ℕ, N ≠ 0 ∧ ∀ j,
      schr ψ (fun i => pairA F 0 ((N : Af F) * y j i), fun i => pairA F 0 ((N : Af F) * z j i)) Ψ = Ψ := by
  first | exact @GlobalTheory.SmallHeisFix.main | exact GlobalTheory.SmallHeisFix.main | (intros; apply GlobalTheory.SmallHeisFix.main <;> assumption)
