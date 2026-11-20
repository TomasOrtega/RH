import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzContinuousHasDerivAtArchimedeanLin
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordAppend
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMixedSymm
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix ENNReal
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAdelicSchwartzContinuousHasDerivAtArchimedeanLin.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.adelicSchwartz_continuous_hasDerivAt_archimedeanLine : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ schA F κ, Continuous g ∧ ∀ (v : κ → mixedEmbedding.mixedSpace F) (x : κ → AF F) (t : ℝ), HasDerivAt (fun s : ℝ => g (x + fun i => infAd F (s • v i))) (dD F v g (x + fun i => infAd F (t • v i))) t := by
  first | exact @GlobalTheory.ArchDecay.SchLine.schline | exact GlobalTheory.ArchDecay.SchLine.schline | (intros; apply GlobalTheory.ArchDecay.SchLine.schline <;> assumption)
