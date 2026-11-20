import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzArchimedeanSliceAdelicSchwartz
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ArchSlice.exists_schwartz_slice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsSchwartzArchimedeanSliceAdelicSchwartz.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_schwartz_archimedeanSlice_adelicSchwartz : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ, ∃ g : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
    g t = Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F)) := by
  first | exact @GlobalTheory.ArchSlice.exists_schwartz_slice | exact GlobalTheory.ArchSlice.exists_schwartz_slice | (intros; apply GlobalTheory.ArchSlice.exists_schwartz_slice <;> assumption)
