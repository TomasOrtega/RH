import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAnnihilatorOpenSubgroupFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedWeilDatumCMPreservesSchwartzHeisenberStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCompactAnnihilatorOpenSubgroupFiniteAdeles.lean&line=107#L107)
-/
theorem _root_.GlobalTheory.T.isCompact_annihilator_openSubgroup_finiteAdeles : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {x : κ → FiniteAdeleRing (𝓞 F) F | ∀ y ∈ L, ψ (pairA F 0 (x ⬝ᵥ y)) = 1} := by
  first | exact @GlobalTheory.AnnCompactStd.isCompact_annihilator | exact GlobalTheory.AnnCompactStd.isCompact_annihilator | (intros; apply GlobalTheory.AnnCompactStd.isCompact_annihilator <;> assumption)
