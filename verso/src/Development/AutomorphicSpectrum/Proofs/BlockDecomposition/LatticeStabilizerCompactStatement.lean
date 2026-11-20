import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeStabilizerCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLatticeStabilizerCompact.lean&line=219#L219)
-/
theorem _root_.GlobalTheory.T.lattice_stabilizer_compact : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}, IsCMExt F E σ → IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsLat (intLoc F E v) Λ → IsCompact (stabLat σ J Λ : Set (GLoc σ J v)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | exact GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat | (intros; apply GlobalTheory.CompanionTheory.KFin.CompactStab.isCompact_stabLat <;> assumption)
