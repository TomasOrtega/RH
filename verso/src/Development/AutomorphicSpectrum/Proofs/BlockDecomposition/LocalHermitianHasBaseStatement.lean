import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianHasBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.KFin.Base.hasBase_place` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLocalHermitianHasBase.lean&line=178#L178)
-/
theorem _root_.GlobalTheory.T.local_hermitian_has_base : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), HasBase (sigR (Fv F v) σ) (intLoc F E v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Base.hasBase_place | exact GlobalTheory.CompanionTheory.KFin.Base.hasBase_place | (intros; apply GlobalTheory.CompanionTheory.KFin.Base.hasBase_place <;> assumption)
