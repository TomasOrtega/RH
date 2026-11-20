import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.SiegelWeilFreeOfBlockNonemptyFrames
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FRepresentationTheoryGL%2FSiegelWeil%2FArchimedeanSiegelWeil%2FPlaceIntegrals%2FSiegelWeilFreeOfBlockNonemptyFrames.lean&line=531#L531)
-/
theorem _root_.GlobalTheory.T.siegelWeil_free_of_block_nonempty_frames : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n t : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), IsBlockM t T → 2 * n < M → (framesE σ J T).Nonempty → SWFree σ J T hT := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.swFree_block | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.swFree_block
