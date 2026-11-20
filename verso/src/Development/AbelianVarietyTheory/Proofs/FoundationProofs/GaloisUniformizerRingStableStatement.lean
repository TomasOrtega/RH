import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisUniformizerRingStable
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisUniformizerRingStable.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.galois_uniformizer_ring_stable : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (σ : Ainf l →+* Ainf l), (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.wittFixedFrobeniusPow K, σ w = w) → (∃ u ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ (GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s) = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * u) → ∀ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s ∧ ∃ b ∈ GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.ringAs AI K s, σ a - a = GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified.piS AI s * b := by
  first | exact @GlobalTheory.RingAsStable.ringAs_stable | exact GlobalTheory.RingAsStable.ringAs_stable | (intros; apply GlobalTheory.RingAsStable.ringAs_stable <;> assumption)
