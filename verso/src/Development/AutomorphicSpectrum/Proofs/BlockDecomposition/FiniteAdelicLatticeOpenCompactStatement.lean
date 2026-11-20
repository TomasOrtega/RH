import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicLatticeOpenCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LastRowMulRowGLInv
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiniteAdelicLatticeOpenCompact.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.finite_adelic_lattice_open_compact : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (S : Finset (Pl E)) (B : ∀ w : Pl E, AddSubgroup (w.adicCompletion E)), (∀ w ∈ S, IsOpen (B w : Set (w.adicCompletion E))) → (∀ w ∈ S, (B w : Set (w.adicCompletion E)) ⊆ (Formalism.UG.Ov E w : Set (w.adicCompletion E))) → IsOpen (latS S B : Set (Af E)) ∧ IsCompact (latS S B : Set (Af E)) := by
  first | exact @GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | exact GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.CutOff.latS_isOpen_isCompact <;> assumption)
