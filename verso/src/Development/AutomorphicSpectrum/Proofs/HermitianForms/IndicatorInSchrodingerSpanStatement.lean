import Mathlib
import Development.AutomorphicSpectrum.Proofs.HermitianForms.IndicatorInSchrodingerSpan
import Formalism.UnipotentAdelicQuotients.SWXSDefs
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SDPadic.exists_selfDual` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FHermitianForms%2FIndicatorInSchrodingerSpan.lean&line=76#L76)
-/
theorem _root_.GlobalTheory.T.self_dual_lattice_filtration_character : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] (χ : V → V → ℂ) (L : ℤ → AddSubgroup V) (D : ℤ → AddSubgroup V), (∀ x x' y, χ (x + x') y = χ x y * χ x' y) → (∀ x y, χ x y = χ y x) → (∀ x y, ‖χ x y‖ = 1) → Continuous (fun p : V × V => χ p.1 p.2) → (∀ n, IsOpen (L n : Set V) ∧ IsCompact (L n : Set V) ∧ IsOpen (D n : Set V) ∧ IsCompact (D n : Set V)) → Antitone L → (∀ U ∈ nhds (0 : V), ∃ n, (L n : Set V) ⊆ U) → (∀ x, ∃ n, x ∈ L n) → (∀ x, ∃ n, x ∈ D n) → (∀ n y, y ∈ D n ↔ ∀ x ∈ L n, χ x y = 1) → (∀ n x, x ∈ L n ↔ ∀ y ∈ D n, χ x y = 1) → ∃ μ : Measure V, SelfDual μ χ := by
  first | exact @GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | exact GlobalTheory.CompanionTheory.SDPadic.exists_selfDual | (intros; apply GlobalTheory.CompanionTheory.SDPadic.exists_selfDual <;> assumption)
