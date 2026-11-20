import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpen
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HBBump.exists_bump` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsInducedSectionSupportedOpen.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_induced_section_supported_open : ∀ {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (B : Subgroup G), IsOpen (B : Set G) → IsCompact (B : Set G) → ∀ z : Z, (∀ h : H, (h : G) ∈ B → ρ h z = z) → ∃ b : cIndSpace H ρ, (∀ (h : H) (β : G), β ∈ B → b.1.1.1 ((h : G) * β) = ρ h z) ∧ ∀ p : G, (¬ ∃ h : H, ∃ β ∈ B, p = (h : G) * β) → b.1.1.1 p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.HBBump.exists_bump | exact GlobalTheory.CompanionTheory.HBBump.exists_bump | (intros; apply GlobalTheory.CompanionTheory.HBBump.exists_bump <;> assumption)
