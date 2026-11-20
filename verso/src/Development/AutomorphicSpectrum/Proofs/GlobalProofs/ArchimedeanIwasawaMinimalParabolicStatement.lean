import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FArchimedeanIwasawaMinimalParabolic.lean&line=250#L250)
-/
theorem _root_.GlobalTheory.T.levi_normalizes_unipotent_variant : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)), ∀ g ∈ levi D.sp.cm.sig V.gram X Y T, ∀ n ∈ unip D.sp.cm.sig V.gram X T, g * n * g⁻¹ ∈ unip D.sp.cm.sig V.gram X T := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi <;> assumption)
