import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.RestrictedCuspConstantTermVanish
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGlobalProofs%2FRestrictedCuspConstantTermVanish.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.cusp_function_of_constant_terms_vanish : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | exact GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame.isCuspFun_of_isConstAlong <;> assumption)
