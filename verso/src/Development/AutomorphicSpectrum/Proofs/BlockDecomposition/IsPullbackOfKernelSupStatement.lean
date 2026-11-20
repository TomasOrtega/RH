import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullbackOfKernelSup
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIsPullbackOfKernelSup.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.is_pullback_of_kernel_sup : ∀ {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A) (g : Z ⟶ B)
    [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)], f ≫ a = g ≫ b →
    Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b → IsPullback f g a b := by
  first | exact @GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | exact GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup | (intros; apply GlobalTheory.CompanionTheory.GE.PbKer.isPullback_of_ker_eq_sup <;> assumption)
