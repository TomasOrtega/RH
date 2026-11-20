import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertPointEqOfOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHilbRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapEqKerIff
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits GlobalTheory.HilbertSch GlobalTheory.HilbGlue
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHilbertPointEqOfOpenCover.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.hilbert_point_eq_of_open_cover : ∀ {S Z : Scheme.{0}} (z : Z ⟶ S) (r : ℕ) (Y : Scheme.{0}) (𝒰 : Y.OpenCover) (x x' : GlobalTheory.HilbGlue.HPt z r Y), (∀ i, GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x = GlobalTheory.HilbGlue.HPt.map (𝒰.f i) x') → x = x' := by
  first | exact @GlobalTheory.HilbGlue.HPt.ext_openCover | exact GlobalTheory.HilbGlue.HPt.ext_openCover | (intros; apply GlobalTheory.HilbGlue.HPt.ext_openCover <;> assumption)
