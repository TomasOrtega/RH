import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianExtensionAbelianLocusNonempty
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSemiAbelianExtensionAbelianLocusNonempty.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.semiAbelianExtension_abelianLocus_nonempty : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (abLocus Zh.G).Nonempty := by
  first | exact @GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty | exact GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty | (intros; apply GlobalTheory.ZHAbLocusNonempty.abLocus_nonempty <;> assumption)
