import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderRetractRestrictionStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AbelianSchemeTorsionAugmentationStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TorsionPointsHopfOrderStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp hc N _ M hM K`. Take `⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, hst, rfl⟩` from `hM`. Use `haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj`. Use `haveI : IsCommMonObj A := hA.comm`. Use `haveI : Finite N' := GlobalTheory.T.torsion_points_finite R p A T N' pt hpt`.

Use `letI : Fintype N' := Fintype.ofFinite N'`. Establish `hi : Function.Injective i` using `Function.LeftInverse.injective (g := π) hiπ`. Use `haveI : Finite N := Finite.of_injective i hi`. Use `letI : Fintype N := Fintype.ofFinite N`. Take `⟨⟨AA, hAA⟩, -⟩` from `GlobalTheory.T.torsion_points_hopf_order p C v R hv hp A T N' pt hpt`.

Establish `hgen` using `GlobalTheory.T.abelian_scheme_torsion_augmentation hQ hZ hH p C v R hv hp hc A L hA hL hamp T N' pt hpt (K.map i)`. Establish `hret` using `GlobalTheory.T.hopf_order_retract_restriction p C v R hv hp N' AA N i π hiπ (by rw [hAA]; exact hst)`. Rewrite using `[← hAA]`. Conclude with `hret.2.2 K (by rw [hAA]; exact hgen)`.
-/
theorem subquotientStatement_of_quotient_zarhin_hodgeTate
    (hQ : QuotientByFiniteFlatStatement) (hZ : ZarhinStatement) (hH : HodgeTateDatumStatement) :
    SubquotientStatement := by
  intro p _ C _ _ _ v R _ _ hv hp hc N _ M hM K
  obtain ⟨A, _, L, hA, hL, hamp, T, N', _, pt, hpt, i, π, hiπ, hst, rfl⟩ := hM
  classical
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : IsCommMonObj A := hA.comm
  haveI : Finite N' := GlobalTheory.T.torsion_points_finite R p A T N' pt hpt
  letI : Fintype N' := Fintype.ofFinite N'
  have hi : Function.Injective i := Function.LeftInverse.injective (g := π) hiπ
  haveI : Finite N := Finite.of_injective i hi
  letI : Fintype N := Fintype.ofFinite N
  obtain ⟨⟨AA, hAA⟩, -⟩ := GlobalTheory.T.torsion_points_hopf_order p C v R hv hp A T N' pt hpt
  have hgen := GlobalTheory.T.abelian_scheme_torsion_augmentation hQ hZ hH p C v R hv hp hc A L hA hL hamp T N' pt hpt (K.map i)
  have hret := GlobalTheory.T.hopf_order_retract_restriction p C v R hv hp N' AA N i π hiπ (by rw [hAA]; exact hst)
  rw [← hAA]
  exact hret.2.2 K (by rw [hAA]; exact hgen)

/- English proof (translation)
The claim follows from `subquotientStatement_of_quotient_zarhin_hodgeTate`.
-/
example : QuotientByFiniteFlatStatement → ZarhinStatement → HodgeTateDatumStatement →
    SubquotientStatement := subquotientStatement_of_quotient_zarhin_hodgeTate

end GlobalTheory.CompanionTheory.Ar.GR
