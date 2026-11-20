import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCdvrMkLeContinuum
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCdvrMkLeContinuum.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_complete_dvr_local_extension_of_countable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R], Countable R → ∃ (T : CDVR) (i : R →+* T.V), Function.Injective i ∧ IsLocalHom i ∧ Cardinal.mk T.V ≤ Cardinal.continuum := by
  first | exact @GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum | exact GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum | (intros; apply GlobalTheory.CountableCompletion.exists_cdvr_mk_le_continuum <;> assumption)
