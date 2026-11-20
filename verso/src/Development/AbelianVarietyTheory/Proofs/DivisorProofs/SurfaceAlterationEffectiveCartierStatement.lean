import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurfaceAlterationEffectiveCartier
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (toMod)
open GlobalTheory.VB
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps
open GlobalTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSurfaceAlterationEffectiveCartier.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.surface_alteration_effective_cartier : ∀ (k : Type) [Field k] (T : Scheme.{0}) [Algebra k Γ(T, ⊤)] [IsIntegral T], IsProjSurface k T → ∀ J : T.IdealSheafData, genericPoint T ∉ J.support → ∃ (T' : Scheme.{0}) (_ : Algebra k Γ(T', ⊤)) (_ : IsIntegral T') (ρ : T' ⟶ T), IsProjSurface k T' ∧ ρ ≫ strHom k T = strHom k T' ∧ IsGenFinite ρ 1 ∧ ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap ρ) := by
  first | exact @GlobalTheory.BlowSurf.exists_isProjSurface_effCartier | exact GlobalTheory.BlowSurf.exists_isProjSurface_effCartier | (intros; apply GlobalTheory.BlowSurf.exists_isProjSurface_effCartier <;> assumption)
