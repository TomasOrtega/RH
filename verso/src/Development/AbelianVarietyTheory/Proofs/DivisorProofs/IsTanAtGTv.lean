import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusExtExponentialDerivativeBijectiveTangent
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChartKSBracket

/- English proof (translation)
Introduce `E _ _ _ H R _ _ _ _ _ t P Y u`. Use `letI := H.starRing`. Establish `: Module.Finite R (DualNumber R)` using `inferInstanceAs (Module.Finite R (R × R))`. Use `GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)` as an intermediate fact. Establish `: Nontrivial (DualNumber R)` using `(TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial`.

Establish `: IsLocalRing (DualNumber R)` using `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by`. Rewrite using `[TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]`. Simplify using `using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst`. Establish `hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R))` using `Category.comp_id _`. Take `⟨x, hx, -⟩` from `GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))`.

Take `⟨x₀, -, hu₀⟩` from `GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)`. Establish `h1` using `hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))`. Establish `e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u`. Rewrite `h1` using `[e]`. Establish `h2` using `GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))`.

Establish `hk : smT (𝟙 (Sp R)) 0 x = 1` using `(hu₀ _ h1).trans (hu₀ _ h2).symm`. Conclude with `⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩`.
-/
theorem tanPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (u : TanM (𝟙 (Sp R)) Y.H), ∃ v' : TanM (𝟙 (Sp R)) t.G, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv u)) (tv v') := by
  intro E _ _ _ H R _ _ _ _ _ t P Y u
  letI := H.starRing
  have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
  have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hs : spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) = spMap (algebraMap R (DualNumber R)) := Category.comp_id _
  obtain ⟨x, hx, -⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ (tv u))
  obtain ⟨x₀, -, hu₀⟩ := GlobalTheory.FormalPoint.existsUnique_isPointOf' P.U.toUnifPre hs (Y.Φ _ 1)
  have h1 := hx.pull (homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R)))) (Y.rep.1 _ _ _ (tv u))
  have e : homAt (𝟙 (Sp R)) (tm ((0 : R) • (LinearMap.id : R →ₗ[R] R))) ≫ tv u = 1 := ReciprocityTheory.ChartRestriction.G.PullbackSections.tv_mem u
  rw [e] at h1
  have h2 := GlobalTheory.FormalPoint.isPointOf_one P.U.toUnifPre (GlobalTheory.ExpTan.isZero_one Y.rep (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R))))
  have hk : smT (𝟙 (Sp R)) 0 x = 1 := (hu₀ _ h1).trans (hu₀ _ h2).symm
  exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.mkT x hk, hx⟩

/- English proof (translation)
Introduce `E _ _ _ H R _ t v'`. Use `GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')` and prove the remaining obligations. Rewrite using `[Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]`. Both sides reduce to the same expression.
-/
theorem isTanAtG_tv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (t : SAB H (Sp R)) (v' : TanM (𝟙 (Sp R)) t.G), IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) (spMap (dualMap (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) ≫ (tv v').left) := by
  intro E _ _ _ H R _ t v'
  refine GlobalTheory.LieMet.isTan_map _ ?_ (GlobalTheory.LieMet.isTan_tv v')
  rw [Category.comp_id, chart, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  rfl

end GlobalTheory.ChartKSBracket
