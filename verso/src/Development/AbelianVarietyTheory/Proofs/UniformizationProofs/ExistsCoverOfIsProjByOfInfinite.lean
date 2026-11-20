import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RingKrullDimLeOfQuasiFinite

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineCover

/- English proof (translation)
Take `⟨H, hH, m, s, hc, hs⟩` from `hp`. Establish `: Smooth f` using `SmoothOfRelativeDimension.smooth g f`. Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian f`. Establish `: CompactSpace X` using `⟨by`. Establish `e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X)`.

Rewrite using `[← TopologicalSpace.Opens.coe_iSup, hc]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `isCompact_iUnion fun i => (hs i).1.isCompact⟩`. Establish `: IsNoetherian X` using `⟨⟩`.

Take `⟨D, hD, h⟩` from `exists_affine_le_coheight (X := X) (fun F hF => exists_isAffineOpen_of_finite (cst f ⊤) hH s hc (fun i => (hs i).1) F hF) (g + 1)`. Use `⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩` and prove the remaining obligations. Use `(h x hx).trans (coheight_le_of_smooth f hf x)` as an intermediate fact. Conclude with `Nat.not_succ_le_self _ (by exact_mod_cast this)`.
-/
theorem exists_cover_of_isProjBy_of_infinite (K : Type) [Field K] [Infinite K] (X : Scheme.{0})
    (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ) (hf : SmoothOfRelativeDimension g f) (hp : IsProjBy f) :
    ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  obtain ⟨H, hH, m, s, hc, hs⟩ := hp
  have : Smooth f := SmoothOfRelativeDimension.smooth g f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := ⟨by
    have e : (Set.univ : Set X) = ⋃ i, (nonzeroLocus (s i) : Set X) := by
      rw [← TopologicalSpace.Opens.coe_iSup, hc]
      rfl
    rw [e]
    exact isCompact_iUnion fun i => (hs i).1.isCompact⟩
  have : IsNoetherian X := ⟨⟩
  obtain ⟨D, hD, h⟩ := exists_affine_le_coheight (X := X) (fun F hF =>
    exists_isAffineOpen_of_finite (cst f ⊤) hH s hc (fun i => (hs i).1) F hF) (g + 1)
  refine ⟨D, hD, top_le_iff.1 fun x _ => not_not.1 fun hx => ?_⟩
  have := (h x hx).trans (coheight_le_of_smooth f hf x)
  exact Nat.not_succ_le_self _ (by exact_mod_cast this)

/- English proof (translation)
Introduce `K _ _ X _ f g hf hp` and use `exists_cover_of_isProjBy_of_infinite K X f g hf hp`.
-/
theorem exists_cover_of_isProjBy :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K)) (g : ℕ), SmoothOfRelativeDimension g f → IsProjBy f → ∃ D : Fin (g + 1) → X.Opens, (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ :=
  fun K _ _ X _ f g hf hp => exists_cover_of_isProjBy_of_infinite K X f g hf hp

end GlobalTheory.AffineCover
