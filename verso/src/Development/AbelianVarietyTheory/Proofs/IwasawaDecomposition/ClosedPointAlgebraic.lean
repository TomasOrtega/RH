import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.ClosedAlg

/- English proof (translation)
Introduce `F _ _ Y M x hx`. Set `ι : F →ₐ[ℚ] AlgebraicClosure ℚ` to `IsAlgClosed.lift`. Use `letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra`. Take `⟨⟨⟨y, hy⟩, hyx⟩⟩` from `(ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) Y.str x hx).1`. Establish `h : (y ≫ M.j) ≫ M.p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F))`.

Rewrite using `[Category.assoc, M.pb.w, ← Category.assoc, hy]`. Conclude with `(Spec.map_comp _ _).symm`. Establish `h2` using `GlobalTheory.Mean4O.GeomPt.isAlgPt M.ar (⟨y ≫ M.j, h⟩ : GlobalTheory.Mean4O.GeomPt M.p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))`. Substitute `hyx` using the available equality. Conclude with `h2`.
-/
theorem isAlgPt_of_isClosed : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (x : Y.X), IsClosed ({x} : Set Y.X) → ArInt.IsAlgPt (M.j x) := by
  intro F _ _ Y M x hx
  let ι : F →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  letI : Algebra F (AlgebraicClosure ℚ) := ι.toRingHom.toAlgebra
  obtain ⟨⟨⟨y, hy⟩, hyx⟩⟩ := (ExtConj.closed_point_geometric_fibres_finite (K := AlgebraicClosure ℚ) Y.str x hx).1
  have h : (y ≫ M.j) ≫ M.p = spMap ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)) := by
    rw [Category.assoc, M.pb.w, ← Category.assoc, hy]
    exact (Spec.map_comp _ _).symm
  have h2 := GlobalTheory.Mean4O.GeomPt.isAlgPt M.ar
    (⟨y ≫ M.j, h⟩ : GlobalTheory.Mean4O.GeomPt M.p ((algebraMap F (AlgebraicClosure ℚ)).comp (algebraMap (𝓞 F) F)))
  subst hyx
  exact h2

end GlobalTheory.TrueGeo.ClosedAlg
