import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

/- English proof (translation)
Introduce `Ω Vs _ _ _ p P v`. Establish `hA : (exteriorPower.ιMulti Ω p).compLinearMap (Fintype.linearCombination Ω v) = (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω).smulRight (exteriorPower.ιMulti Ω p v)`. Use `(Pi.basisFun Ω (Fin p)).ext_alternating fun u hu => ?_` and prove the remaining obligations. Set `s : Equiv.Perm (Fin p)` to `Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)`. Establish `e : (fun i => Pi.basisFun Ω (Fin p) (u i)) = (fun i => Pi.basisFun Ω (Fin p) i) ∘ s` using `rfl`.

Rewrite using `[e, AlternatingMap.map_perm, AlternatingMap.map_perm]`. Use `congr 1`. Establish `e1 : (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω) (fun i => Pi.basisFun Ω (Fin p) i) = 1`. Express the relevant statement in the definitionally equal form `Matrix.det (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1`. Rewrite using `[show (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1 from by`.

Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]`. Rewrite using `[AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Conclude with `AlternatingMap.congr_fun hA P`.
-/
theorem ιMulti_matrix_transform : ∀ (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs] (p : ℕ) (P : Matrix (Fin p) (Fin p) Ω) (v : Fin p → Vs),
    exteriorPower.ιMulti Ω p (fun i => ∑ k, P i k • v k) = P.det • exteriorPower.ιMulti Ω p v := by
  intro Ω Vs _ _ _ p P v
  have hA : (exteriorPower.ιMulti Ω p).compLinearMap (Fintype.linearCombination Ω v) =
      (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω).smulRight
        (exteriorPower.ιMulti Ω p v) := by
    refine (Pi.basisFun Ω (Fin p)).ext_alternating fun u hu => ?_
    let s : Equiv.Perm (Fin p) := Equiv.ofBijective u (Finite.injective_iff_bijective.1 hu)
    have e : (fun i => Pi.basisFun Ω (Fin p) (u i)) = (fun i => Pi.basisFun Ω (Fin p) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin p → Ω) [⋀^Fin p]→ₗ[Ω] Ω)
        (fun i => Pi.basisFun Ω (Fin p) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun Ω (Fin p) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun hA P

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
