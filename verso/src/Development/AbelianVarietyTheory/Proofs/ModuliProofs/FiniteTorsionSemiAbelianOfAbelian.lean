import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfIsReducedOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionFinite

/- English proof (translation)
Introduce `hB k _ _ G _ hG n hn`. Use `haveI := hG.comm`. Set `t : Sp k ⟶ Sp k` to `𝟙 _`. Establish `h` using `(semiAbelian_torsion_finite_and_closedPoint_finiteOrder hB).1 k ((Over.pullback t).obj G) (hG.fibres k t) n hn`. Establish `hp` using `isGrpPullback_pullback G t`.

Establish `hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k))))`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `e : x.left ≫ pullback.fst G.hom t = y.left ≫ pullback.fst G.hom t` using `congrArg (fun z => z.left) hxy`. Conclude with `Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))`.

Introduce `y`. Use `⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y)) (hp.1.lift_snd _ _ _), ?_⟩` and prove the remaining obligations. Conclude with `Over.OverMorphism.ext (hp.1.lift_fst _ _ _)`. Set `e` to `MulEquiv.ofBijective _ hbij`. Establish `h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ G // x ^ n = 1}`.

Use `Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)` and prove the remaining obligations. Use `show x ^ n = 1 ↔ e x ^ n = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`. Establish `h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t` using `Category.id_comp t`. Rewrite `h2` using `[h3]`.

Conclude with `h2`.
-/
theorem finite_torsion_semiAbelian_of_abelian :
    (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G → ∀ n : ℕ, 0 < n → Finite {x : 𝟙_ (Over (Sp k)) ⟶ G // x ^ n = 1} := by
  intro hB k _ _ G _ hG n hn
  haveI := hG.comm
  let t : Sp k ⟶ Sp k := 𝟙 _
  have h := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hB).1 k
    ((Over.pullback t).obj G) (hG.fibres k t) n hn
  have hp := isGrpPullback_pullback G t
  have hbij : Function.Bijective (pushHom hp (𝟙_ (Over (Sp k)))) := by
    constructor
    · intro x y hxy
      have e : x.left ≫ pullback.fst G.hom t = y.left ≫ pullback.fst G.hom t :=
        congrArg (fun z => z.left) hxy
      exact Over.OverMorphism.ext (hp.1.hom_ext e ((Over.w x).trans (Over.w y).symm))
    · intro y
      refine ⟨Over.homMk (hp.1.lift y.left (𝟙_ (Over (Sp k))).hom (Over.w y))
        (hp.1.lift_snd _ _ _), ?_⟩
      exact Over.OverMorphism.ext (hp.1.lift_fst _ _ _)
  let e := MulEquiv.ofBijective _ hbij
  have h2 : Finite {x : Over.mk ((𝟙_ (Over (Sp k))).hom ≫ t) ⟶ G // x ^ n = 1} := by
    refine Finite.of_equiv _ (e.toEquiv.subtypeEquiv (p := fun x => x ^ n = 1) fun x => ?_)
    show x ^ n = 1 ↔ e x ^ n = 1
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  have h3 : (𝟙_ (Over (Sp k))).hom ≫ t = t := Category.id_comp t
  rw [h3] at h2
  exact h2

end GlobalTheory.TorsionFinite
