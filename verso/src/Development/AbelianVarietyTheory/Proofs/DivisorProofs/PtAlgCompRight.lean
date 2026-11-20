import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.SumMulFacts

/- English proof (translation)
Use `conv_lhs => rw [← spOver_ptAlg y, spOver_comp]`. Conclude with `ptAlg_spOver _`.
-/
theorem ptAlg_comp_right {R D D' E : Type} [CommRing R] [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D']
    [CommRing E] [Algebra R E] (φ : D →ₐ[R] D') (y : Pt (SpAlg R D') E) :
    ptAlg (y ≫ spOver φ) = (ptAlg y).comp φ := by
  conv_lhs => rw [← spOver_ptAlg y, spOver_comp]
  exact ptAlg_spOver _

/- English proof (translation)
Introduce `R D _ _ _ B J _ d b`. Use `⟨fun hb ↦ ?_, fun D' _ _ φ ↦ ?_⟩` and prove the remaining obligations. Introduce `E _ _ E' _ _ E'' _ _ φ ψ z _`. Establish `hα : ptAlg (spOver φ ≫ z ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _))` using `ptAlg_comp _ _`. Simplify using `only [sumMul, hα, map_sum, map_mul, AlgHom.comp_apply, Category.assoc]`.

Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Establish `h` using `hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Use function extensionality and compare the values at `E _ _ E' _ _ ψ y`. Simplify using `only [Fn1.pull, sumMul, Category.assoc, whiskerRight_fst, whiskerRight_snd]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ptAlg_comp_right]`. Both sides reduce to the same expression.
-/
theorem main : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D] (B : Over (Sp R)) (J : Type) [Fintype J] (d : J → D) (b : J → Fn1 B), ((∀ i, IsCoc (whole B) (b i)) → IsCoc (whole _) (sumMul d b)) ∧ ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D'), (sumMul d b).pull (spOver φ ▷ B) = sumMul (fun i ↦ φ (d i)) b := by
  intro R D _ _ _ B J _ d b
  refine ⟨fun hb ↦ ?_, fun D' _ _ φ ↦ ?_⟩
  · intro E _ _ E' _ _ E'' _ _ φ ψ z _
    have hα : ptAlg (spOver φ ≫ z ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _)) := ptAlg_comp _ _
    simp only [sumMul, hα, map_sum, map_mul, AlgHom.comp_apply, Category.assoc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have h := hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
    rw [h]
    ring
  · funext E _ _ E' _ _ ψ y
    simp only [Fn1.pull, sumMul, Category.assoc, whiskerRight_fst, whiskerRight_snd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Category.assoc, ptAlg_comp_right]
    rfl

end GlobalTheory.PtExt.SumMulFacts
