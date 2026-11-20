import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ`. Establish `sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x)`. Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => simp`.

Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]`. Establish `sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z)`. Introduce `z`. Proceed by induction on `z with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]`. Establish `ex : Function.Exact (d.lTensor R') (p.lTensor R')` using `lTensor_exact R' hdp hp`. Establish `ps : Function.Surjective (p.lTensor R')` using `LinearMap.lTensor_surjective R' hp`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨z, rfl⟩` from `ps y`. Rewrite `hy` using `[sqZ]`.

Take `⟨x', hx'⟩` from `(hdp' (liftSemi fZ z)).1 hy`. Take `⟨x, rfl⟩` from `hN x'`. Establish `: d.lTensor R' x = z` using `hZ.1 (by rw [sqN, hx'])`. Rewrite using `[← this]`. Conclude with `(ex _).2 ⟨x, rfl⟩`.

Introduce `q'`. Take `⟨z', rfl⟩` from `hp' q'`. Take `⟨z, rfl⟩` from `hZ.2 z'`. Conclude with `⟨p.lTensor R' z, sqZ z⟩`.
-/
theorem liftSemi_bijective_of_exact_cokernel : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (N : Type) [AddCommGroup N] [Module R N] (Z : Type) [AddCommGroup Z] [Module R Z] (Q : Type) [AddCommGroup Q] [Module R Q] (N' : Type) [AddCommGroup N'] [Module R' N'] (Z' : Type) [AddCommGroup Z'] [Module R' Z'] (Q' : Type) [AddCommGroup Q'] [Module R' Q'] (d : N →ₗ[R] Z) (p : Z →ₗ[R] Q) (d' : N' →ₗ[R'] Z') (p' : Z' →ₗ[R'] Q') (fN : N →ₛₗ[algebraMap R R'] N') (fZ : Z →ₛₗ[algebraMap R R'] Z') (fQ : Q →ₛₗ[algebraMap R R'] Q'), Function.Exact d p → Function.Surjective p → Function.Exact d' p' → Function.Surjective p' → (∀ x, d' (fN x) = fZ (d x)) → (∀ z, p' (fZ z) = fQ (p z)) → Function.Surjective (liftSemi fN) → Function.Bijective (liftSemi fZ) → Function.Bijective (liftSemi fQ) := by
  intro R R' _ _ _ N _ _ Z _ _ Q _ _ N' _ _ Z' _ _ Q' _ _ d p d' p' fN fZ fQ hdp hp hdp' hp' sN sZ hN hZ
  have sqN : ∀ x, liftSemi fZ (d.lTensor R' x) = d' (liftSemi fN x) := by
    intro x
    induction x with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sN]
  have sqZ : ∀ z, liftSemi fQ (p.lTensor R' z) = p' (liftSemi fZ z) := by
    intro z
    induction z with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul r n => rw [LinearMap.lTensor_tmul, liftSemi_tmul, liftSemi_tmul, map_smul, sZ]
  have ex : Function.Exact (d.lTensor R') (p.lTensor R') := lTensor_exact R' hdp hp
  have ps : Function.Surjective (p.lTensor R') := LinearMap.lTensor_surjective R' hp
  refine ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨z, rfl⟩ := ps y
    rw [sqZ] at hy
    obtain ⟨x', hx'⟩ := (hdp' (liftSemi fZ z)).1 hy
    obtain ⟨x, rfl⟩ := hN x'
    have : d.lTensor R' x = z := hZ.1 (by rw [sqN, hx'])
    rw [← this]
    exact (ex _).2 ⟨x, rfl⟩
  · intro q'
    obtain ⟨z', rfl⟩ := hp' q'
    obtain ⟨z, rfl⟩ := hZ.2 z'
    exact ⟨p.lTensor R' z, sqZ z⟩

end GlobalTheory
