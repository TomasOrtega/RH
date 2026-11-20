import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitSectionDivisorEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorActionFormEqSimilitudeMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Establish `hc : ∀ y : S, algebraMap A S t * y = y * algebraMap A S t` using `fun y => Algebra.commutes t y`. Establish `h1 : xs = bi * ((↑x⁻¹ : S) * algebraMap A S t)`. Rewrite using `[← hx, ← _root_.mul_assoc (↑x⁻¹ : S), ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul, _root_.one_mul, ← _root_.mul_assoc, hb, _root_.one_mul]`. Rewrite using `[h1, _root_.mul_assoc, _root_.mul_assoc, hc, ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul, _root_.one_mul]`. Conclude with `(hc bi).symm`.
-/
private theorem mul_unit_eq_algebraMap_mul {S A : Type*} [Ring S] [CommRing A] [Algebra A S] (xs : S) (x : Sˣ) (b bi : S)
    (t : A) (hb : bi * b = 1) (hx : (x : S) * b * xs = algebraMap A S t) :
    xs * (x : S) = algebraMap A S t * bi := by
  have hc : ∀ y : S, algebraMap A S t * y = y * algebraMap A S t := fun y => Algebra.commutes t y
  have h1 : xs = bi * ((↑x⁻¹ : S) * algebraMap A S t) := by
    rw [← hx, ← _root_.mul_assoc (↑x⁻¹ : S), ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
      _root_.one_mul, ← _root_.mul_assoc, hb, _root_.one_mul]
  rw [h1, _root_.mul_assoc, _root_.mul_assoc, hc, ← _root_.mul_assoc (↑x⁻¹ : S), Units.inv_mul,
    _root_.one_mul]
  exact (hc bi).symm

/- English proof (translation)
Introduce `p _ D G L B h₁`. Take `⟨t, ht⟩` from `B.trivAf.choose_spec`. Establish `hx : (↑(trivX B) : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ↑B.β * MulOpposite.unop ((starT G.star (AfP p)) ↑(trivX B)) = algebraMap (AfP p) _ ↑t` using `ht`. Establish `key` using `mul_unit_eq_algebraMap_mul (A := AfP p) _ (trivX B) _ (inC G (AfP p) ↑B.β⁻¹) _ (by rw [← map_mul, Units.inv_mul, map_one]) hx`. Establish `hsh : sh G (↑B.β⁻¹ : G.C) = ↑B.β⁻¹`.

Establish `h : sh G (↑B.β⁻¹ : G.C) * ↑B.β = 1`. Rewrite using `[← B.sym]`. Simplify using `only [sh]`. Rewrite using `[← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]`. Conclude with `Units.mul_eq_one_iff_eq_inv.mp h`.

Use `⟨(h₁⁻¹).1.2 * t, fun u w => ?_⟩` and prove the remaining obligations. Unfold `rd`. Rewrite using `[actG_form_eq_sim, adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, key, map_mul, AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]`. Simplify using `only [inC, AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]`. Rewrite using `[actOn_tmul_tmul', TensorProduct.smul_tmul', LinearMap.BilinForm.baseChange_tmul, formB, L.adj, hsh, Units.val_mul]`.

Simplify using `only [smul_eq_mul]`. Rewrite using `[Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.W2.rdForm_of :
    UpperTheory.Gal.W2.RdForm := by
  intro p _ D G L B h₁
  obtain ⟨t, ht⟩ := B.trivAf.choose_spec
  have hx : (↑(trivX B) : AfP p ⊗[ℚ] G.C) * inC G (AfP p) ↑B.β *
      MulOpposite.unop ((starT G.star (AfP p)) ↑(trivX B)) = algebraMap (AfP p) _ ↑t := ht
  have key := mul_unit_eq_algebraMap_mul (A := AfP p) _ (trivX B) _ (inC G (AfP p) ↑B.β⁻¹) _
    (by rw [← map_mul, Units.inv_mul, map_one]) hx
  have hsh : sh G (↑B.β⁻¹ : G.C) = ↑B.β⁻¹ := by
    have h : sh G (↑B.β⁻¹ : G.C) * ↑B.β = 1 := by
      rw [← B.sym]
      simp only [sh]
      rw [← MulOpposite.unop_mul, ← map_mul, Units.mul_inv, map_one, MulOpposite.unop_one]
    exact Units.mul_eq_one_iff_eq_inv.mp h
  refine ⟨(h₁⁻¹).1.2 * t, fun u w => ?_⟩
  unfold rd
  rw [actG_form_eq_sim, adj_actOn_afP, ← Module.End.mul_apply, ← map_mul, key, map_mul,
    AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [inC, AlgHom.coe_toRingHom, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply]
  rw [actOn_tmul_tmul', TensorProduct.smul_tmul', LinearMap.BilinForm.baseChange_tmul, formB,
    L.adj, hsh, Units.val_mul]
  simp only [smul_eq_mul]
  rw [Algebra.smul_def]
  ring
