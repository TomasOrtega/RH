import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechDR

/- English proof (translation)
Introduce `R R' _ _ _ X X' s s' φ H p hp f hf`. Establish `hUY : p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 ⊓ s' ⁻¹ᵁ ⊤` using `by rw [hp]; simp`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := p.1.2.1) (UY := p.1.1.1) le_top le_top hUY).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) p.1.2.2)`. Establish `po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec s p.1.2.1))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom (secPull s s' p)) (CommRingCat.ofHom (algebraMap R' (Sec s' p.1.1.1)))`. Use `po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `(Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R)).hom_inv_id_assoc _).symm`. Rewrite using `[← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Conclude with `(Category.comp_id _).trans (Category.id_comp _).symm`. Conclude with `(Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R')).hom_inv_id_assoc _).symm`.

Use `letI : Algebra (Sec s p.1.2.1) (Sec s' p.1.1.1) := (secPull s s' p).toAlgebra`. Use `letI : Algebra R (Sec s' p.1.1.1) := ((algebraMap R' (Sec s' p.1.1.1)).comp (algebraMap R R')).toAlgebra`. Use `haveI : IsScalarTower R R' (Sec s' p.1.1.1) := .of_algebraMap_eq fun _ => rfl`. Use `haveI : IsScalarTower R (Sec s p.1.2.1) (Sec s' p.1.1.1) := .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) po'.w).symm`. Establish `h : Algebra.IsPushout R R' (Sec s p.1.2.1) (Sec s' p.1.1.1)` using `(CommRingCat.isPushout_iff_isPushout.mp po').symm`.

Establish `e : ⇑(liftSemi f) = ⇑h.out.equiv`. Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero]`. Consider the case `tmul c v => rw [liftSemi_tmul, h.out.equiv_tmul, hf]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Rewrite using `[e]`. Conclude with `h.out.equiv.bijective`.
-/
theorem bijective_liftSemi_secPull : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ p : Pair φ, p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 → ∀ f : Sec s p.1.2.1 →ₛₗ[algebraMap R R'] Sec s' p.1.1.1, (∀ b, f b = secPull s s' p b) → Function.Bijective (liftSemi f) := by
  intro R R' _ _ _ X X' s s' φ H p hp f hf
  have hUY : p.1.1.1 = φ ⁻¹ᵁ p.1.2.1 ⊓ s' ⁻¹ᵁ ⊤ := by rw [hp]; simp
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := p.1.2.1) (UY := p.1.1.1) le_top le_top hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) p.1.2.2)
  have po' : IsPushout (CommRingCat.ofHom (algebraMap R (Sec s p.1.2.1))) (CommRingCat.ofHom (algebraMap R R'))
      (CommRingCat.ofHom (secPull s s' p)) (CommRingCat.ofHom (algebraMap R' (Sec s' p.1.1.1))) := by
    refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R)).hom_inv_id_assoc _).symm
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans ((Scheme.ΓSpecIso (.of R')).hom_inv_id_assoc _).symm
  letI : Algebra (Sec s p.1.2.1) (Sec s' p.1.1.1) := (secPull s s' p).toAlgebra
  letI : Algebra R (Sec s' p.1.1.1) := ((algebraMap R' (Sec s' p.1.1.1)).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' (Sec s' p.1.1.1) := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    .of_algebraMap_eq fun r => (congrArg (fun q => q.hom r) po'.w).symm
  have h : Algebra.IsPushout R R' (Sec s p.1.2.1) (Sec s' p.1.1.1) :=
    (CommRingCat.isPushout_iff_isPushout.mp po').symm
  have e : ⇑(liftSemi f) = ⇑h.out.equiv := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c v => rw [liftSemi_tmul, h.out.equiv_tmul, hf]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e]
  exact h.out.equiv.bijective

end GlobalTheory.CechDR
