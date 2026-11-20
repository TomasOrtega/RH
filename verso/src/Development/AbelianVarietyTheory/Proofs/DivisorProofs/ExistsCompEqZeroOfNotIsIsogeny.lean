import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.FrobFieldExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneFunctorBaseFunctorPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneIntegralityAndFaithfulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraFiniteFinrankLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndIsogenyAlgebraInjectiveClearDenom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.Dieu.AbsDet

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hr : Function.Injective (LinearMap.mulRight ℚ x)`. Introduce `a b hab`. Assume the negation of the conclusion as `hne`.

Use `h (a - b) (sub_ne_zero.mpr hne) ?_` and prove the remaining obligations. Rewrite using `[sub_mul]`. Conclude with `sub_eq_zero.mpr hab`. Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.mp hr) 1`. Establish `hyx : y * x = 1` using `hy`.

Establish `hl : Function.Injective (LinearMap.mulLeft ℚ x)`. Introduce `a b hab`. Establish `hab' : x * a = x * b` using `hab`. Establish `e : y * (x * a) = y * (x * b)` using `by rw [hab']`. Rewrite `e` using `[← mul_assoc, ← mul_assoc, hyx, one_mul, one_mul]`. Then use the resulting hypothesis.

Take `⟨z, hz⟩` from `(LinearMap.injective_iff_surjective.mp hl) 1`. Establish `hxz : x * z = 1` using `hz`. Establish `hyz : y = z`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hx ⟨⟨x, y, hyz ▸ hxz, hyx⟩, rfl⟩`.
-/
theorem exists_mul_eq_zero_of_not_isUnit {R : Type} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R] (x : R)
    (hx : ¬ IsUnit x) : ∃ y : R, y ≠ 0 ∧ y * x = 0 := by
  by_contra h
  push_neg at h
  have hr : Function.Injective (LinearMap.mulRight ℚ x) := by
    intro a b hab
    by_contra hne
    refine h (a - b) (sub_ne_zero.mpr hne) ?_
    rw [sub_mul]
    exact sub_eq_zero.mpr hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hr) 1
  have hyx : y * x = 1 := hy
  have hl : Function.Injective (LinearMap.mulLeft ℚ x) := by
    intro a b hab
    have hab' : x * a = x * b := hab
    have e : y * (x * a) = y * (x * b) := by rw [hab']
    rwa [← mul_assoc, ← mul_assoc, hyx, one_mul, one_mul] at e
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hl) 1
  have hxz : x * z = 1 := hz
  have hyz : y = z := by
    calc y = y * (x * z) := by rw [hxz, mul_one]
      _ = z := by rw [← mul_assoc, hyx, one_mul]
  exact hx ⟨⟨x, y, hyz ▸ hxz, hyx⟩, rfl⟩

/- English proof (translation)
Establish `h1 : ‖((n : ℕ) : ℤ_[p])‖ = ‖((n : ℚ) : ℚ_[p])‖`. Rewrite using `[PadicInt.norm_def]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn.ne'), padicValRat.of_nat]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_natCast_padicInt (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ‖((n : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ‖((n : ℕ) : ℤ_[p])‖ = ‖((n : ℚ) : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn.ne'), padicValRat.of_nat]
  push_cast; rfl

/- English proof (translation)
Establish `hfin` using `(GlobalTheory.T.end_isogeny_algebra_finite_finrank_le k A).1`. Establish `hx : ¬ IsUnit (toEnd0 A f)`. Introduce and unpack `⟨u, hu⟩`. Take `⟨n, g, hn, hg⟩` from `(toEnd0_injective_and_fraction k A).2 (↑u⁻¹ : End0 A)`. Establish `h1 : toEnd0 A (f * g) = toEnd0 A ((n : ℤ) • 𝟙 A)`.

Rewrite using `[map_mul, ← hg, ← hu, mul_smul_comm, Units.mul_inv, map_zsmul, natCast_zsmul]`. Both sides reduce to the same expression. Establish `h2 : g ≫ f = (n : ℤ) • 𝟙 A`. Rewrite using `[← End.mul_def]`. Conclude with `(toEnd0_injective_and_fraction k A).1 h1`.

Establish `hiso : IsIsogeny (g ≫ f)`. Rewrite using `[h2]; exact (GlobalTheory.MulIsogeny.mul_isogeny k A n (by exact_mod_cast hn.ne')).1`. Conclude with `hf ((isIsogeny_comp_iff_and_deg_comp k A A A g f rfl rfl).1.1 hiso).2`. Take `⟨y, hy0, hyx⟩` from `exists_mul_eq_zero_of_not_isUnit _ hx`. Take `⟨n, g, hn, hg⟩` from `(toEnd0_injective_and_fraction k A).2 y`.

Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hg` using `[map_zero]`. Establish `h0 : (n : ℚ) • y = 0` using `by rw [Nat.cast_smul_eq_nsmul]; exact hg`. Establish `hnq : (n : ℚ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Apply `hy0` to reduce the goal to its premises. Rewrite using `[← inv_smul_smul₀ hnq y, h0, smul_zero]`. Rewrite using `[← End.mul_def]`. Apply `(toEnd0_injective_and_fraction k A).1` to reduce the goal to its premises. Rewrite using `[map_mul, ← hg, smul_mul_assoc, hyx, smul_zero, map_zero]`.
-/
theorem exists_comp_eq_zero_of_not_isIsogeny {k : Type} [Field k] (A : AbVar k) (f : End A)
    (hf : ¬ IsIsogeny (A := A) (B := A) f) : ∃ g : End A, g ≠ 0 ∧ f ≫ g = 0 := by
  have hfin := (GlobalTheory.T.end_isogeny_algebra_finite_finrank_le k A).1
  have hx : ¬ IsUnit (toEnd0 A f) := by
    rintro ⟨u, hu⟩
    obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 (↑u⁻¹ : End0 A)
    have h1 : toEnd0 A (f * g) = toEnd0 A ((n : ℤ) • 𝟙 A) := by
      rw [map_mul, ← hg, ← hu, mul_smul_comm, Units.mul_inv, map_zsmul, natCast_zsmul]
      rfl
    have h2 : g ≫ f = (n : ℤ) • 𝟙 A := by
      rw [← End.mul_def]; exact (toEnd0_injective_and_fraction k A).1 h1
    have hiso : IsIsogeny (g ≫ f) := by
      rw [h2]; exact (GlobalTheory.MulIsogeny.mul_isogeny k A n (by exact_mod_cast hn.ne')).1
    exact hf ((isIsogeny_comp_iff_and_deg_comp k A A A g f rfl rfl).1.1 hiso).2
  obtain ⟨y, hy0, hyx⟩ := exists_mul_eq_zero_of_not_isUnit _ hx
  obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 y
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hg
    have h0 : (n : ℚ) • y = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hg
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply hy0
    rw [← inv_smul_smul₀ hnq y, h0, smul_zero]
  · rw [← End.mul_def]
    apply (toEnd0_injective_and_fraction k A).1
    rw [map_mul, ← hg, smul_mul_assoc, hyx, smul_zero, map_zero]

/- English proof (translation)
Introduce `p _ T k _ _ _ A G t _ _ ψ f d hd`. Establish `hlen` using `GlobalTheory.T.wittVector_colength_range_eq_det_valuation p k (T.M G) ψ (T.map (t.map t (Hom.hom f))) d hd`. Distinguish the cases in `hf : IsIsogeny (A := A) (B := A) f`. Establish `hb` using `(GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation p T k A A G G t t f).2.1 hf`. Establish `hpos` using `(isogeny_flat_finrank k A A f hf).2.2.1`.

Rewrite using `[hlen.1 _ hb.2, norm_natCast_padicInt p _ hpos]`. Establish `hdeg : deg (A` using `A) (B := A) f = 0 := by rw [deg, if_neg hf]`. Rewrite using `[hdeg, Nat.cast_zero, norm_zero, norm_eq_zero]`. Apply `hlen.2.1` to reduce the goal to its premises. Introduce `hinj`.

Take `⟨g, hg0, hfg⟩` from `exists_comp_eq_zero_of_not_isIsogeny A f hf`. Establish `hfun` using `GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial`. Establish `hcomp : t.map t (Hom.hom f) ≫ t.map t (Hom.hom g) = 0`. Establish `e1 : Hom.hom f ≫ Hom.hom g = (1 : A.X ⟶ A.X)` using `by rw [← comp_hom, hfg, zero_hom]`. Conclude with `(TorsionTower.map_comp t t t _ _).symm.trans ((t.map_congr t e1).trans (TorsionTower.map_one t t))`.

Establish `hne : T.map (t.map t (Hom.hom g)) ≠ 0`. Introduce `h0`. Conclude with `hg0 ((GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A A G G t t g).2 ((GlobalTheory.T.dieudonne_integrality_and_faithful p T k G G _).2 h0))`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm⟩ : ∃ m, T.map (t.map t (Hom.hom g)) m ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (LinearMap.ext h)`. Apply `hm` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises. Establish `e` using `hfun.2.1 (t.map t (Hom.hom f)) (t.map t (Hom.hom g))`.

Rewrite `e` using `[hcomp, hfun.2.2.2.1]`. Establish `e2` using `LinearMap.congr_fun e m`. Rewrite using `[map_zero]`. Conclude with `e2.symm.trans rfl`.
-/
theorem norm_det_eq_norm_deg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)]
    (ψ : ℤ_[p] →+* (WittVector p k)) (f : End A) (d : ℤ_[p]),
    LinearMap.det (T.map (t.map t (Hom.hom f))) = ψ d → ‖d‖ = ‖((deg (A := A) (B := A) f : ℕ) : ℤ_[p])‖ := by
  intro p _ T k _ _ _ A G t _ _ ψ f d hd
  have hlen := GlobalTheory.T.wittVector_colength_range_eq_det_valuation p k (T.M G) ψ (T.map (t.map t (Hom.hom f))) d hd
  by_cases hf : IsIsogeny (A := A) (B := A) f
  · have hb := (GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation p T k A A G G t t f).2.1 hf
    have hpos := (isogeny_flat_finrank k A A f hf).2.2.1
    rw [hlen.1 _ hb.2, norm_natCast_padicInt p _ hpos]
  · have hdeg : deg (A := A) (B := A) f = 0 := by rw [deg, if_neg hf]
    rw [hdeg, Nat.cast_zero, norm_zero, norm_eq_zero]
    apply hlen.2.1
    intro hinj
    obtain ⟨g, hg0, hfg⟩ := exists_comp_eq_zero_of_not_isIsogeny A f hf
    have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    have hcomp : t.map t (Hom.hom f) ≫ t.map t (Hom.hom g) = 0 := by
      have e1 : Hom.hom f ≫ Hom.hom g = (1 : A.X ⟶ A.X) := by rw [← comp_hom, hfg, zero_hom]
      exact (TorsionTower.map_comp t t t _ _).symm.trans ((t.map_congr t e1).trans (TorsionTower.map_one t t))
    have hne : T.map (t.map t (Hom.hom g)) ≠ 0 := by
      intro h0
      exact hg0 ((GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A A G G t t g).2 ((GlobalTheory.T.dieudonne_integrality_and_faithful p T k G G _).2 h0))
    obtain ⟨m, hm⟩ : ∃ m, T.map (t.map t (Hom.hom g)) m ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (LinearMap.ext h)
    apply hm
    apply hinj
    have e := hfun.2.1 (t.map t (Hom.hom f)) (t.map t (Hom.hom g))
    rw [hcomp, hfun.2.2.2.1] at e
    have e2 := LinearMap.congr_fun e m
    rw [map_zero]
    exact e2.symm.trans rfl

end GlobalTheory.Dieu.AbsDet
