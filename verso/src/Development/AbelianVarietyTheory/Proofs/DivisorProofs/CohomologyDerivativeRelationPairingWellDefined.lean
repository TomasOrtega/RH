import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Take `⟨m, ⟨fr⟩⟩` from `hF`. Use `⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (fr.w i)) • fr.δ i T, fun T T' φ ω ↦ ?_, fun w T ↦ ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, fr.nat, smul_eq_mul, map_sum, map_mul, AlgHom.commutes]`. Establish `hc : ∀ i, ∃ c : R, ∀ T, fr.δ i T (w.1 T) = algebraMap R (F.obj T) c` using `fun i ↦ by`. Take `⟨c, hc, -⟩` from `h0 (fun T ↦ fr.δ i T (w.1 T)) (by`.

Use function extensionality and compare the values at `T T' φ`. Simplify using `only [amitsur_d0_apply, Pi.zero_apply]`. Rewrite using `[w.2 φ, fr.nat, sub_self])`. Conclude with `⟨c, hc⟩`. Use `choose c hc using hc`.

Establish `hw : w = ∑ i, c i • fr.w i`. Use `Subtype.ext (funext fun T ↦ ?_)` and prove the remaining obligations. Rewrite using `[fr.sum T (w.1 T)]`. Simplify using `only [hc, algebraMap_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]`. Use `conv_rhs => rw [hw]`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul, hc, smul_eq_mul, map_mul]`. Conclude with `Finset.sum_congr rfl fun i _ ↦ mul_comm _ _`.
-/
theorem exists_vf_of_frame {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (l : Glob1 F →ₗ[R] R) :
    ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T,
      (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧
      ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  obtain ⟨m, ⟨fr⟩⟩ := hF
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (fr.w i)) • fr.δ i T, fun T T' φ ω ↦ ?_, fun w T ↦ ?_⟩
  · simp only [LinearMap.sum_apply, LinearMap.smul_apply, fr.nat, smul_eq_mul, map_sum,
      map_mul, AlgHom.commutes]
  · have hc : ∀ i, ∃ c : R, ∀ T, fr.δ i T (w.1 T) = algebraMap R (F.obj T) c := fun i ↦ by
      obtain ⟨c, hc, -⟩ := h0 (fun T ↦ fr.δ i T (w.1 T)) (by
        funext T T' φ
        simp only [amitsur_d0_apply, Pi.zero_apply]
        rw [w.2 φ, fr.nat, sub_self])
      exact ⟨c, hc⟩
    choose c hc using hc
    have hw : w = ∑ i, c i • fr.w i := by
      refine Subtype.ext (funext fun T ↦ ?_)
      rw [fr.sum T (w.1 T)]
      simp only [hc, algebraMap_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]
    conv_rhs => rw [hw]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, LinearMap.map_smul, hc, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ C _ F hF h0 x n n' y w y' w' hd hd' l`. Take `⟨δ, hnat, hδ⟩` from `exists_vf_of_frame F hF h0 l`. Take `⟨f, g, ω, rfl, hg, hf⟩` from `hd`. Take `⟨f', g', ω', hx, hg', hf'⟩` from `hd'`. Take `⟨b, hb⟩` from `H1.mk_eq_mk.1 hx`.

Take `rfl : y = fun k ↦ H1.mk F (g k)` from `funext fun k ↦ (hg k).symm`. Take `rfl : y' = fun k ↦ H1.mk F (g' k)` from `funext fun k ↦ (hg' k).symm`. Establish `e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k)` using `by simp [map_sum, map_smul]`. Establish `e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k)` using `by simp [map_sum, map_smul]`. Rewrite using `[e1, e2, H1.mk_eq_mk]`.

Use `⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Establish `hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ` using `congrFun (congrFun (congrFun hb T) T') φ`. Establish `key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T))`. Rewrite using `[← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]`.

Rewrite `key` using `[hf φ, hf' φ]`. Establish `e` using `congrArg (δ T') key`. Simplify using `only [map_sub, map_add, map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e`. Simplify using `only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]`. Simplify using `only [Algebra.smul_def]`.

Simplify using `only [mul_comm (algebraMap R _ _)] at e ⊢`. Take the linear combination `e`.
-/
theorem derivClass_eq : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (x : GlobalTheory.CatCoh.H1 F) (n n' : ℕ) (y : Fin n → GlobalTheory.CatCoh.H1 F) (w : Fin n → Glob1 F) (y' : Fin n' → GlobalTheory.CatCoh.H1 F) (w' : Fin n' → Glob1 F), DRel F x y w → DRel F x y' w' → ∀ l : Glob1 F →ₗ[R] R, ∑ k, l (w k) • y k = ∑ k, l (w' k) • y' k := by
  intro R _ C _ F hF h0 x n n' y w y' w' hd hd' l
  obtain ⟨δ, hnat, hδ⟩ := exists_vf_of_frame F hF h0 l
  obtain ⟨f, g, ω, rfl, hg, hf⟩ := hd
  obtain ⟨f', g', ω', hx, hg', hf'⟩ := hd'
  obtain ⟨b, hb⟩ := H1.mk_eq_mk.1 hx
  obtain rfl : y = fun k ↦ H1.mk F (g k) := funext fun k ↦ (hg k).symm
  obtain rfl : y' = fun k ↦ H1.mk F (g' k) := funext fun k ↦ (hg' k).symm
  have e1 : ∑ k, l (w k) • H1.mk F (g k) = H1.mk F (∑ k, l (w k) • g k) := by simp [map_sum, map_smul]
  have e2 : ∑ k, l (w' k) • H1.mk F (g' k) = H1.mk F (∑ k, l (w' k) • g' k) := by simp [map_sum, map_smul]
  rw [e1, e2, H1.mk_eq_mk]
  refine ⟨fun T ↦ δ T (ω' T - ω T - D R _ (b T)), ?_⟩
  funext T T' φ
  have hbφ : d0 F b T T' φ = f'.1 T T' φ - f.1 T T' φ := congrFun (congrFun (congrFun hb T) T') φ
  have key : D R _ (f'.1 T T' φ) - D R _ (f.1 T T' φ) = D R _ (b T') - p1 F φ (D R _ (b T)) := by
    rw [← map_sub, ← hbφ, amitsur_d0_apply, map_sub, p1_D]
  rw [hf φ, hf' φ] at key
  have e := congrArg (δ T') key
  simp only [map_sub, map_add, map_sum, LinearMap.map_smul, hnat, hδ, smul_eq_mul] at e
  simp only [amitsur_d0_apply, map_sub, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.sub_apply, Pi.smul_apply]
  simp only [Algebra.smul_def]
  simp only [mul_comm (algebraMap R _ _)] at e ⊢
  linear_combination e

end GlobalTheory.AbCoh
