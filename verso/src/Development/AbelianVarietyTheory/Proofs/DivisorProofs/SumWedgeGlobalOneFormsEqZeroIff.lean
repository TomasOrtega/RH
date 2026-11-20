import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctionalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ C _ F hfr hH n u v`. Prove the components needed by the constructor for the conclusion. Introduce `hw l l'`. Take `⟨δ, -, hδ⟩` from `GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l`. Take `⟨δ', -, hδ'⟩` from `GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'`.

Establish `key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0`. Introduce `T`. Establish `h0` using `congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2 (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)`. Simplify using `only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti, Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0`. Simplify using `only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, hδ, hδ'] at h0`.

Rewrite using `[← h0, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨r, -, huniq⟩` from `hH 0 (map_zero _)`.

Establish `h1` using `huniq _ (fun T => by rw [key T]; rfl)`. Establish `h2` using `huniq 0 (fun T => by rw [map_zero]; rfl)`. Rewrite using `[h1, h2]`. Introduce `h`. Take `⟨m, ⟨Φ⟩⟩` from `hfr`.

Take `⟨L, -, hL⟩` from `GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ`. Use function extensionality and compare the values at `T`. Establish `hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T`. Introduce `w`. Use `conv_lhs => rw [hL w]`.

Simplify using `[Submodule.coe_sum, Finset.sum_apply]`. Set `x : Fin m → Fin m → Om R (F.obj T) 2` to `fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)`. Set `c : Fin m → Fin m → R` to `fun i j => ∑ k, L i (u k) * L j (v k)`. Establish `hc : ∀ i j, c i j = c j i`. Introduce `i j`.

Use `h (L i) (L j)` as an intermediate fact. Rewrite `this` using `[Finset.sum_sub_distrib, sub_eq_zero]`. Simplify using `only [c, this]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`. Establish `hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j`.

Establish `hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T` using `fun k => hexp _`. Establish `hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T` using `fun k => hexp _`. Simplify using `only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x, Finset.sum_smul, mul_smul]`. Use `conv_lhs => arg 2`. Use extensionality with `k`.

Rewrite using `[Finset.sum_comm]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _`.

Rewrite using `[Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]`. Use `Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce and unpack `⟨i, j⟩ _`. Simplify using `only [Prod.swap_prod_mk, x]`. Rewrite using `[hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]`.

Introduce and unpack `⟨i, j⟩ _ hne heq`. Apply `hne` to reduce the goal to its premises. Simplify using `only [Prod.swap_prod_mk, Prod.mk.injEq] at heq`. Take `⟨rfl, -⟩` from `heq`. Simplify using `[x]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem wsum_eq_zero_iff : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (n : ℕ) (u v : Fin n → Glob1 F), wsum F u v = 0 ↔ ∀ l l' : Glob1 F →ₗ[R] R, ∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k)) = 0 := by
  intro R _ C _ F hfr hH n u v
  constructor
  · intro hw l l'
    obtain ⟨δ, -, hδ⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l
    obtain ⟨δ', -, hδ'⟩ := GlobalTheory.T.exists_globalVectorField_of_oneForm_functional R C F hfr hH l'
    have key : ∀ T, algebraMap R (F.obj T) (∑ k, (l (u k) * l' (v k) - l (v k) * l' (u k))) = 0 := by
      intro T
      have h0 := congrArg (exteriorPower.pairingDual (F.obj T) Ω[F.obj T⁄R] 2
        (exteriorPower.ιMulti (F.obj T) 2 ![δ T, δ' T])) (congrFun hw T)
      simp only [wsum, map_sum, wedge_eq_ιMulti, exteriorPower.pairingDual_ιMulti_ιMulti,
        Matrix.det_fin_two, map_zero, Pi.zero_apply] at h0
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.head_cons, hδ, hδ'] at h0
      rw [← h0, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_sub, map_mul, map_mul]
      ring
    obtain ⟨r, -, huniq⟩ := hH 0 (map_zero _)
    have h1 := huniq _ (fun T => by rw [key T]; rfl)
    have h2 := huniq 0 (fun T => by rw [map_zero]; rfl)
    rw [h1, h2]
  · intro h
    obtain ⟨m, ⟨Φ⟩⟩ := hfr
    obtain ⟨L, -, hL⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F hH m Φ
    funext T
    have hexp : ∀ w : Glob1 F, w.1 T = ∑ i, L i w • (Φ.w i).1 T := by
      intro w
      conv_lhs => rw [hL w]
      simp [Submodule.coe_sum, Finset.sum_apply]
    let x : Fin m → Fin m → Om R (F.obj T) 2 := fun i j => wedge R _ ((Φ.w i).1 T) ((Φ.w j).1 T)
    let c : Fin m → Fin m → R := fun i j => ∑ k, L i (u k) * L j (v k)
    have hc : ∀ i j, c i j = c j i := by
      intro i j
      have := h (L i) (L j)
      rw [Finset.sum_sub_distrib, sub_eq_zero] at this
      simp only [c, this]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    have hsum : wsum F u v T = ∑ i, ∑ j, c i j • x i j := by
      have hu : ∀ k, (u k).1 T = ∑ i, L i (u k) • (Φ.w i).1 T := fun k => hexp _
      have hv : ∀ k, (v k).1 T = ∑ i, L i (v k) • (Φ.w i).1 T := fun k => hexp _
      simp only [wsum, hu, hv, map_sum, LinearMap.sum_apply, wedge_smul_left, wedge_smul_right, c, x,
        Finset.sum_smul, mul_smul]
      conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [Pi.zero_apply, hsum, ← Finset.sum_product' (f := fun i j => c i j • x i j)]
    refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
    · rintro ⟨i, j⟩ _
      simp only [Prod.swap_prod_mk, x]
      rw [hc j i, wedge_swap ((Φ.w j).1 T), smul_neg, add_neg_cancel]
    · rintro ⟨i, j⟩ _ hne heq
      apply hne
      simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
      obtain ⟨rfl, -⟩ := heq
      simp [x]
    · simp
    · simp

end GlobalTheory.AbCoh
