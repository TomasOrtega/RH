import Mathlib

open Polynomial

namespace GlobalTheory.CompanionTheory.IntFac

/- English proof (translation)
Use `set N := F.natDegree + 1 with hN`. Distinguish the cases in `hk : k < N`. Use `swap`. Rewrite using `[coeff_eq_zero_of_natDegree_lt (by omega)]`. Conclude with `isIntegral_zero`.

Set `φ` to `algebraMap ℂ A`. Set `v : Fin N → ℂ` to `fun j => ((j : ℕ) : ℂ)`. Establish `hv : Function.Injective v` using `fun a b hab => Fin.ext (by simpa only [v, Nat.cast_inj] using hab)`. Set `V` to `Matrix.vandermonde v`. Establish `hdet : IsUnit V.det` using `isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)`.

Set `c : Fin N → A` to `fun j => F.coeff j`. Set `y : Fin N → A` to `fun i => F.eval (φ (v i))`. Establish `hy : Matrix.mulVec (V.map φ) c = y`. Use function extensionality and compare the values at `i`. Simplify using `only [y, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply, c]`.

Rewrite using `[eval_eq_sum_range' (Nat.lt_succ_self _), ← Fin.sum_univ_eq_sum_range (fun j => F.coeff j * φ (v i) ^ j)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, mul_comm]`. Establish `hc : c = Matrix.mulVec (V⁻¹.map φ) y`. Rewrite using `[← hy, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]`.

Establish `hmem : Matrix.mulVec (V⁻¹.map φ) y ⟨k, hk⟩ ∈ integralClosure ℂ A`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply]`. Conclude with `Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (h _)`. Establish `hck : F.coeff k = c ⟨k, hk⟩` using `rfl`. Rewrite using `[hck, hc]`.

Conclude with `hmem`.
-/
theorem isIntegral_coeff_of_eval (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ u : ℂ, IsIntegral ℂ (F.eval (algebraMap ℂ A u))) (k : ℕ) :
    IsIntegral ℂ (F.coeff k) := by
  classical
  set N := F.natDegree + 1 with hN
  by_cases hk : k < N
  swap
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact isIntegral_zero
  let φ := algebraMap ℂ A
  let v : Fin N → ℂ := fun j => ((j : ℕ) : ℂ)
  have hv : Function.Injective v := fun a b hab => Fin.ext (by simpa only [v, Nat.cast_inj] using hab)
  let V := Matrix.vandermonde v
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  let c : Fin N → A := fun j => F.coeff j
  let y : Fin N → A := fun i => F.eval (φ (v i))
  have hy : Matrix.mulVec (V.map φ) c = y := by
    funext i
    simp only [y, Matrix.mulVec, dotProduct, Matrix.map_apply, V, Matrix.vandermonde_apply, c]
    rw [eval_eq_sum_range' (Nat.lt_succ_self _),
      ← Fin.sum_univ_eq_sum_range (fun j => F.coeff j * φ (v i) ^ j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_pow, mul_comm]
  have hc : c = Matrix.mulVec (V⁻¹.map φ) y := by
    rw [← hy, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  have hmem : Matrix.mulVec (V⁻¹.map φ) y ⟨k, hk⟩ ∈ integralClosure ℂ A := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ =>
      Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (h _)
  have hck : F.coeff k = c ⟨k, hk⟩ := rfl
  rw [hck, hc]
  exact hmem

/- English proof (translation)
Rewrite using `[eval_eq_sum_range]`. Conclude with `IsIntegral.sum _ fun i _ => (h i).mul (isIntegral_algebraMap.pow _)`.
-/
theorem isIntegral_eval_of_coeff (A : Type) [CommRing A] [Algebra ℂ A] (F : A[X])
    (h : ∀ k, IsIntegral ℂ (F.coeff k)) (u : ℂ) : IsIntegral ℂ (F.eval (algebraMap ℂ A u)) := by
  rw [eval_eq_sum_range]
  exact IsIntegral.sum _ fun i _ => (h i).mul (isIntegral_algebraMap.pow _)

/- English proof (translation)
Take `⟨q, hq, -, hqm⟩` from `lifts_and_natDegree_eq_and_monic (f := algebraMap (integralClosure ℂ A) A) (p := F) ((lifts_iff_coeff_lifts F).mpr fun n => ⟨⟨F.coeff n, h n⟩, rfl⟩) hF`. Establish `hd' : G ∣ q.map (algebraMap (integralClosure ℂ A) A)`. Rewrite using `[hq]`. Conclude with `hd`. Conclude with `isIntegral_trans _ (isIntegral_coeff_of_dvd q G hqm hG hd' k)`.
-/
theorem isIntegral_coeff_of_monic_dvd (A : Type) [CommRing A] [Algebra ℂ A] (F G : A[X])
    (hF : F.Monic) (hG : G.Monic) (hd : G ∣ F) (h : ∀ k, IsIntegral ℂ (F.coeff k)) (k : ℕ) :
    IsIntegral ℂ (G.coeff k) := by
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
    (f := algebraMap (integralClosure ℂ A) A) (p := F)
    ((lifts_iff_coeff_lifts F).mpr fun n => ⟨⟨F.coeff n, h n⟩, rfl⟩) hF
  have hd' : G ∣ q.map (algebraMap (integralClosure ℂ A) A) := by
    rw [hq]
    exact hd
  exact isIntegral_trans _ (isIntegral_coeff_of_dvd q G hqm hG hd' k)

end GlobalTheory.CompanionTheory.IntFac

/- English proof (translation)
Introduce `A _ _ P Q c₁ c₂ hP hQ h k`. Use `set P₁ := P.comp (X + C (algebraMap ℂ A c₁)) with hP₁d`. Use `set Q₁ := Q.comp (X + C (algebraMap ℂ A c₂)) with hQ₁d`. Establish `hP₁ : P₁.Monic` using `hP.comp_X_add_C _`. Establish `hQ₁ : Q₁.Monic` using `hQ.comp_X_add_C _`.

Establish `hH : ∀ j, IsIntegral ℂ ((P₁ * Q₁).coeff j)` using `GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A (P₁ * Q₁) (fun u => by simpa [hP₁d, hQ₁d, eval_comp] using h u)`. Establish `i₁ : ∀ j, IsIntegral ℂ (P₁.coeff j)` using `GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hP₁ (dvd_mul_right _ _) hH`. Establish `i₂ : ∀ j, IsIntegral ℂ (Q₁.coeff j)` using `GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hQ₁ (dvd_mul_left _ _) hH`. Use `⟨GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A P (fun u => ?_) k, GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A Q (fun u => ?_) k⟩` and prove the remaining obligations. Establish `h₁` using `GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A P₁ i₁ (u - c₁)`.

Simplify `h₁` using `[hP₁d, eval_comp]`. Establish `h₂` using `GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A Q₁ i₂ (u - c₂)`. Simplify `h₂` using `[hQ₁d, eval_comp]`.
-/
theorem GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_shifted_product :
    ∀ (A : Type) [CommRing A] [Algebra ℂ A] (P Q : Polynomial A) (c₁ c₂ : ℂ), P.Monic → Q.Monic →
      (∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ A (u + c₁)) *
        Q.eval (algebraMap ℂ A (u + c₂)))) →
      ∀ k, IsIntegral ℂ (P.coeff k) ∧ IsIntegral ℂ (Q.coeff k) := by
  intro A _ _ P Q c₁ c₂ hP hQ h k
  set P₁ := P.comp (X + C (algebraMap ℂ A c₁)) with hP₁d
  set Q₁ := Q.comp (X + C (algebraMap ℂ A c₂)) with hQ₁d
  have hP₁ : P₁.Monic := hP.comp_X_add_C _
  have hQ₁ : Q₁.Monic := hQ.comp_X_add_C _
  have hH : ∀ j, IsIntegral ℂ ((P₁ * Q₁).coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A (P₁ * Q₁)
      (fun u => by simpa [hP₁d, hQ₁d, eval_comp] using h u)
  have i₁ : ∀ j, IsIntegral ℂ (P₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hP₁ (dvd_mul_right _ _) hH
  have i₂ : ∀ j, IsIntegral ℂ (Q₁.coeff j) :=
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_monic_dvd A _ _ (hP₁.mul hQ₁) hQ₁ (dvd_mul_left _ _) hH
  refine ⟨GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A P (fun u => ?_) k,
    GlobalTheory.CompanionTheory.IntFac.isIntegral_coeff_of_eval A Q (fun u => ?_) k⟩
  · have h₁ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A P₁ i₁ (u - c₁)
    simpa [hP₁d, eval_comp] using h₁
  · have h₂ := GlobalTheory.CompanionTheory.IntFac.isIntegral_eval_of_coeff A Q₁ i₂ (u - c₂)
    simpa [hQ₁d, eval_comp] using h₂
