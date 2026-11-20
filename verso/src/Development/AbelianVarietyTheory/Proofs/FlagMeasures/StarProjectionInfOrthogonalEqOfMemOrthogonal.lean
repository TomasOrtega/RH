import Mathlib

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Conclude with `Submodule.mem_inf.2 ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩`. Introduce `w hw`. Rewrite using `[sub_sub_cancel]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y) (Submodule.mem_inf.1 hw).2`.
-/
theorem starProjection_inf_orthogonal_eq_sub {n : ℕ}
    (A A' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : A' ≤ A) (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact Submodule.mem_inf.2
      ⟨A.sub_mem hy (h (A'.starProjection_apply_mem y)), A'.sub_starProjection_mem_orthogonal y⟩
  · intro w hw
    rw [sub_sub_cancel]
    exact Submodule.inner_right_of_mem_orthogonal (A'.starProjection_apply_mem y)
      (Submodule.mem_inf.1 hw).2

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero` to reduce the goal to its premises. Use `Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.mem_orthogonal]`. Introduce `z hz`. Rewrite using `[← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]`.

Conclude with `Submodule.inner_right_of_mem_orthogonal hz hv`. Introduce `w hw`. Conclude with `C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1`.
-/
theorem starProjection_inf_orthogonal_eq_of_mem_orthogonal {n : ℕ}
    (C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : C' ≤ C) (v : EuclideanSpace ℂ (Fin n))
    (hv : v ∈ C'ᗮ) : (C ⊓ C'ᗮ).starProjection v = C.starProjection v := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · refine Submodule.mem_inf.2 ⟨C.starProjection_apply_mem v, ?_⟩
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 (h hz)]
    exact Submodule.inner_right_of_mem_orthogonal hz hv
  · intro w hw
    exact C.starProjection_inner_eq_zero v w (Submodule.mem_inf.1 hw).1

/- English proof (translation)
Establish `hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ`. Establish `hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))`. Introduce `a b hab`. Establish `h0 : ‖D (a - b)‖ = 0`. Rewrite using `[map_sub]`.

Simplify using `only [ContinuousLinearMap.coe_coe] at hab`. Rewrite using `[hab, sub_self, norm_zero]`. Rewrite `h0` using `[hD, norm_eq_zero, sub_eq_zero]`. Then use the resulting hypothesis. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Rewrite using `[Submodule.mem_orthogonal]`. Introduce `z hz`. Conclude with `hB' x hx z hz`. Rewrite using `[← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]`. Use `symm`.

Apply `Submodule.finrank_add_finrank_orthogonal'` to reduce the goal to its premises. Rewrite using `[finrank_euclideanSpace_fin]`. Conclude with `hdim`. Establish `hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y` using `starProjection_inf_orthogonal_eq_sub A A' hA y hy`. Establish `hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A`.

Rewrite using `[hy1]`. Conclude with `A.sub_mem hy (hA (A'.starProjection_apply_mem y))`. Use `set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def`. Establish `hw : w ∈ C'ᗮ`. Rewrite using `[Submodule.mem_orthogonal]`.

Introduce `z hz`. Conclude with `hB _ (hT _ hy1A) z hz`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by`. Establish `hmem : Cᗮ.starProjection w ∈ B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))`. Rewrite using `[hmap]`.

Conclude with `Cᗮ.starProjection_apply_mem w`. Take `⟨b, hb, hbw⟩` from `hmem`. Conclude with `⟨b, hb, hbw⟩`. Establish `hmemB' : T (A'.starProjection y) + b ∈ B'` using `B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[dist_eq_norm, hy1, map_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Use `_ = ‖w - Cᗮ.starProjection w‖ := by`. Rewrite using `[← hD, map_sub, hbw]`.

Use `_ = ‖C.starProjection w‖ := by`. Rewrite using `[Submodule.starProjection_orthogonal_val, sub_sub_cancel]`. Use `_ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by`. Rewrite using `[starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]`. Use `_ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl`.

Use `_ ≤ _ := ContinuousLinearMap.le_opNorm _ _`.
-/
theorem infDist_le_norm_block_mul (n : ℕ)
    (A A' B B' C C' : Submodule ℂ (EuclideanSpace ℂ (Fin n)))
    (D T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))
    (hD : ∀ x, ‖D x‖ = ‖x‖) (hA : A' ≤ A) (hC : C' ≤ C)
    (hB : ∀ x ∈ B, ∀ z ∈ C', ⟪z, D x⟫_ℂ = 0) (hB' : ∀ x ∈ B', ∀ z ∈ C, ⟪z, D x⟫_ℂ = 0)
    (hdim : Module.finrank ℂ C + Module.finrank ℂ B' = n)
    (hT : ∀ y ∈ A, T y ∈ B) (hT' : ∀ y ∈ A', T y ∈ B') (y : EuclideanSpace ℂ (Fin n))
    (hy : y ∈ A) :
    Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n))) ≤
      ‖(C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection‖ * ‖y‖ := by
  have hmap : B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) = Cᗮ := by
    have hinj : Function.Injective (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      intro a b hab
      have h0 : ‖D (a - b)‖ = 0 := by
        rw [map_sub]
        simp only [ContinuousLinearMap.coe_coe] at hab
        rw [hab, sub_self, norm_zero]
      rwa [hD, norm_eq_zero, sub_eq_zero] at h0
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_orthogonal]
      intro z hz
      exact hB' x hx z hz
    · rw [← (Submodule.equivMapOfInjective _ hinj B').finrank_eq]
      symm
      apply Submodule.finrank_add_finrank_orthogonal'
      rw [finrank_euclideanSpace_fin]
      exact hdim
  have hy1 : (A ⊓ A'ᗮ).starProjection y = y - A'.starProjection y :=
    starProjection_inf_orthogonal_eq_sub A A' hA y hy
  have hy1A : (A ⊓ A'ᗮ).starProjection y ∈ A := by
    rw [hy1]
    exact A.sub_mem hy (hA (A'.starProjection_apply_mem y))
  set w := D (T ((A ⊓ A'ᗮ).starProjection y)) with hw_def
  have hw : w ∈ C'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    exact hB _ (hT _ hy1A) z hz
  obtain ⟨b, hb, hbw⟩ : ∃ b ∈ B', D b = Cᗮ.starProjection w := by
    have hmem : Cᗮ.starProjection w ∈
        B'.map (D : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
      rw [hmap]
      exact Cᗮ.starProjection_apply_mem w
    obtain ⟨b, hb, hbw⟩ := hmem
    exact ⟨b, hb, hbw⟩
  have hmemB' : T (A'.starProjection y) + b ∈ B' :=
    B'.add_mem (hT' _ (A'.starProjection_apply_mem y)) hb
  calc Metric.infDist (T y) (B' : Set (EuclideanSpace ℂ (Fin n)))
      ≤ dist (T y) (T (A'.starProjection y) + b) := Metric.infDist_le_dist_of_mem hmemB'
    _ = ‖T ((A ⊓ A'ᗮ).starProjection y) - b‖ := by
      rw [dist_eq_norm, hy1, map_sub]
      congr 1
      abel
    _ = ‖w - Cᗮ.starProjection w‖ := by
      rw [← hD, map_sub, hbw]
    _ = ‖C.starProjection w‖ := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
    _ = ‖(C ⊓ C'ᗮ).starProjection w‖ := by
      rw [starProjection_inf_orthogonal_eq_of_mem_orthogonal C C' hC w hw]
    _ = ‖((C ⊓ C'ᗮ).starProjection ∘L (D ∘L T) ∘L (A ⊓ A'ᗮ).starProjection) y‖ := rfl
    _ ≤ _ := ContinuousLinearMap.le_opNorm _ _

end GlobalTheory
