import Mathlib
import Formalism.JacquetSubsetSums.JacquetSubsetSum
import Formalism.JacquetSubsetSums.SeparationTR

open Finset

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Matrix.det_vandermonde, ← Finset.prod_mul_distrib]`. Unfold `Formalism.PacketSums.vdm`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_mul_distrib]`. Establish `: Finset.univ.filter (fun j => i < j) = Ioi i` using `by ext; simp`.

Rewrite using `[this]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by
  rw [Matrix.det_vandermonde, ← Finset.prod_mul_distrib]
  unfold Formalism.PacketSums.vdm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  have : Finset.univ.filter (fun j => i < j) = Ioi i := by ext; simp
  rw [this]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Rewrite using `[packetSum_vdm_eq_det, packetSum_vdm_eq_det]`. Establish `: Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id`. Use extensionality with `i j`. Simplify using `[Matrix.vandermonde_apply]`. Rewrite using `[this, Matrix.det_permute]`.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma packetSum_vdm_perm {r : ℕ} (α : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.vdm (fun i => α (σ i)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * Formalism.PacketSums.vdm α := by
  rw [packetSum_vdm_eq_det, packetSum_vdm_eq_det]
  have : Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute]
  ring

/- English proof (translation)
Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.
-/
lemma packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/- English proof (translation)
Unfold `Formalism.PacketSums.numK`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) = ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j)`. Rewrite using `[← Equiv.prod_comp y]`.

Simplify using `[mul_inv_rev, Equiv.Perm.mul_apply]`. Rewrite using `[hp, ← mul_assoc]`. Use `congr 1`. Establish `hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) = Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r)))`. Rewrite using `[Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]`.

Rewrite using `[hs]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma packetSum_numK_perm {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK]
    (μ : Fin r → ℤ) (α : Fin r → ℂ) (y : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) =
      ((Equiv.Perm.sign y : ℤ) : ℂ) * ∑ w : WK,
        ((Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) : ℤ) : ℂ) *
          ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
  unfold Formalism.PacketSums.numK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) =
      ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
    rw [← Equiv.prod_comp y]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hp, ← mul_assoc]
  congr 1
  have hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) =
      Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [hs]; push_cast; ring

/- English proof (translation)
Introduce `r WK _ T hbij μ α _ _`. Use `set f : Equiv.Perm (Fin r) → ℂ := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf`. Establish `hterm : ∀ y : Equiv.Perm (Fin r), Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) = (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α`. Introduce `y`. Rewrite using `[packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv, mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]`.

Rewrite using `[Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]`. Use `congr 1`. Rewrite using `[← Finset.sum_coe_sort T]`. Rewrite using `[← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f (fun _ => rfl)]`. Rewrite using `[Fintype.sum_prod_type_right]`.
-/
theorem packetSum : Formalism.PacketSums.PacketSum := by
  intro r WK _ T hbij μ α _ _
  set f : Equiv.Perm (Fin r) → ℂ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf
  have hterm : ∀ y : Equiv.Perm (Fin r),
      Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) =
        (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α := by
    intro y
    rw [packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv,
      mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort T]
  rw [← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end GlobalTheory
