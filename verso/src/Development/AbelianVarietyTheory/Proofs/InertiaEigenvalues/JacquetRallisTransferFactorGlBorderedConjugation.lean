import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormMulApplyLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisTransferFactorKrylovDet
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.OmegaInv

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_prod]`. Establish `hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1`. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]`.

Conclude with `mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hA _ _)`.
-/
theorem norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rw [norm_mul, norm_prod]
  have hs : ‖((Equiv.Perm.sign σ : ℤ) : F)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  exact mul_le_one₀ hs (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hA _ _)

/- English proof (translation)
Establish `hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2)` using `by rw [h]`. Unfold `eta`. Apply the tactic sequence `split_ifs <;> tauto`.
-/
theorem eta_congr {F : Type} [NormedField F] {x y : F} (h : ‖x‖ = ‖y‖) : eta x = eta y := by
  have hiff : (∃ z : F, ‖x‖ = ‖z‖ ^ 2) ↔ (∃ z : F, ‖y‖ = ‖z‖ ^ 2) := by rw [h]
  unfold eta
  split_ifs <;> tauto

/- English proof (translation)
Unfold `omega`. Apply `eta_congr` to reduce the goal to its premises. Establish `h1` using `(GlobalTheory.JR.transfer_factor_lemma F n).1`. Establish `h2` using `(GlobalTheory.JR.transfer_factor_lemma F n).2`. Establish `hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det`.

Rewrite using `[h1, h1, h2, Matrix.det_mul, mul_assoc]`. Establish `ha` using `norm_det_le_one _ (fun i j => (hk i j).1)`. Establish `hb` using `norm_det_le_one _ (fun i j => (hk i j).2)`. Establish `hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1`. Rewrite using `[← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]`.

Establish `hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1`. Apply `le_antisymm hb` to reduce the goal to its premises. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `: ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hl, norm_mul, hkinv, mul_one]`.
-/
theorem omega_act (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ)
    (k : GL (Fin n) F) (hk : k ∈ glO n F) (Y : Gl n F) : omega (act k Y) = omega Y := by
  unfold omega
  apply eta_congr
  have h1 := (GlobalTheory.JR.transfer_factor_lemma F n).1
  have h2 := (GlobalTheory.JR.transfer_factor_lemma F n).2
  have hl : lastDet (act k Y) = lastDet Y * ((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det := by
    rw [h1, h1, h2, Matrix.det_mul, mul_assoc]
  have ha := norm_det_le_one _ (fun i j => (hk i j).1)
  have hb := norm_det_le_one _ (fun i j => (hk i j).2)
  have hprod : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  have hkinv : ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ = 1 := by
    apply le_antisymm hb
    by_contra hlt
    push_neg at hlt
    have : ‖(k : Matrix (Fin n) (Fin n) F).det‖ * ‖((k⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det‖ < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt
    linarith
  rw [hl, norm_mul, hkinv, mul_one]

end GlobalTheory.JR.OmegaInv

/- English proof (translation)
Introduce `F _ _ n k hk Y` and use `GlobalTheory.JR.OmegaInv.omega_act F n k hk Y`.
-/
theorem GlobalTheory.JR.omega_act_glO : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] (n : ℕ) (k : GL (Fin n) F), k ∈ glO n F → ∀ Y : Gl n F, omega (act k Y) = omega Y :=
  fun F _ _ n k hk Y => GlobalTheory.JR.OmegaInv.omega_act F n k hk Y
