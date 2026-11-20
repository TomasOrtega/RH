import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MinkowskiBound.PowerSumStep

namespace PI.Mk

open Matrix Finset

/- English proof (translation)
Establish `hf : IsIdempotentElem (Matrix.toLin' E)`. Express the relevant statement in the definitionally equal form `Matrix.toLin' E ∘ₗ Matrix.toLin' E = Matrix.toLin' E`. Rewrite using `[← Matrix.toLin'_mul, hE]`. Use `⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' E)), ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.trace_toLin'_eq]`.

Conclude with `(LinearMap.IsIdempotentElem.isProj_range _ hf).trace`.
-/
theorem trace_idem_nat {n : Type*} [Fintype n] [DecidableEq n] (E : Matrix n n ℚ) (hE : E * E = E) :
    ∃ r : ℕ, E.trace = (r : ℚ) := by
  have hf : IsIdempotentElem (Matrix.toLin' E) := by
    change Matrix.toLin' E ∘ₗ Matrix.toLin' E = Matrix.toLin' E
    rw [← Matrix.toLin'_mul, hE]
  refine ⟨Module.finrank ℚ (LinearMap.range (Matrix.toLin' E)), ?_⟩
  rw [← Matrix.trace_toLin'_eq]
  exact (LinearMap.IsIdempotentElem.isProj_range _ hf).trace

/- English proof (translation)
Set `M : H → Matrix n n ℚ` to `fun h => (ρ h).map (Int.castRingHom ℚ)`. Establish `hM : ∀ a b, M (a * b) = M a * M b` using `fun a b => by`. Simplify using `only [M, hρ, Matrix.map_mul]`. Establish `hc : (Fintype.card H : ℚ) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hsum : ∀ a, M a * ∑ h, M h = ∑ h, M h` using `fun a => by`.

Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[← hM]`. Conclude with `Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)`. Establish `hE : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) * ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) = (Fintype.card H : ℚ)⁻¹ • ∑ h, M h`. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul]`.

Repeatedly rewrite using `[hsum]`. Rewrite using `[Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hc, mul_one]`. Take `⟨r, hr⟩` from `trace_idem_nat _ hE`. Establish `htr : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h).trace = (Fintype.card H : ℚ)⁻¹ * ∑ h, ((ρ h).trace : ℚ)`. Rewrite using `[Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Simplify using `[M, Matrix.trace]`. Rewrite `hr` using `[htr, inv_mul_eq_iff_eq_mul₀ hc]`. Use `⟨(r : ℤ), ?_⟩` and prove the remaining obligations.

Establish `h2 : ((∑ h, (ρ h).trace : ℤ) : ℚ) = (((Fintype.card H : ℤ) * (r : ℤ) : ℤ) : ℚ)`. Use `push_cast`. Conclude with `hr`. Conclude with `h2` after adjusting the coercions.
-/
theorem card_dvd_sum_trace {H : Type*} [Group H] [Fintype H] {n : Type*} [Fintype n] [DecidableEq n]
    (ρ : H → Matrix n n ℤ) (hρ : ∀ a b, ρ (a * b) = ρ a * ρ b) :
    (Fintype.card H : ℤ) ∣ ∑ h : H, (ρ h).trace := by
  classical
  let M : H → Matrix n n ℚ := fun h => (ρ h).map (Int.castRingHom ℚ)
  have hM : ∀ a b, M (a * b) = M a * M b := fun a b => by
    simp only [M, hρ, Matrix.map_mul]
  have hc : (Fintype.card H : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : ∀ a, M a * ∑ h, M h = ∑ h, M h := fun a => by
    rw [Finset.mul_sum]
    simp_rw [← hM]
    exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ (fun _ => rfl)
  have hE : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) * ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h) =
      (Fintype.card H : ℚ)⁻¹ • ∑ h, M h := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Finset.sum_mul]
    simp_rw [hsum]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul,
      mul_assoc, inv_mul_cancel₀ hc, mul_one]
  obtain ⟨r, hr⟩ := trace_idem_nat _ hE
  have htr : ((Fintype.card H : ℚ)⁻¹ • ∑ h, M h).trace = (Fintype.card H : ℚ)⁻¹ * ∑ h, ((ρ h).trace : ℚ) := by
    rw [Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun h _ => ?_
    simp [M, Matrix.trace]
  rw [htr, inv_mul_eq_iff_eq_mul₀ hc] at hr
  refine ⟨(r : ℤ), ?_⟩
  have h2 : ((∑ h, (ρ h).trace : ℤ) : ℚ) = (((Fintype.card H : ℤ) * (r : ℤ) : ℤ) : ℚ) := by
    push_cast
    exact hr
  exact_mod_cast h2

def kron {n : Type*} (k : ℕ) (M : Matrix n n ℤ) : Matrix (Fin k → n) (Fin k → n) ℤ :=
  fun i j => ∏ t, M (i t) (j t)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [kron, Matrix.mul_apply]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.
-/
theorem kron_mul {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A B : Matrix n n ℤ) :
    kron k (A * B) = kron k A * kron k B := by
  ext i j
  simp only [kron, Matrix.mul_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.prod_mul_distrib]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, kron]`. Rewrite using `[show (∑ i, A i i) ^ k = ∏ _t : Fin k, ∑ j, A j j by`. Rewrite using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin],`. Use the proof step `Finset.prod_univ_sum, Fintype.piFinset_univ]`.
-/
theorem trace_kron {n : Type*} [Fintype n] [DecidableEq n] (k : ℕ) (A : Matrix n n ℤ) :
    (kron k A).trace = A.trace ^ k := by
  simp only [Matrix.trace, Matrix.diag, kron]
  rw [show (∑ i, A i i) ^ k = ∏ _t : Fin k, ∑ j, A j j by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin],
    Finset.prod_univ_sum, Fintype.piFinset_univ]

/- English proof (translation)
Introduce `N P _ k`. Establish `h` using `card_dvd_sum_trace (H := P) (fun g => kron k (((g : Matrix.GeneralLinearGroup (Fin N) ℤ)) : Matrix (Fin N) (Fin N) ℤ)) (fun a b => by simp only [Subgroup.coe_mul, Units.val_mul, kron_mul])`. Simplify `h` using `only [trace_kron]`.
-/
theorem powerSumStep : PowerSumStep := by
  intro N P _ k
  have h := card_dvd_sum_trace (H := P)
    (fun g => kron k (((g : Matrix.GeneralLinearGroup (Fin N) ℤ)) : Matrix (Fin N) (Fin N) ℤ))
    (fun a b => by simp only [Subgroup.coe_mul, Units.val_mul, kron_mul])
  simpa only [trace_kron] using h

end PI.Mk
