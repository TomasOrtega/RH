import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.MemSGIffFlagC

noncomputable section

namespace MassDataIdxStIm

open Matrix Formalism.FourierDecayAlt.S3

variable {K : Type} [Field K] {r k : ℕ}

/- English proof (translation)
Use `set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1`. Use `set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i`. Use `set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm`. Use `set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi`. Establish `e1 : G1 * G1i = 1` using `by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `e1' : G1i * G1 = 1` using `by rw [hG1, hG1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `eQ : Qm * Qi = 1` using `by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `eQ' : Qi * Qm = 1` using `by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `hJt : IsUnit J1ᵀ.det` using `by rw [Matrix.det_transpose]; exact hJ`. Establish `eJ : J1ᵀ⁻¹ * J1ᵀ = 1` using `Matrix.nonsing_inv_mul _ hJt`.

Establish `eJ' : J1ᵀ * J1ᵀ⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hJt`. Establish `hS : ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1 * Qm`. Simplify using `[hQi, hG1, hQm, Units.val_mul]`. Establish `hSi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm`. Establish `: (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q` using `by group`.

Rewrite using `[this]`. Simplify using `[hQi, hG1i, hQm, Units.val_mul]`. Establish `hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ`. Establish `hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ`. Use `congrArg Matrix.transpose hU` as an intermediate fact.

Simplify `this` using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Establish `hit : G1iᵀ * G1ᵀ = 1` using `by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]`. Use `_ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]`.

Rewrite using `[mem_sG_iff_flagC, hS, hSi]`. Use `and_congr ?_ ?_` and prove the remaining obligations. Rewrite using `[← flagC_conj Qi Qm G1 eQ eQ' y1]`. Conclude with `Iff.of_eq (congrArg _ (funext hy1))`. Rewrite using `[← flagC_conj J1ᵀ J1ᵀ⁻¹ g2 eJ eJ' y2, hT]`.

Establish `eQt : Qiᵀ * Qmᵀ = 1` using `by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]`. Establish `eQt' : Qmᵀ * Qiᵀ = 1` using `by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]`. Rewrite using `[← flagC_conj Qmᵀ Qiᵀ G1iᵀ eQt eQt' _]`. Establish `hv : (fun b => Qmᵀ *ᵥ (J1ᵀ *ᵥ y2 b)) = fun b => l b • Pi.single (pf (k` using `k) b) (1 : K) := funext hy2`. Rewrite using `[hv, flagC_smul _ l hl]`.

Establish `hm : Qmᵀ * G1iᵀ * Qiᵀ = (Qi * G1i * Qm)ᵀ`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[hm]`.
-/
theorem frame_mem_sG (g1 Q : GL (Idx r k) K) (g2 J1 : Matrix (Idx r k) (Idx r k) K) (hJ : IsUnit J1.det)
    (hU : g2ᵀ * J1 * (g1 : Matrix (Idx r k) (Idx r k) K) = J1)
    (y1 y2 : Fin (r + 1) → Idx r k → K) (l : Fin (r + 1) → K) (hl : ∀ b, l b ≠ 0)
    (hy1 : ∀ b, ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) *ᵥ y1 b = Pi.single (pe b) 1)
    (hy2 : ∀ b, (Q : Matrix (Idx r k) (Idx r k) K)ᵀ *ᵥ (J1ᵀ *ᵥ y2 b) = l b • Pi.single (pf b) 1) :
    (FlagC (g1 : Matrix (Idx r k) (Idx r k) K) y1 ∧ FlagC g2 y2) ↔ Q⁻¹ * g1 * Q ∈ sG K r k := by
  set G1 : Matrix (Idx r k) (Idx r k) K := (g1 : Matrix (Idx r k) (Idx r k) K) with hG1
  set G1i : Matrix (Idx r k) (Idx r k) K := ((g1⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hG1i
  set Qm : Matrix (Idx r k) (Idx r k) K := (Q : Matrix (Idx r k) (Idx r k) K) with hQm
  set Qi : Matrix (Idx r k) (Idx r k) K := ((Q⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) with hQi
  have e1 : G1 * G1i = 1 := by rw [hG1, hG1i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e1' : G1i * G1 = 1 := by rw [hG1, hG1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have eQ : Qm * Qi = 1 := by rw [hQm, hQi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have eQ' : Qi * Qm = 1 := by rw [hQm, hQi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hJt : IsUnit J1ᵀ.det := by rw [Matrix.det_transpose]; exact hJ
  have eJ : J1ᵀ⁻¹ * J1ᵀ = 1 := Matrix.nonsing_inv_mul _ hJt
  have eJ' : J1ᵀ * J1ᵀ⁻¹ = 1 := Matrix.mul_nonsing_inv _ hJt
  have hS : ((Q⁻¹ * g1 * Q : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1 * Qm := by
    simp [hQi, hG1, hQm, Units.val_mul]
  have hSi : (((Q⁻¹ * g1 * Q)⁻¹ : GL (Idx r k) K) : Matrix (Idx r k) (Idx r k) K) = Qi * G1i * Qm := by
    have : (Q⁻¹ * g1 * Q)⁻¹ = Q⁻¹ * g1⁻¹ * Q := by group
    rw [this]
    simp [hQi, hG1i, hQm, Units.val_mul]

  have hT : J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ := by
    have hUt : G1ᵀ * J1ᵀ * g2 = J1ᵀ := by
      have := congrArg Matrix.transpose hU
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    have hit : G1iᵀ * G1ᵀ = 1 := by rw [← Matrix.transpose_mul, e1, Matrix.transpose_one]
    calc J1ᵀ * g2 * J1ᵀ⁻¹ = G1iᵀ * (G1ᵀ * J1ᵀ * g2) * J1ᵀ⁻¹ := by
          rw [← Matrix.mul_assoc G1iᵀ, ← Matrix.mul_assoc G1iᵀ, hit, Matrix.one_mul]
      _ = G1iᵀ := by rw [hUt, Matrix.mul_assoc, eJ', Matrix.mul_one]
  rw [mem_sG_iff_flagC, hS, hSi]
  refine and_congr ?_ ?_
  · rw [← flagC_conj Qi Qm G1 eQ eQ' y1]
    exact Iff.of_eq (congrArg _ (funext hy1))
  · rw [← flagC_conj J1ᵀ J1ᵀ⁻¹ g2 eJ eJ' y2, hT]
    have eQt : Qiᵀ * Qmᵀ = 1 := by rw [← Matrix.transpose_mul, eQ, Matrix.transpose_one]
    have eQt' : Qmᵀ * Qiᵀ = 1 := by rw [← Matrix.transpose_mul, eQ', Matrix.transpose_one]
    rw [← flagC_conj Qmᵀ Qiᵀ G1iᵀ eQt eQt' _]
    have hv : (fun b => Qmᵀ *ᵥ (J1ᵀ *ᵥ y2 b)) = fun b => l b • Pi.single (pf (k := k) b) (1 : K) := funext hy2
    rw [hv, flagC_smul _ l hl]
    have hm : Qmᵀ * G1iᵀ * Qiᵀ = (Qi * G1i * Qm)ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [hm]

end MassDataIdxStIm
