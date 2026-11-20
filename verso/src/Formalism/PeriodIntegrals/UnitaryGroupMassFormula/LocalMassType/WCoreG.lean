import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.TransitiveOverLocalRings

noncomputable section

namespace PI.LocMassTypL

open Matrix PI.LocMassTypW.WCoreP

/- English proof (translation)
Use `set K' : Matrix (Fin n) (Fin n) O := A' * L0 - Mᵀ * B'ᵀ * (1 - A0 * L0) with hK'`. Establish `h1 : (1 - A0 * L0) * A0 = 0`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]`. Establish `hkey : t • (A0ᵀ * B' + A'ᵀ * B) = 0`. Establish `e : Aᵀ * B = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hA, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul]`. Use `_ = A0ᵀ * B0 + t • (A0ᵀ * B') + t • (A'ᵀ * B) := by nth_rewrite 1 [hB]; rw [Matrix.mul_add, Matrix.mul_smul]`. Use `_ = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by rw [smul_add, add_assoc]`. Rewrite `hC` using `[e]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hBM : Bᵀ * Mᵀ = 1` using `by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]`. Establish `key' : t • (Bᵀ * A') + t • (B'ᵀ * A0) = 0`. Use `congrArg Matrix.transpose hkey` as an intermediate fact. Simplify using `only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero, smul_add] at this`.

Rewrite using `[add_comm]`. Conclude with `this`. Establish `hB0 : B0ᵀ = Bᵀ - t • B'ᵀ`. Rewrite using `[hB, Matrix.transpose_add, Matrix.transpose_smul, add_sub_cancel_right]`. Establish `hk : Bᵀ * (1 + t • K') = B0ᵀ`.

Establish `e : Bᵀ * (1 + t • K') = Bᵀ - t • B'ᵀ + (t • (Bᵀ * A') + t • (B'ᵀ * A0)) * L0`. Simplify using `only [hK', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub, ← Matrix.mul_assoc, hBM, Matrix.one_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, key', Matrix.zero_mul, add_zero, hB0]`. Use `⟨1 + t • K', K', ?_, ?_, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Establish `ht0 : IsLocalRing.residue O t = 0` using `(IsLocalRing.residue_eq_zero_iff t).2 ht`. Establish `hmap : (IsLocalRing.residue O).mapMatrix (1 + t • K') = 1`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, apply_ite, ht0]`.

Establish `hdet : IsLocalRing.residue O (1 + t • K').det = 1`. Rewrite using `[RingHom.map_det, hmap, Matrix.det_one]`. Assume the negation of the conclusion as `hnu`. Establish `hm : (1 + t • K').det ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hnu`. Rewrite `hdet` using `[(IsLocalRing.residue_eq_zero_iff _).2 hm]`.

Conclude with `zero_ne_one hdet`. Rewrite using `[Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hK', Matrix.sub_mul, Matrix.mul_assoc A', hL0, Matrix.mul_one, Matrix.mul_assoc (Mᵀ * B'ᵀ), h1, Matrix.mul_zero, sub_zero, hA]`. Rewrite using `[← Matrix.transpose_transpose B, ← Matrix.transpose_mul, hk, Matrix.transpose_transpose]`.
-/
theorem wCoreG (O : Type) [CommRing O] [IsLocalRing O] {n m : ℕ} (t : O)
    (ht : t ∈ IsLocalRing.maximalIdeal O) (A0 A B0 B A' B' : Matrix (Fin n) (Fin m) O)
    (L0 M : Matrix (Fin m) (Fin n) O) (hL0 : L0 * A0 = 1) (hM : M * B = 1)
    (hC : A0ᵀ * B0 = Aᵀ * B) (hA : A = A0 + t • A') (hB : B = B0 + t • B') :
    ∃ k K' : Matrix (Fin n) (Fin n) O, IsUnit k ∧ k * A0 = A ∧ kᵀ * B = B0 ∧ k = 1 + t • K' := by
  classical
  set K' : Matrix (Fin n) (Fin n) O := A' * L0 - Mᵀ * B'ᵀ * (1 - A0 * L0) with hK'

  have h1 : (1 - A0 * L0) * A0 = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hL0, Matrix.mul_one, sub_self]

  have hkey : t • (A0ᵀ * B' + A'ᵀ * B) = 0 := by
    have e : Aᵀ * B = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by
      calc Aᵀ * B = A0ᵀ * B + t • (A'ᵀ * B) := by
            rw [hA, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B') + t • (A'ᵀ * B) := by
            nth_rewrite 1 [hB]; rw [Matrix.mul_add, Matrix.mul_smul]
        _ = A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B) := by rw [smul_add, add_assoc]
    rw [e] at hC
    calc t • (A0ᵀ * B' + A'ᵀ * B) = (A0ᵀ * B0 + t • (A0ᵀ * B' + A'ᵀ * B)) - A0ᵀ * B0 := by abel
      _ = 0 := by rw [← hC, sub_self]
  have hBM : Bᵀ * Mᵀ = 1 := by rw [← Matrix.transpose_mul, hM, Matrix.transpose_one]
  have key' : t • (Bᵀ * A') + t • (B'ᵀ * A0) = 0 := by
    have := congrArg Matrix.transpose hkey
    simp only [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_zero, smul_add] at this
    rw [add_comm]; exact this
  have hB0 : B0ᵀ = Bᵀ - t • B'ᵀ := by
    rw [hB, Matrix.transpose_add, Matrix.transpose_smul, add_sub_cancel_right]
  have hk : Bᵀ * (1 + t • K') = B0ᵀ := by
    have e : Bᵀ * (1 + t • K') = Bᵀ - t • B'ᵀ + (t • (Bᵀ * A') + t • (B'ᵀ * A0)) * L0 := by
      simp only [hK', Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_sub,
        ← Matrix.mul_assoc, hBM, Matrix.one_mul, Matrix.add_mul, Matrix.smul_mul, smul_sub]
      abel
    rw [e, key', Matrix.zero_mul, add_zero, hB0]
  refine ⟨1 + t • K', K', ?_, ?_, ?_, rfl⟩
  ·
    rw [Matrix.isUnit_iff_isUnit_det]
    have ht0 : IsLocalRing.residue O t = 0 := (IsLocalRing.residue_eq_zero_iff t).2 ht
    have hmap : (IsLocalRing.residue O).mapMatrix (1 + t • K') = 1 := by
      ext i j
      simp [Matrix.one_apply, apply_ite, ht0]
    have hdet : IsLocalRing.residue O (1 + t • K').det = 1 := by
      rw [RingHom.map_det, hmap, Matrix.det_one]
    by_contra hnu
    have hm : (1 + t • K').det ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hm] at hdet
    exact zero_ne_one hdet
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hK', Matrix.sub_mul, Matrix.mul_assoc A',
      hL0, Matrix.mul_one, Matrix.mul_assoc (Mᵀ * B'ᵀ), h1, Matrix.mul_zero, sub_zero, hA]
  · rw [← Matrix.transpose_transpose B, ← Matrix.transpose_mul, hk,
      Matrix.transpose_transpose]

end PI.LocMassTypL
