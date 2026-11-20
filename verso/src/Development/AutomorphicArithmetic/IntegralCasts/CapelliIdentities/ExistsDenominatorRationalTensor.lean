import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh61.VQ :
    {p : ℕ} → [inst : Fact (Nat.Prime p)] → GlobalTheory.UPel.HT.Datum p → Type :=
    fun {p : ℕ} [Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) ↦ TensorProduct ℤ ℚ D.La

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, one_pos, 0, by simp⟩`. Consider the case `tmul q m`. Use `⟨q.den, q.den_pos, q.num • m, ?_⟩` and prove the remaining obligations. Establish `h : q.den • q = q.num • (1 : ℚ)`.

Rewrite using `[nsmul_eq_mul, zsmul_eq_mul, mul_one, mul_comm, Rat.mul_den_eq_num]`. Rewrite using `[TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy`. Take `⟨k, hk, a, ha⟩` from `hx`. Take `⟨l, hl, b, hb⟩` from `hy`.

Use `⟨k * l, Nat.mul_pos hk hl, l • a + k • b, ?_⟩` and prove the remaining obligations. Establish `e : ∀ (n : ℕ) (c : M), (1 : ℚ) ⊗ₜ[ℤ] (n • c) = n • ((1 : ℚ) ⊗ₜ[ℤ] c)` using `fun n c => map_nsmul (TensorProduct.mk ℤ ℚ M 1) n c`. Rewrite using `[TensorProduct.tmul_add, e, e, ← ha, ← hb, smul_add, smul_smul, smul_smul, mul_comm l k]`.
-/
private theorem UpperTheory.Reformulated.B.Qh61.exists_den {M : Type} [AddCommGroup M] (x : TensorProduct ℤ ℚ M) :
    ∃ k : ℕ, 0 < k ∧ ∃ a : M, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | tmul q m =>
    refine ⟨q.den, q.den_pos, q.num • m, ?_⟩
    have h : q.den • q = q.num • (1 : ℚ) := by
      rw [nsmul_eq_mul, zsmul_eq_mul, mul_one, mul_comm, Rat.mul_den_eq_num]
    rw [TensorProduct.smul_tmul', h, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨k, hk, a, ha⟩ := hx
    obtain ⟨l, hl, b, hb⟩ := hy
    refine ⟨k * l, Nat.mul_pos hk hl, l • a + k • b, ?_⟩
    have e : ∀ (n : ℕ) (c : M), (1 : ℚ) ⊗ₜ[ℤ] (n • c) = n • ((1 : ℚ) ⊗ₜ[ℤ] c) := fun n c =>
      map_nsmul (TensorProduct.mk ℤ ℚ M 1) n c
    rw [TensorProduct.tmul_add, e, e, ← ha, ← hb, smul_add, smul_smul, smul_smul, mul_comm l k]

/- English proof (translation)
Use `choose d hd a ha using fun x : TensorProduct ℤ ℚ M => UpperTheory.Reformulated.B.Qh61.exists_den x`. Use `⟨∏ x ∈ s, d x, Finset.prod_pos fun x _ => hd x, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem d hx`. Use `⟨c • a x, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, mul_comm, mul_smul, ha]`.

Conclude with `(map_nsmul (TensorProduct.mk ℤ ℚ M 1) c (a x)).symm`.
-/
private theorem UpperTheory.Reformulated.B.Qh61.exists_denominator_rational_tensor {M : Type} [AddCommGroup M]
    (s : Finset (TensorProduct ℤ ℚ M)) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ s, ∃ a : M, k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  classical
  choose d hd a ha using fun x : TensorProduct ℤ ℚ M => UpperTheory.Reformulated.B.Qh61.exists_den x
  refine ⟨∏ x ∈ s, d x, Finset.prod_pos fun x _ => hd x, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem d hx
  refine ⟨c • a x, ?_⟩
  rw [hc, mul_comm, mul_smul, ha]
  exact (map_nsmul (TensorProduct.mk ℤ ℚ M 1) c (a x)).symm

/- English proof (translation)
Introduce `p _ D s`. Conclude with `UpperTheory.Reformulated.B.Qh61.exists_denominator_rational_tensor s`.
-/
theorem UpperTheory.Reformulated.B.Qh61.exists_den_finset :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (D : GlobalTheory.UPel.HT.Datum p) (s : Finset (UpperTheory.Reformulated.B.Qh61.VQ D)),
      ∃ (k : ℕ), (0 : ℕ) < k ∧ ∀ x ∈ s, ∃ (a : D.La), k • x = (1 : ℚ) ⊗ₜ[ℤ] a := by
  intro p _ D s
  exact UpperTheory.Reformulated.B.Qh61.exists_denominator_rational_tensor s
