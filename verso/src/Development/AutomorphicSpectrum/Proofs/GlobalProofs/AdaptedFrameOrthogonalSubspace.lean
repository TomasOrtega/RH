import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.MidConj

/- English proof (translation)
Simplify using `[Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_ite, ite_mul]`.
-/
theorem mul_single_one_mul_apply {l m o s : Type*} [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq o]
    (A : Matrix l m ℂ) (C : Matrix o s ℂ) (x : m) (y : o) (i : l) (k : s) :
    (A * Matrix.single x y (1 : ℂ) * C) i k = A i x * C y k := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, mul_ite, ite_mul]

/- English proof (translation)
Establish `hPP : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hP`. Set `Pm : Matrix (Fin n) (Fin n') ℂ` to `fun i s => P i ⟨a + s.val, by omega⟩`. Establish `hJm : J = Pm * B`. Use extensionality with `i j`. Rewrite using `[hJ i j]`.

Both sides reduce to the same expression. Establish `hmid : Jp * Pm = Bi`. Combine the equalities or inequalities in the displayed calculation. Establish `hN_mid : ∀ (q : Fin n') (s : Fin n'), (Jp * P) q ⟨a + s.val, by omega⟩ = Bi q s`. Introduce `q s`.

Combine the equalities or inequalities in the displayed calculation. Establish `hN_out : ∀ (q : Fin n') (b : Fin n), (b.val < a ∨ n ≤ b.val + a) → (Jp * P) q b = 0`. Introduce `q b hb`. Establish `h` using `congrFun (hout b hb) q`. Simplify `h` using `[Matrix.mulVec, dotProduct, Matrix.mul_apply]`.

Establish `hJp : ∀ (q : Fin n') (k : Fin n), Jp q k = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k`. Introduce `q k`. Combine the equalities or inequalities in the displayed calculation. Use `symm`. Use `Fintype.sum_of_injective (fun u : Fin n' => (⟨a + u.val, by omega⟩ : Fin n)) ?_ _ _ ?_ ?_` and prove the remaining obligations.

Introduce `u v huv`. Simplify using `only [Fin.mk.injEq] at huv`. Conclude with `Fin.ext (by omega)`. Introduce `b hb`. Establish `hb' : b.val < a ∨ n ≤ b.val + a`.

Assume the negation of the conclusion as `hc`. Simplify using `only [not_or, not_lt] at hc`. Conclude with `hb (Set.mem_range.mpr ⟨⟨b.val - a, by omega⟩, Fin.ext (show a + (b.val - a) = b.val by omega)⟩)`. Rewrite using `[hN_out q b hb', zero_mul]`. Introduce `u`.

Rewrite using `[hN_mid q u]`. Use extensionality with `i k`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_single_one_mul_apply]`. Rewrite using `[hJ i p, hJp q k, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun u _ => ?_))` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_units_of_mid (n n' a : ℕ) (hdim : a + n' + a = n) (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P.det)
    (J : Matrix (Fin n) (Fin n') ℂ) (Jp : Matrix (Fin n') (Fin n) ℂ) (B Bi : Matrix (Fin n') (Fin n') ℂ)
    (hJJ : Jp * J = 1) (hBB : B * Bi = 1)
    (hJ : ∀ (i : Fin n) (j : Fin n'), J i j = ∑ r : Fin n', P i (⟨a + r.val, by omega⟩ : Fin n) * B r j)
    (hout : ∀ b : Fin n, (b.val < a ∨ n ≤ b.val + a) → Jp *ᵥ (fun k => P k b) = 0)
    (p q : Fin n') :
    J * Matrix.single p q (1 : ℂ) * Jp = ∑ r : Fin n', ∑ u : Fin n', (B r p * Bi q u) •
      (P * Matrix.single (⟨a + r.val, by omega⟩ : Fin n) (⟨a + u.val, by omega⟩ : Fin n) (1 : ℂ) * P⁻¹) := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  let Pm : Matrix (Fin n) (Fin n') ℂ := fun i s => P i ⟨a + s.val, by omega⟩
  have hJm : J = Pm * B := by
    ext i j
    rw [hJ i j]
    rfl
  have hmid : Jp * Pm = Bi := by
    calc Jp * Pm = Jp * Pm * (B * Bi) := by rw [hBB, Matrix.mul_one]
      _ = (Jp * J) * Bi := by rw [hJm]; simp only [Matrix.mul_assoc]
      _ = Bi := by rw [hJJ, Matrix.one_mul]
  have hN_mid : ∀ (q : Fin n') (s : Fin n'), (Jp * P) q ⟨a + s.val, by omega⟩ = Bi q s := by
    intro q s
    calc (Jp * P) q ⟨a + s.val, by omega⟩ = (Jp * Pm) q s := rfl
      _ = Bi q s := by rw [hmid]
  have hN_out : ∀ (q : Fin n') (b : Fin n), (b.val < a ∨ n ≤ b.val + a) → (Jp * P) q b = 0 := by
    intro q b hb
    have h := congrFun (hout b hb) q
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using h
  have hJp : ∀ (q : Fin n') (k : Fin n),
      Jp q k = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
    intro q k
    calc Jp q k = ((Jp * P) * P⁻¹) q k := by rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
      _ = ∑ b : Fin n, (Jp * P) q b * P⁻¹ b k := by rw [Matrix.mul_apply]
      _ = ∑ u : Fin n', Bi q u * P⁻¹ ⟨a + u.val, by omega⟩ k := by
        symm
        refine Fintype.sum_of_injective (fun u : Fin n' => (⟨a + u.val, by omega⟩ : Fin n)) ?_ _ _ ?_ ?_
        · intro u v huv
          simp only [Fin.mk.injEq] at huv
          exact Fin.ext (by omega)
        · intro b hb
          have hb' : b.val < a ∨ n ≤ b.val + a := by
            by_contra hc
            simp only [not_or, not_lt] at hc
            exact hb (Set.mem_range.mpr ⟨⟨b.val - a, by omega⟩, Fin.ext (show a + (b.val - a) = b.val by omega)⟩)
          rw [hN_out q b hb', zero_mul]
        · intro u
          rw [hN_mid q u]
  ext i k
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, mul_single_one_mul_apply]
  rw [hJ i p, hJp q k, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun u _ => ?_))
  ring

end GlobalTheory.CompanionTheory.MidConj
