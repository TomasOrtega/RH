import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric.ColSplit

abbrev HiIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // r ≤ (t.1.1 : ℕ)}

abbrev LoIx (a r k : ℕ) : Type := {t : UnipotentBlockColumnIndex a k k // ¬ r ≤ (t.1.1 : ℕ)}

def colEquiv (a r k : ℕ) : HiIx a r k ⊕ LoIx a r k ≃ UnipotentBlockColumnIndex a k k := Equiv.sumCompl _

def blkEquiv (a r m : ℕ) (hr : r ≤ m + 1) : UnipotentBlockColumnIndex a r m ⊕ LoIx a r (m + 1) ≃ UnipotentBlockColumnIndex a r (m + 1) where
  toFun := Sum.elim (fun s : UnipotentBlockColumnIndex a r m => ⟨s.1, s.2.1, s.2.2.1, by have := s.2.2.2; omega⟩)
    (fun l : LoIx a r (m + 1) => ⟨l.1.1, by have := l.2; omega, by have := l.1.2; omega, by have := l.1.2; omega⟩)
  invFun := fun t => if h : (t.1.2 : ℕ) ≤ m then Sum.inl ⟨t.1, t.2.1, t.2.2.1, h⟩
    else Sum.inr ⟨⟨t.1, by have := t.2; omega, by have := t.2; omega, by have := t.2; omega⟩,
      show ¬ r ≤ (t.1.1 : ℕ) by have := t.2; omega⟩
  left_inv := by
    rintro (s | l)
    · simp [s.2.2.2]
    · have h1 := l.1.2
      have h2 : ¬ ((l.1.1.2 : ℕ) ≤ m) := by omega
      simp [h2]
  right_inv := by
    intro t
    by_cases h : (t.1.2 : ℕ) ≤ m
    · simp [h]
    · simp [h]

section Mat

variable {R : Type} [CommRing R] {a : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem posM_apply_ne_zero {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} {x : ι → R} {i k : Fin a}
    (h : posM p x i k ≠ 0) : ∃ t, p t = (i, k) := by
  simp only [posM, Matrix.sum_apply] at h
  obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨t, ?_⟩
  rw [Matrix.single_apply] at ht
  split_ifs at ht with hc
  · exact Prod.ext hc.1 hc.2
  · exact absurd rfl ht

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem posM_eq_of_support {ι : Type} [Fintype ι] {p : ι → Fin a × Fin a} (hp : Function.Injective p)
    (M : Matrix (Fin a) (Fin a) R) (hM : ∀ i k, M i k ≠ 0 → ∃ t, p t = (i, k)) :
    posM p (fun t => M (p t).1 (p t).2) = M := by
  ext i k
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases h : ∃ t, p t = (i, k)
  · obtain ⟨t, ht⟩ := h
    rw [Finset.sum_eq_single t]
    · simp [ht]
    · intro t' _ ht'
      rw [if_neg]
      rintro ⟨e1, e2⟩
      exact ht' (hp (by rw [ht]; exact Prod.ext e1 e2))
    · simp
  · have h0 : M i k = 0 := by
      by_contra h1
      exact h (hM i k h1)
    rw [h0]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg]
    rintro ⟨e1, e2⟩
    exact h ⟨t, Prod.ext e1 e2⟩

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem posM_comp_symm {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι → Fin a × Fin a) (τ : κ ≃ ι) (w : κ → R) :
    posM p (w ∘ τ.symm) = posM (p ∘ τ) w := by
  simp only [posM]
  exact (Fintype.sum_equiv τ.symm _ _ (fun t => by simp)).trans rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem posM_sumElim {ι κ : Type} [Fintype ι] [Fintype κ] (p : ι ⊕ κ → Fin a × Fin a) (z : ι → R) (y : κ → R) :
    posM p (Sum.elim z y) = posM (p ∘ Sum.inl) z + posM (p ∘ Sum.inr) y := by
  simp only [posM, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem posM_sub {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) (x y : ι → R) :
    posM p (x - y) = posM p x - posM p y := by
  rw [eq_sub_iff_add_eq, ← posM_add, sub_add_cancel]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem posM_zero' {ι : Type} [Fintype ι] (p : ι → Fin a × Fin a) : posM p (0 : ι → R) = 0 := by
  simp [posM]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem posM_mul_eq_zero {ι κ : Type} [Fintype ι] [Fintype κ] {p : ι → Fin a × Fin a} {q : κ → Fin a × Fin a}
    (h : ∀ s t, (p s).2 ≠ (q t).1) (x : ι → R) (y : κ → R) : posM p x * posM q y = 0 := by
  simp only [posM, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun t _ => ?_
  exact Matrix.single_mul_single_of_ne _ _ _ _ (h _ _) _

def corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) : LoIx a r (m + 1) → R := fun l =>
  (posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z) l.1.1.1 l.1.1.2

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem posM_corr {r m : ℕ} (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R) :
    posM (fun l : LoIx a r (m + 1) => l.1.1) (corr n z) =
      posM Subtype.val n * posM (fun t : HiIx a r (m + 1) => t.1.1) z := by
  refine posM_eq_of_support (fun l l' e => Subtype.ext (Subtype.ext e)) _ fun i k hik => ?_
  obtain ⟨l, hl⟩ : ∃ l, posM Subtype.val n i l * posM (fun t : HiIx a r (m + 1) => t.1.1) z l k ≠ 0 := by
    rw [Matrix.mul_apply] at hik
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero hik
    exact ⟨l, hl⟩
  obtain ⟨s, hs⟩ := posM_apply_ne_zero (left_ne_zero_of_mul hl)
  obtain ⟨t, ht⟩ := posM_apply_ne_zero (right_ne_zero_of_mul hl)
  have s2 := s.2
  have t2 := t.1.2
  rw [hs] at s2
  rw [ht] at t2
  simp only at s2 t2
  exact ⟨⟨⟨(i, k), show (i : ℕ) < m + 1 by omega, show m + 1 ≤ (k : ℕ) by omega, show (k : ℕ) ≤ m + 1 by omega⟩,
    show ¬ r ≤ (i : ℕ) by omega⟩, rfl⟩

end Mat

section Id

variable {R : Type} [CommRing R] {a : ℕ}

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Normalize the expressions using the abelian group laws. A detailed English derivation is pending.
-/
theorem blkU_col_mul_blkU {r m : ℕ} (hr : r ≤ m + 1) (n : UnipotentBlockColumnIndex a r m → R) (z : HiIx a r (m + 1) → R)
    (y : LoIx a r (m + 1) → R) :
    blkU (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm) * blkU n =
      blkU (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm) *
        blkU (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm) := by
  apply Units.ext
  change (1 + posM Subtype.val (Sum.elim z y ∘ (colEquiv a r (m + 1)).symm)) * (1 + posM Subtype.val n) =
    (1 + posM Subtype.val (Sum.elim n (y - corr n z) ∘ (blkEquiv a r m hr).symm)) *
      (1 + posM Subtype.val (Sum.elim z 0 ∘ (colEquiv a r (m + 1)).symm))
  simp only [posM_comp_symm, posM_sumElim, posM_sub, posM_zero', add_zero]
  have e1 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inl) = fun t : HiIx a r (m + 1) => t.1.1 := rfl
  have e2 : ((Subtype.val ∘ colEquiv a r (m + 1)) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  have e3 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inl) = (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) := rfl
  have e4 : ((Subtype.val ∘ blkEquiv a r m hr) ∘ Sum.inr) = fun t : LoIx a r (m + 1) => t.1.1 := rfl
  rw [e1, e2, e3, e4, posM_corr]
  set P := posM (fun t : HiIx a r (m + 1) => t.1.1) z
  set Q := posM (fun t : LoIx a r (m + 1) => t.1.1) y
  set N := posM (Subtype.val : UnipotentBlockColumnIndex a r m → Fin a × Fin a) n
  have hPN : P * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQN : Q * N = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.2; omega) _ _
  have hQP : Q * P = 0 := posM_mul_eq_zero (fun s t => by
    have := s.1.2; have := t.1.2; omega) _ _
  have hNPP : N * P * P = 0 := by
    rw [mul_assoc, posM_mul_eq_zero (fun s t => by have := s.1.2; have := t.1.2; omega) z z, mul_zero]
  simp only [mul_add, add_mul, mul_one, one_mul, mul_sub, sub_mul, hPN, hQN, hQP, hNPP]
  abel

end Id

end GlobalTheory.CuspGeneric.ColSplit
