import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.SkipOneEqSuccAbove
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BorderMinorRotation.SkipTwoSuccAboveComp

namespace PI

/- English proof (translation)
Substitute `hk` using the available equality. Establish `hf : f = g` using `funext fun i => by simpa using hfg i`. Substitute `hf` using the available equality. Use function extensionality and compare the values at `i`. Simplify using `[bS]`.
-/
private theorem snoc_comp_cast_eq_bS_of_eq {n k t : ℕ} (hk : k = t) (h : t + 1 = k + 1) (f : Fin k → Fin n)
    (g : Fin t → Fin n) (es : Fin n) (hfg : ∀ i : Fin k, f i = g (Fin.cast hk i)) :
    (Fin.snoc f es ∘ Fin.cast h : Fin (t + 1) → Fin n) = bS g es := by
  subst hk
  have hf : f = g := funext fun i => by simpa using hfg i
  subst hf
  funext i
  simp [bS]

/- English proof (translation)
Introduce `A _ _ n m E e es v hG hB u w`. Take `⟨t, rfl⟩ : ∃ t, m = t + 1` from `⟨m - 1, by have := w.pos; omega⟩`. Establish `hexp` using `hLC A n (t + 1) E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bS v es) (u - 1)`. Establish `hb1 : bS v es ∘ Fin.castSucc = v`. Use function extensionality and compare the values at `i`.

Simplify using `[bS]`. Establish `hb2 : bS v es (Fin.last (t + 1)) = es` using `by simp [bS]`. Rewrite `hexp` using `[Fin.sum_univ_succ, Fin.sum_univ_castSucc]`. Use `beta_reduce at hexp`. Rewrite `hexp` using `[hb1, hb2, Fin.succ_last, hX A n t E e es v hG hB u w, UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp]`.

Simplify using `only [Nat.succ_eq_add_one] at hexp`. Establish `e1 : bE e (bS (v ∘ w.succAbove) es) ∘ Fin.succ = bS (v ∘ w.succAbove) es`. Use function extensionality and compare the values at `i`. Simplify using `[bE]`. Establish `e2 : bE e (bS (v ∘ w.succAbove) es) 0 = e` using `by simp [bE]`.

Establish `e3 : bE e (bS (v ∘ w.succAbove) es) (Fin.last (t + 1)) = es`. Rewrite using `[← Fin.succ_last]`. Simplify using `[bE, bS]`. Establish `hees : e ≠ es` using `hB.2.1`. Rewrite `hexp` using `[Fin.succAbove_zero, e1, e2, e3, UnitaryGroupMassFormula.QmBorderFull.bL_last, UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E _ hees, UnitaryGroupMassFormula.QmBorderFull.Four.rowPart hLR E hG e (v ∘ w.succAbove) v (fun x => hB.2.2.1 x) (u - 1)]`.

Establish `g1 : bE e (bS v es) ∘ Fin.succ = bS v es`. Use function extensionality and compare the values at `i`. Simplify using `[bE]`. Establish `g2 : bE e (bS v es) 0 = e` using `by simp [bE]`. Establish `hsk : ∀ i : Fin (t + 1), (v ∘ skip1 i : Fin t → Fin n) = v ∘ i.succAbove`.

Introduce `i`. Use function extensionality and compare the values at `j`. Conclude with `congrArg v (hS1 t i j)`. Establish `hu1 : u - 1 - 1 = u - 2` using `by ring`. Establish `hu2 : u - 1 - ((t + 1 : ℕ) : ℂ) = u - ((t + 1 : ℕ) : ℂ) - 1` using `by ring`.

Rewrite using `[UnitaryGroupMassFormula.QmBorderFull.Four.mid_val (t := t + 1) e es v w, g2, UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E u (hB.2.2.1 w), UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp, g1, hexp]`. Rewrite using `[hu1, hu2]`. Simplify using `only [hsk, Fin.val_succ, Fin.coe_castSucc, Fin.val_zero, Fin.val_last]`. Rewrite using `[snoc_comp_cast_eq_bS_of_eq (k := t + 1 - 1) (t := t) rfl _ (v ∘ w.succAbove) (v ∘ w.succAbove) es (fun _ => rfl)]`. Establish `hT : ∀ x : Fin (t + 1), E e (v x) * Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es = Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es * E e (v x)` using `fun x => (UnitaryGroupMassFormula.QmBorderFull.tm_comm_E E hG _ es e (v x) hees.symm (hB.2.2.2 x)).symm`.

Use `clear hexp hb1 hb2 e1 e2 e3 g1 g2 hu1 hu2 hX hLC hLR hS1 hsk`. Simplify using `only [UnitaryGroupMassFormula.QmBorderFull.Four.zmul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_add, Finset.mul_sum, Finset.smul_sum, Finset.sum_mul, mul_ite, mul_zero, smul_ite, smul_zero, mul_assoc, hT]`. Establish `k1 : ((-1 : ℤ) ^ (t + 1 + 0) * (-1) ^ ((w : ℕ) + 1)) = (-1) ^ ((w : ℕ) + 1 + (t + 1))` using `by ring`. Establish `k2 : ∀ a b : ℤ, a * (b * ((-1) ^ (w : ℕ) * (-1) ^ ((w : ℕ) + 1))) = -(a * b)`. Introduce `a b`.

Establish `hw : ((-1 : ℤ) ^ (w : ℕ)) * (-1) ^ ((w : ℕ) + 1) = -1`. Rewrite using `[pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions. Rewrite using `[hw]`. Expand and normalize the polynomial expressions, which then agree.

Establish `k3 : ∀ x : ℕ, (-1 : ℤ) ^ x * ((-1) ^ (t + 1 + (t + 1)) * (-1) ^ ((w : ℕ) + 1)) = -(-1) ^ ((w : ℕ) + x)`. Introduce `x`. Establish `: ((-1 : ℤ) ^ (t + 1 + (t + 1))) = 1`. Rewrite using `[← two_mul, pow_mul]`. Evaluate the numerical expressions.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `kite : ∀ (c : Prop) [Decidable c] (X : A), (if c then -X else 0) = -(if c then X else 0)`. Introduce `c _ X`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [k1, k2, k3, neg_smul, kite, Finset.sum_neg_distrib]`. Normalize the expressions using the abelian group laws.
-/
private theorem bfMid_of_expLastCol_expLastRow_skipSucc_bfCross (hLC : ExpLastCol) (hLR : ExpLastRow) (hS1 : SkipSucc)
    (hX : UnitaryGroupMassFormula.QmBorderFull.BFCross) : UnitaryGroupMassFormula.QmBorderFull.BFMid := by
  intro A _ _ n m E e es v hG hB u w
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by have := w.pos; omega⟩
  have hexp := hLC A n (t + 1) E (bE e (bS v es) ∘ w.castSucc.succ.succAbove) (bS v es) (u - 1)
  have hb1 : bS v es ∘ Fin.castSucc = v := by
    funext i
    simp [bS]
  have hb2 : bS v es (Fin.last (t + 1)) = es := by simp [bS]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hexp
  beta_reduce at hexp
  rw [hb1, hb2, Fin.succ_last, hX A n t E e es v hG hB u w, UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp] at hexp
  simp only [Nat.succ_eq_add_one] at hexp
  have e1 : bE e (bS (v ∘ w.succAbove) es) ∘ Fin.succ = bS (v ∘ w.succAbove) es := by
    funext i
    simp [bE]
  have e2 : bE e (bS (v ∘ w.succAbove) es) 0 = e := by simp [bE]
  have e3 : bE e (bS (v ∘ w.succAbove) es) (Fin.last (t + 1)) = es := by
    rw [← Fin.succ_last]
    simp [bE, bS]
  have hees : e ≠ es := hB.2.1
  rw [Fin.succAbove_zero, e1, e2, e3, UnitaryGroupMassFormula.QmBorderFull.bL_last,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E _ hees,
    UnitaryGroupMassFormula.QmBorderFull.Four.rowPart hLR E hG e (v ∘ w.succAbove) v (fun x => hB.2.2.1 x) (u - 1)] at hexp
  have g1 : bE e (bS v es) ∘ Fin.succ = bS v es := by
    funext i
    simp [bE]
  have g2 : bE e (bS v es) 0 = e := by simp [bE]
  have hsk : ∀ i : Fin (t + 1), (v ∘ skip1 i : Fin t → Fin n) = v ∘ i.succAbove := by
    intro i
    funext j
    exact congrArg v (hS1 t i j)
  have hu1 : u - 1 - 1 = u - 2 := by ring
  have hu2 : u - 1 - ((t + 1 : ℕ) : ℂ) = u - ((t + 1 : ℕ) : ℂ) - 1 := by ring
  rw [UnitaryGroupMassFormula.QmBorderFull.Four.mid_val (t := t + 1) e es v w, g2,
    UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne E u (hB.2.2.1 w), UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp, g1, hexp]
  rw [hu1, hu2]
  simp only [hsk, Fin.val_succ, Fin.coe_castSucc, Fin.val_zero, Fin.val_last]
  rw [snoc_comp_cast_eq_bS_of_eq (k := t + 1 - 1) (t := t) rfl _ (v ∘ w.succAbove) (v ∘ w.succAbove) es (fun _ => rfl)]
  have hT : ∀ x : Fin (t + 1), E e (v x) * Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es =
      Formalism.REAL.Tm E (u - ↑(t + 1) - 1) es es * E e (v x) := fun x =>
    (UnitaryGroupMassFormula.QmBorderFull.tm_comm_E E hG _ es e (v x) hees.symm (hB.2.2.2 x)).symm
  clear hexp hb1 hb2 e1 e2 e3 g1 g2 hu1 hu2 hX hLC hLR hS1 hsk
  simp only [UnitaryGroupMassFormula.QmBorderFull.Four.zmul, mul_smul_comm, smul_mul_assoc, smul_add, smul_smul, mul_add,
    Finset.mul_sum, Finset.smul_sum, Finset.sum_mul, mul_ite, mul_zero, smul_ite, smul_zero, mul_assoc, hT]
  have k1 : ((-1 : ℤ) ^ (t + 1 + 0) * (-1) ^ ((w : ℕ) + 1)) = (-1) ^ ((w : ℕ) + 1 + (t + 1)) := by ring
  have k2 : ∀ a b : ℤ, a * (b * ((-1) ^ (w : ℕ) * (-1) ^ ((w : ℕ) + 1))) = -(a * b) := by
    intro a b
    have hw : ((-1 : ℤ) ^ (w : ℕ)) * (-1) ^ ((w : ℕ) + 1) = -1 := by
      rw [pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [hw]
    ring
  have k3 : ∀ x : ℕ, (-1 : ℤ) ^ x * ((-1) ^ (t + 1 + (t + 1)) * (-1) ^ ((w : ℕ) + 1)) = -(-1) ^ ((w : ℕ) + x) := by
    intro x
    have : ((-1 : ℤ) ^ (t + 1 + (t + 1))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [this]
    ring
  have kite : ∀ (c : Prop) [Decidable c] (X : A), (if c then -X else 0) = -(if c then X else 0) := by
    intro c _ X
    split_ifs <;> simp
  simp only [k1, k2, k3, neg_smul, kite, Finset.sum_neg_distrib]
  abel

/- English proof (translation)
Take `⟨hE, hS⟩` from `hES`. Take `⟨hFC, hLC⟩` from `hCol`. Take `⟨hFR, hLR⟩` from `hRow`. Take `⟨hS1, hS2⟩` from `hSkip`. Conclude with `UnitaryGroupMassFormula.QmBorderFull.borderFull_of hFC hS (bfMid_of_expLastCol_expLastRow_skipSucc_bfCross hLC hLR hS1 (UnitaryGroupMassFormula.QmBorderFull.Four.bfCross_of ⟨hFR, hLR⟩ ⟨hS1, hS2⟩))`.
-/
theorem qmBorderFull_of (hES : PI.QmBorderES) (hCol : PI.QmColExp) (hRow : PI.QmRowExp) (hSkip : PI.QmSkip) :
    PI.QmBorderFull := by
  obtain ⟨hE, hS⟩ := hES
  obtain ⟨hFC, hLC⟩ := hCol
  obtain ⟨hFR, hLR⟩ := hRow
  obtain ⟨hS1, hS2⟩ := hSkip
  exact UnitaryGroupMassFormula.QmBorderFull.borderFull_of hFC hS
    (bfMid_of_expLastCol_expLastRow_skipSucc_bfCross hLC hLR hS1 (UnitaryGroupMassFormula.QmBorderFull.Four.bfCross_of ⟨hFR, hLR⟩ ⟨hS1, hS2⟩))

end PI
