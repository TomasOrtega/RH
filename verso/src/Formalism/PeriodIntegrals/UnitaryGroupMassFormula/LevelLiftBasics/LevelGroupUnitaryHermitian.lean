import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.SplitInvInjective

open Matrix

noncomputable section

namespace PI.QnLevBasicsW

open Formalism.QuantumDeterminants

variable {k i r' : ℕ}

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Establish `h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i` using `by omega`. Establish `h2 : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i` using `by omega`. Simplify using `only [ιLev]`.

Rewrite using `[dif_pos h1, dif_pos h2]`. Apply the tactic sequence `congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega`.
-/
theorem ιLev_apply_in (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (a b : Fin (2 * r' + k + 1))
    (hp : p.val = a.val + i) (hq : q.val = b.val + i) : ιLev k i r' g p q = g a b := by
  have ha := a.isLt
  have hb := b.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  have h2 : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i := by omega
  simp only [ιLev]
  rw [dif_pos h1, dif_pos h2]
  congr 1 <;> apply Fin.ext <;> simp only [Fin.val_mk] <;> omega

/- English proof (translation)
Simplify using `only [ιLev]`. Rewrite using `[dif_neg hp]`.
-/
theorem ιLev_apply_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) :
    ιLev k i r' g p q = if p = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg hp]

/- English proof (translation)
Simplify using `only [ιLev]`. Rewrite using `[dif_pos hp, dif_neg hq]`.
-/
theorem ιLev_apply_in_out (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (p q : Fin (2 * (i + r') + k + 1)) (hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)
    (hq : ¬ (i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i)) : ιLev k i r' g p q = 0 := by
  simp only [ιLev]
  rw [dif_pos hp, dif_neg hq]

/- English proof (translation)
Establish `ha` using `a.isLt`. Establish `h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i` using `by omega`. Simplify using `only [liftVec]`. Rewrite using `[dif_pos h1]`. Use `congr 1`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [Fin.val_mk]`. Use linear arithmetic over natural numbers and integers.
-/
theorem liftVec_apply_in (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (a : Fin (2 * r' + k + 1)) (hp : p.val = a.val + i) : liftVec k i r' v p = v a := by
  have ha := a.isLt
  have h1 : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i := by omega
  simp only [liftVec]
  rw [dif_pos h1]
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk]
  omega

/- English proof (translation)
Simplify using `only [liftVec]`. Rewrite using `[dif_neg hp]`.
-/
theorem liftVec_apply_out (v : Fin (2 * r' + k + 1) → ℂ) (p : Fin (2 * (i + r') + k + 1))
    (hp : ¬ (i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i)) : liftVec k i r' v p = 0 := by
  simp only [liftVec]
  rw [dif_neg hp]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `ha` using `a.isLt`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Rewrite using `[liftVec_apply_in (bvec a) p ⟨p.val - i, by omega⟩ (by simp only [Fin.val_mk]; omega)]`. Simplify using `only [bvec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[liftVec_apply_out _ p hp]`. Simplify using `only [bvec, Pi.single_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`.
-/
theorem bvec_lift (a : Fin (2 * r' + k + 1)) (q : Fin (2 * (i + r') + k + 1)) (hq : q.val = a.val + i) :
    liftVec k i r' (bvec a) = bvec q := by
  funext p
  have ha := a.isLt
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · rw [liftVec_apply_in (bvec a) p ⟨p.val - i, by omega⟩ (by simp only [Fin.val_mk]; omega)]
    simp only [bvec, Pi.single_apply, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [liftVec_apply_out _ p hp]
    simp only [bvec, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/- English proof (translation)
Simplify using `[bvec, Matrix.mulVec, dotProduct, Pi.single_apply]`.
-/
theorem mulVec_bvec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (q p : Fin m) : (M *ᵥ bvec q) p = M p q := by
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

/- English proof (translation)
Distinguish the cases in `hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i`. Establish `hqa : q.val - i < 2 * r' + k + 1` using `by omega`. Establish `e : q.val = (⟨q.val - i, hqa⟩ : Fin (2 * r' + k + 1)).val + i` using `by simp only [Fin.val_mk]; omega`. Rewrite using `[← bvec_lift ⟨q.val - i, hqa⟩ q e, mulVec_lift, h _ e]`. Use function extensionality and compare the values at `p`.

Rewrite using `[mulVec_bvec]`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Rewrite using `[ιLev_apply_in_out g p q hp hq]`. Simplify using `only [bvec, Pi.single_apply]`. Rewrite using `[if_neg]`.

Introduce `e`. Rewrite `hp` using `[e]`. Conclude with `hq hp`. Rewrite using `[ιLev_apply_out g p q hp]`. Simplify using `[bvec, Pi.single_apply]`.
-/
theorem col_fix (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (q : Fin (2 * (i + r') + k + 1))
    (h : ∀ a : Fin (2 * r' + k + 1), q.val = a.val + i → g *ᵥ bvec a = bvec a) :
    ιLev k i r' g *ᵥ bvec q = bvec q := by
  by_cases hq : i ≤ q.val ∧ q.val < 2 * r' + k + 1 + i
  · have hqa : q.val - i < 2 * r' + k + 1 := by omega
    have e : q.val = (⟨q.val - i, hqa⟩ : Fin (2 * r' + k + 1)).val + i := by simp only [Fin.val_mk]; omega
    rw [← bvec_lift ⟨q.val - i, hqa⟩ q e, mulVec_lift, h _ e]
  · funext p
    rw [mulVec_bvec]
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · rw [ιLev_apply_in_out g p q hp hq]
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro e
      rw [e] at hp
      exact hq hp
    · rw [ιLev_apply_out g p q hp]
      simp [bvec, Pi.single_apply]

/- English proof (translation)
Introduce `k i r'`. Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Rewrite using `[ιLev_eq, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]`. Rewrite using `[ιLev_eq, ιLev_eq, ιLev_eq, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules.
-/
theorem level_group_homomorphism : LevHom := by
  intro k i r'
  refine ⟨?_, fun g h => ?_⟩
  · rw [ιLev_eq, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  · rw [ιLev_eq, ιLev_eq, ιLev_eq, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

/- English proof (translation)
Introduce `k i r' g hg`. Establish `hU : gᴴ * Hpk k r' * g = Hpk k r'` using `hg`. Use `show (ιLev k i r' g)ᴴ * Hpk k (i + r') * ιLev k i r' g = Hpk k (i + r')`. Rewrite using `[ιLev_eq, Hpk_eq, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `[hU]`.
-/
theorem level_group_unitary_hermitian : LevUH := by
  intro k i r' g hg
  have hU : gᴴ * Hpk k r' * g = Hpk k r' := hg
  show (ιLev k i r' g)ᴴ * Hpk k (i + r') * ιLev k i r' g = Hpk k (i + r')
  rw [ιLev_eq, Hpk_eq, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hU]

/- English proof (translation)
Introduce `k i r' g hg`. Simplify using `only [Nset, Set.mem_setOf_eq] at hg ⊢`. Take `⟨hU, h2, h3⟩` from `hg`. Use `⟨level_group_unitary_hermitian k i r' g hU, ?_, ?_⟩` and prove the remaining obligations. Introduce `a p hap`.

Establish `ha` using `a.isLt`. Distinguish the cases in `hai : i ≤ a.val`. Establish `hbr : a.val - i < r'` using `by omega`. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Establish `hpl : p.val - i < 2 * r' + k + 1` using `by omega`.

Rewrite using `[ιLev_apply_in g p (eI k (i + r') a) ⟨p.val - i, hpl⟩ (eI k r' ⟨a.val - i, hbr⟩) (by simp only [Fin.val_mk]; omega) (by simp only [eI, Fin.val_mk]; omega)]`. Rewrite using `[h2 ⟨a.val - i, hbr⟩ ⟨p.val - i, hpl⟩ (by simp only [Fin.val_mk]; omega)]`. Simplify using `only [Fin.ext_iff, eI, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[ιLev_apply_out g p _ hp]`.

Establish `hq : ¬ (i ≤ (eI k (i + r') a).val ∧ (eI k (i + r') a).val < 2 * r' + k + 1 + i)`. Simplify using `only [eI, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Rewrite using `[ιLev_apply_in_out g p _ hp hq]`.

Simplify using `only [Fin.ext_iff, eI, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[ιLev_apply_out g p _ hp]`. Introduce `p q hq1 hq2 hp1`. Establish `hql : q.val - i < 2 * r' + k + 1` using `by omega`.

Distinguish the cases in `hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`. Establish `hpl : p.val - i < 2 * r' + k + 1` using `by omega`. Rewrite using `[ιLev_apply_in g p q ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]`. Rewrite using `[h3 ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)]`. Simplify using `only [Fin.ext_iff, Fin.val_mk]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (exfalso; omega)`. Rewrite using `[ιLev_apply_out g p q hp]`.
-/
theorem level_group_nilpotent : LevN := by
  intro k i r' g hg
  simp only [Nset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, h2, h3⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, ?_, ?_⟩
  · intro a p hap
    have ha := a.isLt
    by_cases hai : i ≤ a.val
    · have hbr : a.val - i < r' := by omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · have hpl : p.val - i < 2 * r' + k + 1 := by omega
        rw [ιLev_apply_in g p (eI k (i + r') a) ⟨p.val - i, hpl⟩ (eI k r' ⟨a.val - i, hbr⟩)
          (by simp only [Fin.val_mk]; omega) (by simp only [eI, Fin.val_mk]; omega)]
        rw [h2 ⟨a.val - i, hbr⟩ ⟨p.val - i, hpl⟩ (by simp only [Fin.val_mk]; omega)]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
    · have hq : ¬ (i ≤ (eI k (i + r') a).val ∧ (eI k (i + r') a).val < 2 * r' + k + 1 + i) := by
        simp only [eI, Fin.val_mk]; omega
      by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
      · rw [ιLev_apply_in_out g p _ hp hq]
        simp only [Fin.ext_iff, eI, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega)
      · rw [ιLev_apply_out g p _ hp]
  · intro p q hq1 hq2 hp1
    have hql : q.val - i < 2 * r' + k + 1 := by omega
    by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have hpl : p.val - i < 2 * r' + k + 1 := by omega
      rw [ιLev_apply_in g p q ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      rw [h3 ⟨p.val - i, hpl⟩ ⟨q.val - i, hql⟩ (by simp only [Fin.val_mk]; omega) (by simp only [Fin.val_mk]; omega)
        (by simp only [Fin.val_mk]; omega)]
      simp only [Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega)
    · rw [ιLev_apply_out g p q hp]

/- English proof (translation)
Introduce `k i r' z g hg`. Simplify using `only [UWset, Set.mem_setOf_eq] at hg ⊢`. Take `⟨hU, hfix, hz⟩` from `hg`. Use `⟨level_group_unitary_hermitian k i r' g hU, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `col_fix` to reduce the goal to its premises.

Introduce `b hb`. Establish `ha` using `a.isLt`. Establish `hbr : b.val < r'` using `by simp only [eI, Fin.val_mk] at hb; omega`. Establish `e : b = eI k r' ⟨b.val, hbr⟩` using `Fin.ext rfl`. Rewrite using `[e]`.

Conclude with `(hfix ⟨b.val, hbr⟩).1`. Apply `col_fix` to reduce the goal to its premises. Introduce `b hb`. Establish `ha` using `a.isLt`. Establish `hb'` using `b.isLt`.

Establish `hai : i ≤ a.val` using `by simp only [esI, Fin.val_mk] at hb; omega`. Establish `hcr : a.val - i < r'` using `by omega`. Establish `e : b = esI k r' ⟨a.val - i, hcr⟩`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [esI, Fin.val_mk] at hb ⊢`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e]`. Conclude with `(hfix ⟨a.val - i, hcr⟩).2`. Rewrite using `[mulVec_lift, hz]`.
-/
theorem level_group_unitary_weyl : LevUW := by
  intro k i r' z g hg
  simp only [UWset, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix, hz⟩ := hg
  refine ⟨level_group_unitary_hermitian k i r' g hU, fun a => ⟨?_, ?_⟩, ?_⟩
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hbr : b.val < r' := by simp only [eI, Fin.val_mk] at hb; omega
    have e : b = eI k r' ⟨b.val, hbr⟩ := Fin.ext rfl
    rw [e]
    exact (hfix ⟨b.val, hbr⟩).1
  · apply col_fix
    intro b hb
    have ha := a.isLt
    have hb' := b.isLt
    have hai : i ≤ a.val := by simp only [esI, Fin.val_mk] at hb; omega
    have hcr : a.val - i < r' := by omega
    have e : b = esI k r' ⟨a.val - i, hcr⟩ := by
      apply Fin.ext
      simp only [esI, Fin.val_mk] at hb ⊢
      omega
    rw [e]
    exact (hfix ⟨a.val - i, hcr⟩).2
  · rw [mulVec_lift, hz]

/- English proof (translation)
Introduce `k i r' z hz`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `inWb at hz ⊢`. Introduce `p hp`. Distinguish the cases in `hb : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i`.

Establish `ha : p.val - i < 2 * r' + k + 1` using `by omega`. Rewrite using `[liftVec_apply_in z p ⟨p.val - i, ha⟩ (by simp only [Fin.val_mk]; omega)]`. Conclude with `hz _ (by simp only [Fin.val_mk]; omega)`. Conclude with `liftVec_apply_out z p hb`. Unfold `Tz`.

Rewrite using `[herm_lift]`.
-/
theorem level_group_isotropic_vector : LevWb := by
  intro k i r' z hz
  refine ⟨?_, ?_⟩
  · unfold inWb at hz ⊢
    intro p hp
    by_cases hb : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
    · have ha : p.val - i < 2 * r' + k + 1 := by omega
      rw [liftVec_apply_in z p ⟨p.val - i, ha⟩ (by simp only [Fin.val_mk]; omega)]
      exact hz _ (by simp only [Fin.val_mk]; omega)
    · exact liftVec_apply_out z p hb
  · unfold Tz
    rw [herm_lift]

/- English proof (translation)
Introduce `k i r' z g`. Unfold `ell`. Rewrite using `[Fin.sum_univ_add]`. Use `Eq.trans (congrArg (· + _) (Finset.sum_eq_zero ?_)) ?_` and prove the remaining obligations. Introduce `a _`.

Establish `ha` using `a.isLt`. Establish `hp : ¬ (i ≤ (eI k (i + r') (Fin.castAdd r' a)).val ∧ (eI k (i + r') (Fin.castAdd r' a)).val < 2 * r' + k + 1 + i)`. Simplify using `only [eI, Fin.val_mk, Fin.coe_castAdd]`. Use linear arithmetic over natural numbers and integers. Use `split_ifs with h`.

Rewrite using `[ιLev_apply_out g _ _ hp, if_neg]`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `only [eI, Fin.val_mk, Fin.coe_castAdd] at this`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[mulVec_lift, liftVec_apply_out _ _ hp]`. Rewrite using `[zero_add]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `b _`. Establish `hb` using `b.isLt`.

Use `split_ifs with h1 h2 h3`. Apply the tactic sequence `apply ιLev_apply_in <;> simp only [eI, Fin.val_mk, Fin.coe_natAdd] <;> omega`. It suffices to derive a contradiction. Simplify using `only [Fin.coe_natAdd] at h1`. Use linear arithmetic over natural numbers and integers.

It suffices to derive a contradiction. Simplify using `only [Fin.coe_natAdd] at h1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mulVec_lift]`. Apply `liftVec_apply_in` to reduce the goal to its premises.

Simplify using `only [eI, Fin.val_mk, Fin.coe_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem level_group_ellipticity : LevEll := by
  intro k i r' z g
  unfold ell
  rw [Fin.sum_univ_add]
  refine Eq.trans (congrArg (· + _) (Finset.sum_eq_zero ?_)) ?_
  · intro a _
    have ha := a.isLt
    have hp : ¬ (i ≤ (eI k (i + r') (Fin.castAdd r' a)).val ∧
        (eI k (i + r') (Fin.castAdd r' a)).val < 2 * r' + k + 1 + i) := by
      simp only [eI, Fin.val_mk, Fin.coe_castAdd]; omega
    split_ifs with h
    · rw [ιLev_apply_out g _ _ hp, if_neg]
      intro e
      have := congrArg Fin.val e
      simp only [eI, Fin.val_mk, Fin.coe_castAdd] at this
      omega
    · rw [mulVec_lift, liftVec_apply_out _ _ hp]
  · rw [zero_add]
    apply Finset.sum_congr rfl
    intro b _
    have hb := b.isLt
    split_ifs with h1 h2 h3
    · apply ιLev_apply_in <;> simp only [eI, Fin.val_mk, Fin.coe_natAdd] <;> omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · exfalso
      simp only [Fin.coe_natAdd] at h1
      omega
    · rw [mulVec_lift]
      apply liftVec_apply_in
      simp only [eI, Fin.val_mk, Fin.coe_natAdd]
      omega

/- English proof (translation)
Assemble the required witnesses or components as `⟨level_group_homomorphism, level_group_unitary_hermitian, level_group_nilpotent, level_group_unitary_weyl, level_group_isotropic_vector, level_group_ellipticity⟩`.
-/
theorem qnLevBasics_main :
    LevHom ∧ LevUH ∧ LevN ∧ LevUW ∧ LevWb ∧ LevEll :=
  ⟨level_group_homomorphism, level_group_unitary_hermitian, level_group_nilpotent, level_group_unitary_weyl, level_group_isotropic_vector, level_group_ellipticity⟩

end PI.QnLevBasicsW
