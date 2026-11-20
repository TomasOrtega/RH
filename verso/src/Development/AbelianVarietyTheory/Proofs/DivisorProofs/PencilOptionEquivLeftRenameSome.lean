import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C r => simp [MvPolynomial.optionEquivLeft_C]`. Consider the case `add p q hp hq => simp [map_add, hp, hq]`. Consider the case `mul_X p x hp => simp [map_mul, hp, MvPolynomial.optionEquivLeft_X_some]`.
-/
theorem pencil_optionEquivLeft_rename_some {τ : Type} (a : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.rename some a) = Polynomial.C a := by
  induction a using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.optionEquivLeft_C]
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p x hp => simp [map_mul, hp, MvPolynomial.optionEquivLeft_X_some]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Polynomial.natDegree_sum_le_of_forall_le _ _ ?_` and prove the remaining obligations. Introduce `g _`. Combine the equalities or inequalities in the displayed calculation. Break down `Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg` into its components or cases.

Rewrite using `[sg, one_smul]`. Rewrite using `[sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]`. Use `_ ≤ ∑ i, (M (g i) i).natDegree := Polynomial.natDegree_prod_le _ _`. Use `_ ≤ ∑ i, d (g i) := Finset.sum_le_sum fun i _ => h _ _`. Use `_ = ∑ i, d i := Equiv.sum_comp g d`.
-/
theorem pencil_natDegree_det_le_rowSum {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (Polynomial R)) (d : ι → ℕ) (h : ∀ i j, (M i j).natDegree ≤ d i) :
    M.det.natDegree ≤ ∑ i, d i := by
  rw [Matrix.det_apply]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro g _
  calc (Equiv.Perm.sign g • ∏ i, M (g i) i).natDegree ≤ (∏ i, M (g i) i).natDegree := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign g) with sg | sg
        · rw [sg, one_smul]
        · rw [sg, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i, (M (g i) i).natDegree := Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ i, d (g i) := Finset.sum_le_sum fun i _ => h _ _
    _ = ∑ i, d i := Equiv.sum_comp g d

/- English proof (translation)
Simplify using `[map_add, map_mul, MvPolynomial.optionEquivLeft_X_none, pencil_optionEquivLeft_rename_some]`.
-/
theorem pencil_map_entry {τ : Type} (a b : MvPolynomial τ ℂ) :
    MvPolynomial.optionEquivLeft ℂ τ
      (MvPolynomial.X none * MvPolynomial.rename some a + MvPolynomial.rename some b) =
      Polynomial.X * Polynomial.C a + Polynomial.C b := by
  simp [map_add, map_mul, MvPolynomial.optionEquivLeft_X_none, pencil_optionEquivLeft_rename_some]

/- English proof (translation)
Introduce `τ ι _ _ A B Z`. Use `set e : MvPolynomial (Option τ) ℂ →+* Polynomial (MvPolynomial τ ℂ) := (MvPolynomial.optionEquivLeft ℂ τ).toRingEquiv.toRingHom with he`. Establish `hZ : e.mapMatrix Z = (Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Z, he]`.

Apply the tactic sequence `exact pencil_map_entry (A i j) (B i j)`. Establish `hdet : MvPolynomial.optionEquivLeft ℂ τ Z.det = ((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).det`. Rewrite using `[← hZ, ← RingHom.map_det]`. Both sides reduce to the same expression. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `k hk`. Rewrite using `[hdet]`. Conclude with `Polynomial.coeff_eq_zero_of_natDegree_lt ((Polynomial.natDegree_det_X_add_C_le A B).trans_lt hk)`. Rewrite using `[hdet, Polynomial.coeff_det_X_add_C_card]`. Introduce `k i j hk`.

Establish `hadj : MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i) = (((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).updateRow i (Pi.single j 1)).det`. Use `congrFun (congrFun (RingHom.map_adjugate e Z) j) i` as an intermediate fact. Rewrite `this` using `[RingHom.mapMatrix_apply, Matrix.map_apply]`. Express the relevant statement in the definitionally equal form `e (Z.adjugate j i) = _`. Rewrite using `[this, hZ, Matrix.adjugate_apply]`.

Rewrite using `[hadj]`. Apply `Polynomial.coeff_eq_zero_of_natDegree_lt` to reduce the goal to its premises. Establish `hcard : 0 < Fintype.card ι` using `Fintype.card_pos_iff.mpr ⟨i⟩`. Use `lt_of_le_of_lt (pencil_natDegree_det_le_rowSum _ (fun r => if r = i then 0 else 1) ?_) ?_` and prove the remaining obligations. Introduce `r c`.

Distinguish the cases in `hr : r = i`. Substitute `hr` using the available equality. Simplify using `only [Matrix.updateRow_self, if_true]`. Distinguish the cases in `hc : c = j`. Substitute `hc` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hc]`. Simplify using `only [Matrix.updateRow_ne hr, if_neg hr, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul] compute_degree`. Establish `: (∑ r, if r = i then 0 else 1 : ℕ) = Fintype.card ι - 1`. Rewrite using `[Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one, Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem pencil_det_adjugate_coeff :
    ∀ {τ : Type} {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι (MvPolynomial τ ℂ)),
      let Z : Matrix ι ι (MvPolynomial (Option τ) ℂ) := fun i j =>
        MvPolynomial.X none * MvPolynomial.rename some (A i j) + MvPolynomial.rename some (B i j);
      (∀ k, Fintype.card ι < k → (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff k = 0) ∧
      (MvPolynomial.optionEquivLeft ℂ τ (Z.det)).coeff (Fintype.card ι) = A.det ∧
      ∀ k i j, Fintype.card ι ≤ k →
        (MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i)).coeff k = 0 := by
  intro τ ι _ _ A B Z
  set e : MvPolynomial (Option τ) ℂ →+* Polynomial (MvPolynomial τ ℂ) :=
    (MvPolynomial.optionEquivLeft ℂ τ).toRingEquiv.toRingHom with he
  have hZ : e.mapMatrix Z = (Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
      B.map Polynomial.C := by
    refine Matrix.ext fun i j => ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Z, he]
    exact pencil_map_entry (A i j) (B i j)
  have hdet : MvPolynomial.optionEquivLeft ℂ τ Z.det =
      ((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C + B.map Polynomial.C).det := by
    rw [← hZ, ← RingHom.map_det]; rfl
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [hdet]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt
      ((Polynomial.natDegree_det_X_add_C_le A B).trans_lt hk)
  · rw [hdet, Polynomial.coeff_det_X_add_C_card]
  · intro k i j hk
    have hadj : MvPolynomial.optionEquivLeft ℂ τ (Z.adjugate j i) =
        (((Polynomial.X : Polynomial (MvPolynomial τ ℂ)) • A.map Polynomial.C +
          B.map Polynomial.C).updateRow i (Pi.single j 1)).det := by
      have := congrFun (congrFun (RingHom.map_adjugate e Z) j) i
      rw [RingHom.mapMatrix_apply, Matrix.map_apply] at this
      change e (Z.adjugate j i) = _
      rw [this, hZ, Matrix.adjugate_apply]
    rw [hadj]
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hcard : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    refine lt_of_le_of_lt (pencil_natDegree_det_le_rowSum _ (fun r => if r = i then 0 else 1) ?_) ?_
    · intro r c
      by_cases hr : r = i
      · subst hr
        simp only [Matrix.updateRow_self, if_true]
        by_cases hc : c = j
        · subst hc; simp
        · simp [Pi.single_apply, hc]
      · simp only [Matrix.updateRow_ne hr, if_neg hr, Matrix.add_apply, Matrix.smul_apply,
          Matrix.map_apply, smul_eq_mul]
        compute_degree
    · have : (∑ r, if r = i then 0 else 1 : ℕ) = Fintype.card ι - 1 := by
        rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul, mul_one,
          Finset.filter_ne' , Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      omega

end GlobalTheory
