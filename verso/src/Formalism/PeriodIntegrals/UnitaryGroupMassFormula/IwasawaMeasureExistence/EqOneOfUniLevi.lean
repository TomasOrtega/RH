import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.ParabolicDecomposition

noncomputable section

namespace PI.IwaMeasEx.LP

open Matrix Formalism.L2.S.S7.WittLeviSubgroups PI.IwaMeasEx.PD

section Gen

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  (Fm Fi : Matrix (Fin n) (Fin n) R)

def wc (X : Matrix (Fin n) (Fin n) R) : Matrix ι ι R := (Fi * X * Fm).submatrix e e

def uw (A : Matrix ι ι R) : Matrix (Fin n) (Fin n) R := Fm * A.submatrix e.symm e.symm * Fi

variable {Fm Fi}

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem wc_mul (hFm : Fm * Fi = 1) (X Y : Matrix (Fin n) (Fin n) R) :
    wc e Fm Fi (X * Y) = wc e Fm Fi X * wc e Fm Fi Y := by
  unfold wc
  rw [submatrix_mul_equiv, show Fi * X * Fm * (Fi * Y * Fm) = Fi * X * (Fm * Fi) * Y * Fm by
    simp only [Matrix.mul_assoc], hFm, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem uw_mul (hFi : Fi * Fm = 1) (A B : Matrix ι ι R) :
    uw e Fm Fi (A * B) = uw e Fm Fi A * uw e Fm Fi B := by
  unfold uw
  rw [(submatrix_mul_equiv A B e.symm e.symm e.symm).symm,
    show Fm * A.submatrix e.symm e.symm * Fi * (Fm * B.submatrix e.symm e.symm * Fi) =
      Fm * A.submatrix e.symm e.symm * (Fi * Fm) * B.submatrix e.symm e.symm * Fi by simp only [Matrix.mul_assoc],
    hFi, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem wc_one (hFi : Fi * Fm = 1) : wc e Fm Fi (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  unfold wc
  rw [Matrix.mul_one, hFi, submatrix_one_equiv]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem uw_one (hFm : Fm * Fi = 1) : uw e Fm Fi (1 : Matrix ι ι R) = 1 := by
  unfold uw
  rw [submatrix_one_equiv, Matrix.mul_one, hFm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem blo_of_par (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev) :
    BLo lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R)) := by
  intro s r hl
  have h1 : g ∈ Formalism.UG.stabGL (stepLo (cols e Fm) lev (lev r + 1)) := Subgroup.mem_iInf.1 hg (lev r + 1)
  exact entry_zero hFi {t | lev t < lev r + 1} h1 s r (by simp only [Set.mem_ofPred_eq]; omega)
    (by simp only [Set.mem_ofPred_eq]; omega)

end Gen

section Form

variable {R : Type} [CommRing R] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι ≃ Fin n) (lev : ι → ℕ)
  {Fm Fi : Matrix (Fin n) (Fin n) R}

def ALev (a : ℕ) (W : Matrix ι ι R) : Prop := ∀ q r, W q r ≠ 0 → lev q + lev r = 2 * a

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cT_apply (σ : R →+* R) {m p : Type} (M : Matrix m p R) (i : p) (j : m) :
    Formalism.UG.cT σ M i j = σ (M j i) := rfl

/- English proof (translation)
By extensionality, compare the relevant components. Both sides reduce to the same expression.
-/
theorem cT_submatrix (σ : R →+* R) {m p m' p' : Type} (M : Matrix m p R) (f : m' → m) (g : p' → p) :
    Formalism.UG.cT σ (M.submatrix f g) = (Formalism.UG.cT σ M).submatrix g f := by
  ext i j; rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem tripleS (σ : R →+* R) (A W : Matrix ι ι R) (p q : ι) :
    (Formalism.UG.cT σ A * W * A) p q = ∑ t, ∑ r, σ (A r p) * W r t * A t q := by
  simp only [Matrix.mul_apply, cT_apply, Finset.sum_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem bd_unitaryS (σ : R →+* R) {a : ℕ} {W T : Matrix ι ι R} (hA : ALev lev a W) (hT : BLo lev T)
    (hU : Formalism.UG.cT σ T * W * T = W) : Formalism.UG.cT σ (bd lev T) * W * bd lev T = W := by
  ext p q
  rw [tripleS]
  by_cases hpq : lev p + lev q = 2 * a
  · conv_rhs => rw [← hU, tripleS]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
    by_cases hW : W r t = 0
    · rw [hW, mul_zero, zero_mul, mul_zero, zero_mul]
    have hl := hA r t hW
    simp only [bd]
    by_cases h1 : lev r = lev p
    · rw [if_pos h1, if_pos (show lev t = lev q by omega)]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]
      rcases Nat.lt_or_ge (lev p) (lev r) with h2 | h2
      · rw [hT r p h2, map_zero, zero_mul, zero_mul]
      · rw [hT t q (by omega), mul_zero]
  · have hW : W p q = 0 := by
      by_contra h; exact hpq (hA p q h)
    rw [hW]
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun r _ => ?_
    simp only [bd]
    by_cases h1 : lev r = lev p
    · by_cases h2 : lev t = lev q
      · have hW' : W r t = 0 := by
          by_contra h; have := hA r t h; omega
        rw [hW', mul_zero, zero_mul]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, map_zero, zero_mul, zero_mul]

/- English proof (translation)
Substitute using the available equality. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wc_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (X : Matrix (Fin n) (Fin n) R)
    (hX : Formalism.UG.cT σ X * Jx * X = Jx) : Formalism.UG.cT σ (wc e Fm Fi X) * W * wc e Fm Fi X = W := by
  subst hW
  unfold wc
  rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]
  congr 1
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  calc Formalism.UG.cT σ (Fi * X * Fm) * (Formalism.UG.cT σ Fm * Jx * Fm) * (Fi * X * Fm)
      = Formalism.UG.cT σ Fm * Formalism.UG.cT σ X * (Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm) * Jx * (Fm * Fi) * X * Fm := by
        simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fm * (Formalism.UG.cT σ X * Jx * X) * Fm := by
        rw [e1, hFm]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by rw [hX]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem uw_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) (hFm : Fm * Fi = 1) {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (A : Matrix ι ι R) (hA : Formalism.UG.cT σ A * W * A = W) :
    Formalism.UG.cT σ (uw e Fm Fi A) * Jx * uw e Fm Fi A = Jx := by
  have e1 : Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm = 1 := by rw [← Formalism.UG.cT_mul, hFm, Formalism.UG.cT_one]
  have hG : Formalism.UG.cT σ Fm * Jx * Fm = W.submatrix e.symm e.symm := by
    rw [← hW, submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id]
  have hA' : Formalism.UG.cT σ (A.submatrix e.symm e.symm) * W.submatrix e.symm e.symm * A.submatrix e.symm e.symm =
      W.submatrix e.symm e.symm := by
    rw [cT_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, hA]
  unfold uw
  calc Formalism.UG.cT σ (Fm * A.submatrix e.symm e.symm * Fi) * Jx * (Fm * A.submatrix e.symm e.symm * Fi)
      = Formalism.UG.cT σ Fi * (Formalism.UG.cT σ (A.submatrix e.symm e.symm) * (Formalism.UG.cT σ Fm * Jx * Fm) *
          A.submatrix e.symm e.symm) * Fi := by simp only [Formalism.UG.cT_mul, Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Fi * Formalism.UG.cT σ Fm * Jx * (Fm * Fi) := by
        rw [hG, hA', ← hG]; simp only [Matrix.mul_assoc]
    _ = Jx := by rw [e1, hFm, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem wc_mul_inv (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) * wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, mul_inv_cancel, Units.val_one, wc_one e hFi]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem wc_inv_mul (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) :
    wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * wc e Fm Fi (g : Matrix (Fin n) (Fin n) R) = 1 := by
  rw [← wc_mul e hFm, ← Units.val_mul, inv_mul_cancel, Units.val_one, wc_one e hFi]

def levGL (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) (g : GL (Fin n) R) (hg : g ∈ parGL (cols e Fm) lev) :
    GL (Fin n) R :=
  ⟨uw e Fm Fi (bd lev (wc e Fm Fi (g : Matrix (Fin n) (Fin n) R))),
    uw e Fm Fi (bd lev (wc e Fm Fi ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R))),
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi hg) (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg))
      (wc_mul_inv e hFm hFi g), uw_one e hFm],
    by rw [← uw_mul e hFi, bd_mul lev (blo_of_par e lev hFi ((parGL _ lev).inv_mem hg)) (blo_of_par e lev hFi hg)
      (wc_inv_mul e hFm hFi g), uw_one e hFm]⟩

variable (hFm : Fm * Fi = 1) (hFi : Fi * Fm = 1) {g : GL (Fin n) R} (hg : g ∈ parGL (cols e Fm) lev)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem levGL_unitary (σ : R →+* R) (Jx : Matrix (Fin n) (Fin n) R) {a : ℕ} {W : Matrix ι ι R}
    (hW : (Formalism.UG.cT σ Fm * Jx * Fm).submatrix e e = W) (hA : ALev lev a W) (hgU : g ∈ Formalism.UG.UJ σ Jx) :
    levGL e lev hFm hFi g hg ∈ Formalism.UG.UJ σ Jx :=
  uw_unitary e σ Jx hFm hW _ (bd_unitaryS lev σ hA (blo_of_par e lev hFi hg) (wc_unitary e σ Jx hFm hW _ hgU))

end Form

end PI.IwaMeasEx.LP

end
