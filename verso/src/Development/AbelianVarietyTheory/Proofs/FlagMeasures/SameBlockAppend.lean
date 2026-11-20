import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RowRawRange
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Substitute using the available equality.

Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem ptEntryL_append (bs : List (Eˣ × ℕ+)) (t : Eˣ) (s : ℕ+) :
    ∀ (m : ℕ), (bs.map (fun b => (b.2 : ℕ))).sum = m → ∀ a b : ℕ,
      ptEntryL (bs ++ [(t, s)]) a b =
        if a < m ∧ b < m then ptEntryL bs a b
        else if m ≤ a ∧ m ≤ b ∧ a + b + 1 = 2 * m + s then (t : E) else 0 := by
  induction bs with
  | nil =>
    intro m hm a b
    simp only [List.map_nil, List.sum_nil] at hm
    subst hm
    simp only [List.nil_append, ptEntryL]
    split_ifs <;> first | rfl | omega
  | cons hd bs ih =>
    obtain ⟨t', s'⟩ := hd
    intro m hm a b
    simp only [List.map_cons, List.sum_cons] at hm
    simp only [List.cons_append, ptEntryL]
    rw [ih _ rfl]
    split_ifs <;> first | rfl | omega

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

/- English proof (translation)
Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_snoc_eq {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det =
      h.mat.det * (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s)) : ℤˣ) : ℤ) *
        (t : E) ^ (s : ℕ)) := by
  have key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat =
      Matrix.fromBlocks h.mat 0 0
        ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E) := by
    ext (i | i) (j | j) <;>
      simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc,
        finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.zero_apply, smul_eq_mul] <;>
      have hi := i.isLt <;> have hj := j.isLt
    · rw [dif_pos ⟨hi, hj⟩]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega), if_neg (by omega)]
    · rw [dif_neg (by omega)]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
        Option.mem_def, Option.some.injEq, Fin.revPerm_apply]
      by_cases hij : Fin.rev i = j
      · rw [if_pos (by rw [← hij, Fin.val_rev]; omega), if_pos hij, mul_one]
      · rw [if_neg (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))), if_neg hij, mul_zero]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul,
    Matrix.det_permutation, Fintype.card_fin] at hdet
  rw [hdet]
  ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem det_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) :
    (h.snoc t s).mat.det = h.mat.det * (t : E) ^ (s : ℕ) ∨
      (h.snoc t s).mat.det = -(h.mat.det * (t : E) ^ (s : ℕ)) := by
  rw [det_snoc_eq]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1
  · left
    rw [h1]
    simp
  · right
    rw [h1]
    simp

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality.

Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Substitute using the available equality. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem isUnit_det_of_mem_UH_Hpk (bs : List (Eˣ × ℕ+)) :
    ∀ (n : ℕ) (hn : (bs.map (fun b => (b.2 : ℕ))).sum = n),
      IsUnit (Pt.mat (⟨bs, hn⟩ : Pt E n)).det := by
  induction bs using List.reverseRecOn with
  | nil =>
    intro n hn
    have hn' : n = 0 := by rw [← hn]; simp
    subst hn'
    simp
  | append_singleton bs x ih =>
    obtain ⟨t, s⟩ := x
    intro n hn
    have hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s := by rw [← hn]; simp
    subst hn'
    have hu := ih _ rfl
    change IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det
    rcases det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1
    · rw [h1]
      exact hu.mul ((Units.isUnit t).pow _)
    · rw [h1]
      exact (hu.mul ((Units.isUnit t).pow _)).neg

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
