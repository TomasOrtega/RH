import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.RowRawRange
open ValuativeRel MeasureTheory ComplexConjugate Formalism.MainNotions.S.Loc GlobalTheory.SgLoc
open scoped ComplexOrder

namespace GlobalTheory.SgLoc.PtAlg

variable {E : Type} [CommRing E]

/- English proof (translation)
Proceed by induction on `bs with`. Consider the case `nil`. Introduce `m hm a b`. Simplify using `only [List.map_nil, List.sum_nil] at hm`. Substitute `hm` using the available equality.

Simplify using `only [List.nil_append, ptEntryL]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Consider the case `cons hd bs ih`. Take `⟨t', s'⟩` from `hd`. Introduce `m hm a b`.

Simplify using `only [List.map_cons, List.sum_cons] at hm`. Simplify using `only [List.cons_append, ptEntryL]`. Rewrite using `[ih _ rfl]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
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
Use `show ptEntryL (h.blocks ++ [(t, s)]) a b = _`. Rewrite using `[ptEntryL_append h.blocks t s m h.size]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem mat_snoc {m : ℕ} (h : Pt E m) (t : Eˣ) (s : ℕ+) (a b : Fin (m + s)) :
    (h.snoc t s).mat a b =
      if hab : (a : ℕ) < m ∧ (b : ℕ) < m then h.mat ⟨a, hab.1⟩ ⟨b, hab.2⟩
      else if m ≤ (a : ℕ) ∧ m ≤ (b : ℕ) ∧ (a : ℕ) + b + 1 = 2 * m + s then (t : E) else 0 := by
  show ptEntryL (h.blocks ++ [(t, s)]) a b = _
  rw [ptEntryL_append h.blocks t s m h.size]
  split_ifs <;> rfl

/- English proof (translation)
Establish `key : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (h.snoc t s).mat = Matrix.fromBlocks h.mat 0 0 ((t : E) • (Fin.revPerm : Equiv.Perm (Fin s)).permMatrix E)`. Apply the tactic sequence `ext (i | i) (j | j) <;>`. Apply the tactic sequence `simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, mat_snoc, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, …`. Apply the tactic sequence `have hi := i.isLt <;> have hj := j.isLt`. Rewrite using `[dif_pos ⟨hi, hj⟩]`.

Rewrite using `[dif_neg (by omega), if_neg (by omega)]`. Rewrite using `[dif_neg (by omega), if_neg (by omega)]`. Rewrite using `[dif_neg (by omega)]`. Simplify using `only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq, Fin.revPerm_apply]`. Distinguish the cases in `hij : Fin.rev i = j`.

Rewrite using `[if_pos (by rw [← hij, Fin.val_rev]; omega), if_pos hij, mul_one]`. Rewrite using `[if_neg (fun hc => hij (Fin.ext (by rw [Fin.val_rev]; omega))), if_neg hij, mul_zero]`. Establish `hdet` using `congrArg Matrix.det key`. Rewrite `hdet` using `[Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_permutation, Fintype.card_fin]`. Rewrite using `[hdet]`.

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
Rewrite using `[det_snoc_eq]`. Break down `Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin s))) with h1 | h1` into its components or cases. Use `left`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.

Use `right`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
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
Proceed by induction on `bs using List.reverseRecOn with`. Consider the case `nil`. Introduce `n hn`. Establish `hn' : n = 0` using `by rw [← hn]; simp`. Substitute `hn'` using the available equality.

Simplify using the standard rewrite rules. Consider the case `append_singleton bs x ih`. Take `⟨t, s⟩` from `x`. Introduce `n hn`. Establish `hn' : n = (bs.map (fun b => (b.2 : ℕ))).sum + s` using `by rw [← hn]; simp`.

Substitute `hn'` using the available equality. Establish `hu` using `ih _ rfl`. Express the relevant statement in the definitionally equal form `IsUnit (Pt.snoc (⟨bs, rfl⟩ : Pt E _) t s).mat.det`. Break down `det_snoc (⟨bs, rfl⟩ : Pt E _) t s with h1 | h1` into its components or cases. Rewrite using `[h1]`.

Conclude with `hu.mul ((Units.isUnit t).pow _)`. Rewrite using `[h1]`. Conclude with `(hu.mul ((Units.isUnit t).pow _)).neg`.
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
Conclude with `isUnit_det_of_mem_UH_Hpk h.blocks m h.size`.
-/
theorem isUnit_det {m : ℕ} (h : Pt E m) : IsUnit h.mat.det := by
  exact isUnit_det_of_mem_UH_Hpk h.blocks m h.size

end GlobalTheory.SgLoc.PtAlg

namespace GlobalTheory.SgLoc

end GlobalTheory.SgLoc
