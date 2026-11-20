import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDACapTodaVGrpCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainX1

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.CutMP.TVG

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

/- English proof (translation)
Use function extensionality and compare the values at `j`. Use `ext`. Simplify using `[colsVm]`.
-/
theorem colsVm_castSucc {k r m : ℕ} (hm : m + 1 ≤ r) :
    colsVm k r (m + 1) ∘ Fin.castSucc = colsVm k r m := by
  funext j; ext; simp [colsVm]

/- English proof (translation)
Introduce `A _ _ M _ _ k r E La ρ hG m _hm u hR0 hR1 hL`. Establish `hm : m + 2 ≤ r` using `_hm`. Use `set a := colsVm k r (m + 2) with hadef`. Establish `hav : ∀ l : Fin (m + 2), (a l).val = r + k + 1 + l.val`. Introduce `l`.

Use `l.isLt` as an intermediate fact. Simplify using `[a, colsVm]`. Use linear arithmetic over natural numbers and integers. Establish `hcs : a ∘ Fin.castSucc = colsVm k r (m + 1)` using `colsVm_castSucc hm`. Establish `hexp` using `Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u`.

Rewrite using `[hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`. Establish `ha2 : a (Fin.last (m + 1)) = esI k r ⟨r - m - 2, by omega⟩` using `by ext; rw [hav]; simp [esI]; omega`. Establish `hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) …`. Introduce `l`. Rewrite using `[la_intmul]`.

Establish `hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1))`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[tm_offdiag _ _ hne]`. Establish `ha1 : a (Fin.castSucc (Fin.castSucc l)) = esI k r ⟨r - 1 - l.val, by omega⟩` using `by ext; rw [hav]; simp [esI]; omega`. Rewrite using `[ha1, ha2, hR0 _ ⟨r - 1 - l.val, by omega⟩ (by simp; omega), smul_zero]`. Rewrite using `[Finset.sum_eq_zero (fun l _ => hzero l), zero_add]`.

Establish `hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) = La (qminor E (colsVm k r (m + 1)) (colsVm k r ( …`. Rewrite using `[la_intmul, Fin.succAbove_last, hcs, ha2]`. Establish `h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1`. Simplify using `only [Fin.val_last]`. Rewrite using `[← two_mul, pow_mul]`.

Evaluate the numerical expressions. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite using `[hlast]`. Use `set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (esI k r ⟨r - m - 2, by omega⟩) (colsVm k r m) with hrP`.

Establish `hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1))`. Use function extensionality and compare the values at `q`. Use `ext`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hq : q = Fin.last m`.

Substitute `hq` using the available equality. Rewrite using `[finRotate_last]`. Simplify using `only [rowsP, Fin.cons_zero]`. Rewrite using `[hav, succAbove_val]`. Simplify using `[esI]`.

Use linear arithmetic over natural numbers and integers. Establish `hq' : q.val < m`. Use `q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega` as an intermediate fact. Establish `hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩` using `by ext; rw [coe_finRotate_of_ne_last hq]; simp`. Rewrite using `[hr1]`.

Simplify using `only [rowsP, Fin.cons_succ]`. Rewrite using `[hav, succAbove_val]`. Simplify using `[colsVm, hq']`. Use linear arithmetic over natural numbers and integers. Establish `hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) = ρ • La (qminor E (colsVm k r m) (colsVm k r m) u)`.

Rewrite using `[hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]`. Rewrite using `[Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]`. Rewrite using `[Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]`. Rewrite using `[la_intmul]`. Establish `hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩` using `by simp [rowsP]`.

Establish `hrs : rowsP ∘ Fin.succ = colsVm k r m` using `by funext q; simp [rowsP]`. Rewrite using `[hr0, hrs, Fin.succAbove_last, hcs]`. Establish `hx : colsVm k r (m + 1) (Fin.last m) = esI k r ⟨r - m - 1, by omega⟩` using `by ext; simp [colsVm, esI]; omega`. Establish `hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.last m)`. Rewrite using `[hx]`.

Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `[esI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tm_offdiag _ _ hne, hx, hL _ ⟨r - m - 1, by omega⟩ (by simp; omega), if_pos rfl]`.

Rewrite using `[colsVm_castSucc (by omega), smul_smul, smul_smul]`. Use `congr 1`. Simplify using `only [Fin.val_last]`. Use `push_cast`. Rewrite using `[neg_one_sq', one_mul]`.

Introduce `q _`. Rewrite using `[la_intmul]`. Establish `hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩` using `by simp [rowsP]`. Rewrite using `[hr0, hcs]`. Establish `hq` using `q.isLt`.

Establish `hx : colsVm k r (m + 1) (Fin.castSucc q) = esI k r ⟨r - 1 - q.val, by omega⟩` using `by ext; simp [colsVm, esI]`. Establish `hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.castSucc q)`. Rewrite using `[hx]`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `[esI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tm_offdiag _ _ hne, hx, hL _ ⟨r - 1 - q.val, by omega⟩ (by simp; omega), if_neg (by simp; omega), zero_smul, smul_zero]`. Establish `hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) = La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u)`. Establish `hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1))`.

Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Simplify using `at this`. Rewrite using `[tm_offdiag _ _ hne]`.

Establish `ha1 : a (Fin.castSucc (Fin.last m)) = esI k r ⟨r - m - 1, by omega⟩` using `by ext; rw [hav]; simp [esI]; omega`. Rewrite using `[ha1, ha2, hR1]`. Rewrite using `[la_intmul, hmT, hQm]`. Establish `h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`.

Use `push_cast`. Rewrite using `[show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num`. Rewrite using `[h3, neg_one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem mirror_chain_expansion_holds : MirrorChainExpansion := by
  intro A _ _ M _ _ k r E La ρ hG m _hm u hR0 hR1 hL
  have hm : m + 2 ≤ r := _hm
  set a := colsVm k r (m + 2) with hadef
  have hav : ∀ l : Fin (m + 2), (a l).val = r + k + 1 + l.val := by
    intro l; have := l.isLt; simp [a, colsVm]; omega
  have hcs : a ∘ Fin.castSucc = colsVm k r (m + 1) := colsVm_castSucc hm
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have ha2 : a (Fin.last (m + 1)) = esI k r ⟨r - m - 2, by omega⟩ := by
    ext; rw [hav]; simp [esI]; omega

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = esI k r ⟨r - 1 - l.val, by omega⟩ := by
      ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR0 _ ⟨r - 1 - l.val, by omega⟩ (by simp; omega), smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (colsVm k r (m + 1)) (colsVm k r (m + 1)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (esI k r ⟨r - m - 2, by omega⟩) (esI k r ⟨r - m - 2, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs, ha2]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (esI k r ⟨r - m - 2, by omega⟩) (colsVm k r m) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [esI]; omega
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [colsVm, hq']; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ρ • La (qminor E (colsVm k r m) (colsVm k r m) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = colsVm k r m := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hx : colsVm k r (m + 1) (Fin.last m) = esI k r ⟨r - m - 1, by omega⟩ := by
        ext; simp [colsVm, esI]; omega
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.last m) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - m - 1, by omega⟩ (by simp; omega), if_pos rfl]
      rw [colsVm_castSucc (by omega), smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = esI k r ⟨r - m - 2, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hq := q.isLt
      have hx : colsVm k r (m + 1) (Fin.castSucc q) = esI k r ⟨r - 1 - q.val, by omega⟩ := by
        ext; simp [colsVm, esI]
      have hne : esI k r ⟨r - m - 2, by omega⟩ ≠ colsVm k r (m + 1) (Fin.castSucc q) := by
        rw [hx]; intro h'; have := congrArg Fin.val h'; simp [esI] at this; omega
      rw [tm_offdiag _ _ hne, hx, hL _ ⟨r - 1 - q.val, by omega⟩ (by simp; omega), if_neg (by simp; omega),
        zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = esI k r ⟨r - m - 1, by omega⟩ := by ext; rw [hav]; simp [esI]; omega
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.CutMP.TVG
