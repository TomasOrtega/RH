import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainFirstIdentity

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBN

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

/- English proof (translation)
Use `set a := xR k r (m + 2) hm with hadef`. Establish `hav : ∀ l, (a l).val = l.val` using `by intro l; simp [a, xR, eI]`. Establish `hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega)`. Use function extensionality and compare the values at `l`. Use `ext`.

Simplify using `[a, xR, eI]`. Establish `hexp` using `Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u`. Rewrite using `[hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`. Establish `hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) …`. Introduce `l`.

Rewrite using `[la_intmul]`. Establish `hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1))`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`.

Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tm_offdiag _ _ hne]`. Establish `ha1 : a (Fin.castSucc (Fin.castSucc l)) = eI k r ⟨l.val, by omega⟩` using `by ext; rw [hav]; simp [eI]`. Establish `ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩` using `by ext; rw [hav]; simp [eI]`.

Rewrite using `[ha1, ha2, hR0 _ l.val l.isLt, smul_zero]`. Rewrite using `[Finset.sum_eq_zero (fun l _ => hzero l), zero_add]`. Establish `hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) = La (qminor E (xR k r (m + 1) (by omega)) (xR k …`. Rewrite using `[la_intmul, Fin.succAbove_last, hcs]`. Establish `h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩` using `by ext; rw [hav]; simp [eI]`.

Rewrite using `[h1]`. Establish `h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1`. Simplify using `only [Fin.val_last]`. Rewrite using `[← two_mul, pow_mul]`. Evaluate the numerical expressions.

Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite using `[hlast]`. Use `set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP`. Establish `hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1))`.

Use function extensionality and compare the values at `q`. Use `ext`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hq : q = Fin.last m`. Substitute `hq` using the available equality.

Rewrite using `[finRotate_last]`. Simplify using `only [rowsP, Fin.cons_zero]`. Rewrite using `[hav, succAbove_val]`. Simplify using `[eI]`. Establish `hq' : q.val < m`.

Use `q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega` as an intermediate fact. Establish `hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩` using `by ext; rw [coe_finRotate_of_ne_last hq]; simp`. Rewrite using `[hr1]`. Simplify using `only [rowsP, Fin.cons_succ]`. Rewrite using `[hav, succAbove_val]`.

Simplify using `[xR, eI]`. Use linear arithmetic over natural numbers and integers. Establish `hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) = (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u)`. Rewrite using `[hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]`. Rewrite using `[Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]`.

Rewrite using `[Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]`. Rewrite using `[la_intmul]`. Establish `hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩` using `by simp [rowsP]`. Establish `hrs : rowsP ∘ Fin.succ = xR k r m (by omega)` using `by funext q; simp [rowsP]`. Rewrite using `[hr0, hrs, Fin.succAbove_last, hcs]`.

Establish `hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m)`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Simplify using `[eI, xR] at this`. Rewrite using `[tm_offdiag _ _ hne]`.

Establish `hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩` using `by ext; simp [xR, eI]`. Rewrite using `[hx, hL _ m le_rfl, if_pos rfl]`. Establish `hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega)` using `by funext q; ext; simp [xR, eI]`. Rewrite using `[hcs2, smul_smul, smul_smul]`. Use `congr 1`.

Simplify using `only [Fin.val_last]`. Use `push_cast`. Rewrite using `[neg_one_sq', one_mul]`. Introduce `q _`. Rewrite using `[la_intmul]`.

Establish `hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩` using `by simp [rowsP]`. Rewrite using `[hr0, hcs]`. Establish `hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val` using `by simp [xR, eI]`. Establish `hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q)`. Introduce `h'`.

Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hqv]`. Simplify using `[eI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[tm_offdiag _ _ hne]`.

Establish `hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩` using `by ext; simp [xR, eI]`. Establish `hq` using `q.isLt`. Rewrite using `[hx, hL _ q.val (by omega), if_neg (by omega), zero_smul, smul_zero]`. Establish `hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) = La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u)`. Establish `hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1))`.

Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Simplify using `at this`. Rewrite using `[tm_offdiag _ _ hne]`.

Establish `ha1 : a (Fin.castSucc (Fin.last m)) = eI k r ⟨m, by omega⟩` using `by ext; rw [hav]; simp [eI]`. Establish `ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩` using `by ext; rw [hav]; simp [eI]`. Rewrite using `[ha1, ha2, hR1]`. Rewrite using `[la_intmul, hmT, hQm]`. Establish `h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1`.

Simplify using `only [Fin.val_castSucc, Fin.val_last]`. Use `push_cast`. Rewrite using `[show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num`. Rewrite using `[h3, neg_one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem chainX1' {A M : Type} [Ring A] [Algebra ℂ A] [AddCommGroup M] [Module ℂ M] (k r : ℕ) (c : Fin r → ℂ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M) (hG : GlRel E) (m : ℕ) (hm : m + 2 ≤ r)
    (u : ℂ)
    (hR0 : ∀ (x : A) (l : ℕ) (hl : l < m), La (x * E (eI k r ⟨l, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = 0)
    (hR1 : ∀ x : A, La (x * E (eI k r ⟨m, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) = La x)
    (hL : ∀ (x : A) (q : ℕ) (hq : q ≤ m), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨q, by omega⟩) * x) =
      (if q = m then c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩ else 0) • La x) :
    La (qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
        (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
  rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]

  have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
    intro l
    rw [la_intmul]
    have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.castSucc l)) = eI k r ⟨l.val, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR0 _ l.val l.isLt, smul_zero]
  rw [Finset.sum_eq_zero (fun l _ => hzero l), zero_add]

  have hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) =
      La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) := by
    rw [la_intmul, Fin.succAbove_last, hcs]
    have h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [h1]
    have h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1 := by
      simp only [Fin.val_last]; rw [← two_mul, pow_mul]; norm_num
    rw [h2]; simp
  rw [hlast]

  set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP
  have hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1)) := by
    funext q
    ext
    simp only [Function.comp_apply]
    by_cases hq : q = Fin.last m
    · subst hq
      rw [finRotate_last]
      simp only [rowsP, Fin.cons_zero]
      rw [hav, succAbove_val]; simp [eI]
    · have hq' : q.val < m := by
        have := q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega
      have hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩ := by
        ext; rw [coe_finRotate_of_ne_last hq]; simp
      rw [hr1]
      simp only [rowsP, Fin.cons_succ]
      rw [hav, succAbove_val]; simp [xR, eI]; omega
  have hQm : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      (c ⟨m + 1, by omega⟩ / c ⟨m, by omega⟩) • La (qminor E (xR k r m (by omega)) (xR k r m (by omega)) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum]
    rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero, zero_add]
    · rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
      rw [hr0, hrs, Fin.succAbove_last, hcs]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.last m) := by
        intro h'; have := congrArg Fin.val h'; simp [eI, xR] at this
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.last m) = eI k r ⟨m, by omega⟩ := by ext; simp [xR, eI]
      rw [hx, hL _ m le_rfl, if_pos rfl]
      have hcs2 : xR k r (m + 1) (by omega) ∘ Fin.castSucc = xR k r m (by omega) := by funext q; ext; simp [xR, eI]
      rw [hcs2, smul_smul, smul_smul]
      congr 1
      simp only [Fin.val_last]
      push_cast
      rw [neg_one_sq', one_mul]
    · intro q _
      rw [la_intmul]
      have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
      rw [hr0, hcs]
      have hqv : (xR k r (m + 1) (by omega) (Fin.castSucc q)).val = q.val := by simp [xR, eI]
      have hne : eI k r ⟨m + 1, by omega⟩ ≠ xR k r (m + 1) (by omega) (Fin.castSucc q) := by
        intro h'; have := congrArg Fin.val h'; rw [hqv] at this; simp [eI] at this; omega
      rw [tm_offdiag _ _ hne]
      have hx : xR k r (m + 1) (by omega) (Fin.castSucc q) = eI k r ⟨q.val, by omega⟩ := by ext; simp [xR, eI]
      have hq := q.isLt
      rw [hx, hL _ q.val (by omega), if_neg (by omega), zero_smul, smul_zero]
  have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
      Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
      intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
    rw [tm_offdiag _ _ hne]
    have ha1 : a (Fin.castSucc (Fin.last m)) = eI k r ⟨m, by omega⟩ := by ext; rw [hav]; simp [eI]
    have ha2 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩ := by ext; rw [hav]; simp [eI]
    rw [ha1, ha2, hR1]
  rw [la_intmul, hmT, hQm]
  have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
    simp only [Fin.val_castSucc, Fin.val_last]
    push_cast
    rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [h3, neg_one_smul]; abel

end Formalism.FourierDecayAlt.P.PBN
