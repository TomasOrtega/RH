import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.PBG

open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.SignAntidiagonal

/- English proof (translation)
Establish `hxi' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)) (ha : a.val < m + 1), xi a q = if h : q.val < m + 1 then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0`. Introduce `a q ha`. Use `hxi ⟨a.val, ha⟩ q` as an intermediate fact. Simplify using `using this`. Establish `hxl' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)), a.val = m + 1 → xi a q = if q.val = m + 1 then c else 0`.

Introduce `a q ha`. Establish `e : a = ⟨m + 1, by omega⟩` using `Fin.ext ha`. Rewrite using `[e]`. Conclude with `hxl q`. Establish `hA2 : AAx k r E xi (m + 2) hm u = (Z.det * c) • qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u`.

Rewrite using `[AAx_head k r E xi (m + 2) hm (Matrix.of fun a b : Fin (m + 2) => xi (Fin.castLE hm a) (xR k r (m + 2) hm b)) u ?_ (fun a b => rfl)]`. Use `congr 1`. Rewrite using `[Matrix.det_succ_row _ (Fin.last (m + 1)), Fin.sum_univ_castSucc, Finset.sum_eq_zero]`. Simplify using `only [Matrix.of_apply, Matrix.submatrix, Fin.succAbove_last, zero_add]`. Establish `h1 : xi (Fin.castLE hm (Fin.last (m + 1))) (xR k r (m + 2) hm (Fin.last (m + 1))) = c`.

Rewrite using `[hxl' _ _ (by simp), if_pos (by simp [xR, eI])]`. Rewrite using `[h1]`. Establish `h2 : (Matrix.of fun i j : Fin (m + 1) => xi (Fin.castLE hm (Fin.castSucc i)) (xR k r (m + 2) hm (Fin.castSucc j))) = Z`. Use extensionality with `i j`. Simplify using `only [Matrix.of_apply]`.

Apply the tactic sequence `rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]`. Use `congr 1`. Rewrite using `[h2]`. Simplify using `only [Fin.val_last]`. Rewrite using `[← two_mul, pow_mul]`.

Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Introduce `j _`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hxl' _ _ (by simp), if_neg (by simp [xR, eI]; omega)]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `a p ha hp`. Distinguish the cases in `ha' : a.val < m + 1`. Rewrite using `[hxi' a p ha', dif_neg (by omega)]`. Rewrite using `[hxl' a p (by omega), if_neg (by omega)]`.

Establish `hA1 : AAx k r E xi (m + 1) (by omega) u = Z.det • qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u`. Rewrite using `[AAx_head k r E xi (m + 1) (by omega) Z u]`. Introduce `a p ha hp`. Rewrite using `[hxi' a p ha, dif_neg (by omega)]`. Introduce `a b`.

Apply the tactic sequence `rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]`. Use `congr 1`. Establish `hA0 : AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1), (Z.submatrix Fin.castSucc l0.succAbove).det • qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l0.succAbove) u`. Rewrite using `[AAx_omit k r m (by omega) E xi u]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `l0 _`. Use `congr 2`. Use extensionality with `a l`. Simplify using `only [Matrix.of_apply, Matrix.submatrix_apply]`. Apply the tactic sequence `rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]`.

Use `congr 1`. Introduce `a p ha hp`. Rewrite using `[hxi' a p (by omega), dif_neg (by omega)]`. Use `set a := xR k r (m + 2) hm with hadef`. Establish `hav : ∀ l, (a l).val = l.val` using `by intro l; simp [a, xR, eI]`.

Establish `hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega)`. Use function extensionality and compare the values at `l`. Use `ext`. Simplify using `[a, xR, eI]`. Establish `hmain : La (qminor E a a u) = La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) - La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u …`.

Establish `hexp` using `Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u`. Rewrite using `[hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]`. Establish `hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))) …`. Introduce `l`. Rewrite using `[la_intmul]`.

Establish `hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1))`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp <;> omega) (by rw [hav]; simp <;> omega), if_neg (by rw [hav, hav]; simp <;> omega), zero_smul, smul_zero]`. Rewrite using `[Finset.sum_eq_zero (fun l _ => hzero l), zero_add]`. Establish `hlast : La ((((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ)) : ℤ) : A) * (qminor E (a ∘ (Fin.last (m + 1)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.last (m + 1))) (a (Fin.last (m + 1))))) = La (qminor E (xR k r (m + 1) (by omega)) (xR k …`. Rewrite using `[la_intmul, Fin.succAbove_last, hcs]`.

Establish `h1 : a (Fin.last (m + 1)) = eI k r ⟨m + 1, by omega⟩` using `by ext; rw [hav]; simp [eI]`. Rewrite using `[h1]`. Establish `h2 : ((-1 : ℤ) ^ (m + 1 + ((Fin.last (m + 1) : Fin (m + 2)) : ℕ))) = 1`. Simplify using `only [Fin.val_last]`. Rewrite using `[← two_mul, pow_mul]`.

Evaluate the numerical expressions. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Rewrite using `[hlast]`. Establish `hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u * Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) = La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u)`.

Establish `hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1))`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact. Rewrite `this` using `[hav, hav]`. Simplify using `at this`.

Apply the tactic sequence `rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp) (by rw [hav]; simp <;> omega), if_pos (by rw [hav, hav]; simp), one_smul]`. Rewrite using `[la_intmul, hmT]`. Establish `h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`. Use `push_cast`.

Rewrite using `[show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num`. Rewrite using `[h3, neg_one_smul]`. Normalize the expressions using the abelian group laws. Use `set rowsP : Fin (m + 1) → Fin (2 * r + k + 1) := Fin.cons (eI k r ⟨m + 1, by omega⟩) (xR k r m (by omega)) with hrP`. Establish `hrows : a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove = rowsP ∘ (finRotate (m + 1))`.

Use function extensionality and compare the values at `q`. Use `ext`. Simplify using `only [Function.comp_apply]`. Distinguish the cases in `hq : q = Fin.last m`. Substitute `hq` using the available equality.

Rewrite using `[finRotate_last]`. Simplify using `only [rowsP, Fin.cons_zero]`. Rewrite using `[hav, succAbove_val]`. Simplify using `[eI]`. Establish `hq' : q.val < m`.

Use `q.isLt; have : q.val ≠ m := fun h' => hq (Fin.ext (by simp [h'])); omega` as an intermediate fact. Establish `hr1 : finRotate (m + 1) q = Fin.succ ⟨q.val, hq'⟩` using `by ext; rw [coe_finRotate_of_ne_last hq]; simp`. Rewrite using `[hr1]`. Simplify using `only [rowsP, Fin.cons_succ]`. Rewrite using `[hav, succAbove_val]`.

Simplify using `[xR, eI]`. Use linear arithmetic over natural numbers and integers. Establish `hQ : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) = ∑ l : Fin (m + 1), ((-1 : ℂ) ^ (m + (l : ℕ)) * (c' * Z⁻¹ l (Fin.last m))) • La (qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l.succAbove) u)`. Rewrite using `[hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]`. Rewrite using `[Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum, Finset.smul_sum]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[la_intmul]`. Establish `hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩` using `by simp [rowsP]`. Establish `hrs : rowsP ∘ Fin.succ = xR k r m (by omega)` using `by funext q; simp [rowsP]`.

Rewrite using `[hr0, hrs, hcs]`. Establish `hx : xR k r (m + 1) (by omega) l = eI k r ⟨l.val, by omega⟩` using `by ext; simp [xR, eI]`. Establish `hne : eI k r ⟨m + 1, by omega⟩ ≠ eI k r ⟨l.val, by omega⟩`. Introduce `h'`. Use `congrArg Fin.val h'` as an intermediate fact.

Simplify using `[eI] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hx, tm_offdiag _ _ hne, hL l, smul_smul, smul_smul]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[pow_add]`. Apply the tactic sequence `try ring`. Establish `hT : Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) = algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)`. Simplify using `[Tm]`. Rewrite using `[hA2, hA1, hA0, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hZ hc), one_smul, smul_mul_assoc, map_smul, smul_smul, inv_mul_cancel₀ hZ, one_smul, map_sum, hmain, hQ, hT, Finset.smul_sum]`.

Use `congr 1`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `l _`. Rewrite using `[map_smul, smul_smul, inv_last Z hZ]`. Use `congr 1`.

Establish `hs : ((-1 : ℂ) ^ (m + (l : ℕ))) * (-1) ^ (m + (l : ℕ)) = 1`. Rewrite using `[← pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions. Take the linear combination `(c' * Z.det⁻¹ * (Z.submatrix Fin.castSucc l.succAbove).det) * hs`.
-/
theorem headAlg_gen (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ)
    (hm : m + 2 ≤ r) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (c c' u : ℂ)
    (hG : Formalism.REAL.GlRel E)
    (hR : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r →
      La (x * E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x)
    (hZ : Z.det ≠ 0) (hc : c ≠ 0)
    (hL : ∀ (b : Fin (m + 1)) (x : A), La (E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c' * Z⁻¹ b (Fin.last m)) • La x)
    (hxi : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z a ⟨q, h⟩ else 0)
    (hxl : ∀ q : Fin (2 * r + k + 1), xi ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0) :
    (Z.det * c)⁻¹ • La (C3.AAx k r E xi (m + 2) hm u) =
      Z.det⁻¹ • La (C3.AAx k r E xi (m + 1) (by omega) u *
          (algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩))) -
        (c' * Z.det⁻¹) • La (C3.AAx k r E xi m (by omega) u) := by
  have hxi' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)) (ha : a.val < m + 1),
      xi a q = if h : q.val < m + 1 then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
    intro a q ha; have := hxi ⟨a.val, ha⟩ q; simpa using this
  have hxl' : ∀ (a : Fin r) (q : Fin (2 * r + k + 1)), a.val = m + 1 → xi a q = if q.val = m + 1 then c else 0 := by
    intro a q ha
    have e : a = ⟨m + 1, by omega⟩ := Fin.ext ha
    rw [e]; exact hxl q

  have hA2 : AAx k r E xi (m + 2) hm u = (Z.det * c) • qminor E (xR k r (m + 2) hm) (xR k r (m + 2) hm) u := by
    rw [AAx_head k r E xi (m + 2) hm (Matrix.of fun a b : Fin (m + 2) => xi (Fin.castLE hm a) (xR k r (m + 2) hm b)) u
      ?_ (fun a b => rfl)]
    · congr 1
      rw [Matrix.det_succ_row _ (Fin.last (m + 1)), Fin.sum_univ_castSucc, Finset.sum_eq_zero]
      · simp only [Matrix.of_apply, Matrix.submatrix, Fin.succAbove_last, zero_add]
        have h1 : xi (Fin.castLE hm (Fin.last (m + 1))) (xR k r (m + 2) hm (Fin.last (m + 1))) = c := by
          rw [hxl' _ _ (by simp), if_pos (by simp [xR, eI])]
        rw [h1]
        have h2 : (Matrix.of fun i j : Fin (m + 1) => xi (Fin.castLE hm (Fin.castSucc i))
            (xR k r (m + 2) hm (Fin.castSucc j))) = Z := by
          ext i j
          simp only [Matrix.of_apply]
          rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
          congr 1
        rw [h2]
        simp only [Fin.val_last]
        rw [← two_mul, pow_mul]; norm_num; ring
      · intro j _
        simp only [Matrix.of_apply]
        rw [hxl' _ _ (by simp), if_neg (by simp [xR, eI]; omega)]
        ring
    · intro a p ha hp
      by_cases ha' : a.val < m + 1
      · rw [hxi' a p ha', dif_neg (by omega)]
      · rw [hxl' a p (by omega), if_neg (by omega)]
  have hA1 : AAx k r E xi (m + 1) (by omega) u = Z.det • qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u := by
    rw [AAx_head k r E xi (m + 1) (by omega) Z u]
    · intro a p ha hp
      rw [hxi' a p ha, dif_neg (by omega)]
    · intro a b
      rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
      congr 1
  have hA0 : AAx k r E xi m (by omega) u = ∑ l0 : Fin (m + 1),
      (Z.submatrix Fin.castSucc l0.succAbove).det •
        qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l0.succAbove) u := by
    rw [AAx_omit k r m (by omega) E xi u]
    · apply Finset.sum_congr rfl
      intro l0 _
      congr 2
      ext a l
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [hxi' _ _ (by simp <;> omega), dif_pos (by simp [xR, eI] <;> omega)]
      congr 1
    · intro a p ha hp
      rw [hxi' a p (by omega), dif_neg (by omega)]

  set a := xR k r (m + 2) hm with hadef
  have hav : ∀ l, (a l).val = l.val := by intro l; simp [a, xR, eI]
  have hcs : a ∘ Fin.castSucc = xR k r (m + 1) (by omega) := by
    funext l; ext; simp [a, xR, eI]
  have hmain : La (qminor E a a u) = La (qminor E (xR k r (m + 1) (by omega)) (xR k r (m + 1) (by omega)) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩)) -
      La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
    have hexp := Formalism.FourierDecayAlt.P.expansion_last_column A _ (m + 1) E a a u
    rw [hexp, map_sum, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    have hzero : ∀ l : Fin m, La ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.castSucc l) : Fin (m + 2)) : ℕ)) : ℤ) : A) *
        (qminor E (a ∘ (Fin.castSucc (Fin.castSucc l)).succAbove) (a ∘ Fin.castSucc) u *
          Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.castSucc l))) (a (Fin.last (m + 1))))) = 0 := by
      intro l
      rw [la_intmul]
      have hne : a (Fin.castSucc (Fin.castSucc l)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this; omega
      rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp <;> omega) (by rw [hav]; simp <;> omega),
        if_neg (by rw [hav, hav]; simp <;> omega), zero_smul, smul_zero]
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
    have hmT : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u *
        Tm E (u - ((m + 1 : ℕ) : ℂ)) (a (Fin.castSucc (Fin.last m))) (a (Fin.last (m + 1)))) =
        La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) := by
      have hne : a (Fin.castSucc (Fin.last m)) ≠ a (Fin.last (m + 1)) := by
        intro h'; have := congrArg Fin.val h'; rw [hav, hav] at this; simp at this
      rw [tm_offdiag _ _ hne, hR _ _ _ (by rw [hav, hav]; simp) (by rw [hav]; simp <;> omega),
        if_pos (by rw [hav, hav]; simp), one_smul]
    rw [la_intmul, hmT]
    have h3 : ((((-1 : ℤ) ^ (m + 1 + ((Fin.castSucc (Fin.last m) : Fin (m + 2)) : ℕ))) : ℤ) : ℂ) = -1 := by
      simp only [Fin.val_castSucc, Fin.val_last]
      push_cast
      rw [show m + 1 + m = 2 * m + 1 by ring, pow_succ, pow_mul]; norm_num
    rw [h3, neg_one_smul]; abel

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
  have hQ : La (qminor E (a ∘ (Fin.castSucc (Fin.last m) : Fin (m + 2)).succAbove) (a ∘ Fin.castSucc) u) =
      ∑ l : Fin (m + 1), ((-1 : ℂ) ^ (m + (l : ℕ)) * (c' * Z⁻¹ l (Fin.last m))) •
        La (qminor E (xR k r m (by omega)) (xR k r (m + 1) (by omega) ∘ l.succAbove) u) := by
    rw [hrows, Formalism.REAL.quantumMinorRowSkew_holds A _ (m + 1) E rowsP _ (finRotate (m + 1)) u, la_intmul, sign_finRotate]
    rw [Formalism.FourierDecayAlt.P.expansion_first_line A _ m E hG rowsP _ u, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [la_intmul]
    have hr0 : rowsP 0 = eI k r ⟨m + 1, by omega⟩ := by simp [rowsP]
    have hrs : rowsP ∘ Fin.succ = xR k r m (by omega) := by funext q; simp [rowsP]
    rw [hr0, hrs, hcs]
    have hx : xR k r (m + 1) (by omega) l = eI k r ⟨l.val, by omega⟩ := by ext; simp [xR, eI]
    have hne : eI k r ⟨m + 1, by omega⟩ ≠ eI k r ⟨l.val, by omega⟩ := by
      intro h'; have := congrArg Fin.val h'; simp [eI] at this; omega
    rw [hx, tm_offdiag _ _ hne, hL l, smul_smul, smul_smul]
    congr 1
    push_cast
    rw [pow_add]
    try ring
  have hT : Tm E (u - ((m + 1 : ℕ) : ℂ)) (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      algebraMap ℂ A (u - ((m + 1 : ℕ) : ℂ)) + E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) := by
    simp [Tm]
  rw [hA2, hA1, hA0, map_smul, smul_smul, inv_mul_cancel₀ (mul_ne_zero hZ hc), one_smul, smul_mul_assoc, map_smul,
    smul_smul, inv_mul_cancel₀ hZ, one_smul, map_sum, hmain, hQ, hT, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  rw [map_smul, smul_smul, inv_last Z hZ]
  congr 1
  have hs : ((-1 : ℂ) ^ (m + (l : ℕ))) * (-1) ^ (m + (l : ℕ)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  linear_combination (c' * Z.det⁻¹ * (Z.submatrix Fin.castSucc l.succAbove).det) * hs

section mirror

variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

def rv (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) := Fin.rev p

def ep (p : Fin (2 * r + k + 1)) : ℂ := (-1 : ℂ) ^ (p : ℕ)

/- English proof (translation)
Unfold `ep`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem ep_sq (p : Fin (2 * r + k + 1)) : ep p * ep p = 1 := by
  unfold ep
  rw [← mul_pow]
  norm_num

/- English proof (translation)
The claim follows from `Fin.rev_rev p`.
-/
theorem rv_rv (p : Fin (2 * r + k + 1)) : rv (rv p) = p := Fin.rev_rev p

/- English proof (translation)
Simplify using `only [rv, Fin.val_rev]`. Use linear arithmetic over natural numbers and integers.
-/
theorem rv_val (p : Fin (2 * r + k + 1)) : (rv p).val = 2 * r + k - p.val := by
  simp only [rv, Fin.val_rev]
  omega

/- English proof (translation)
Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[rv_val]`. Simplify using `[eI, esI]`.
-/
theorem rv_eI (b : Fin r) : rv (eI k r b) = esI k r b := by
  apply Fin.ext
  rw [rv_val]
  simp [eI, esI]

def Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (p q : Fin (2 * r + k + 1)) : A :=
  -((ep p * ep q) • E (rv q) (rv p))

/- English proof (translation)
Introduce `a b c d`. Establish `hinj : ∀ x y : Fin (2 * r + k + 1), rv x = rv y ↔ x = y` using `fun x y => ⟨fun h => by rw [← rv_rv x, h, rv_rv], fun h => h ▸ rfl⟩`. Establish `key` using `hE (rv b) (rv a) (rv d) (rv c)`. Simplify using `only [hinj] at key`. Establish `h1 : Emir E a b * Emir E c d - Emir E c d * Emir E a b = (ep a * ep b * (ep c * ep d)) • (E (rv b) (rv a) * E (rv d) (rv c) - E (rv d) (rv c) * E (rv b) (rv a))`.

Simplify using `only [Emir, neg_mul_neg, smul_mul_smul_comm, smul_sub, mul_comm (ep c * ep d) (ep a * ep b)]`. Rewrite using `[h1, key]`. Distinguish the cases in `hbc : b = c`. Substitute `c` using the available equality. Distinguish the cases in `hda : d = a`.

Substitute `a` using the available equality. Establish `hs : ep d * ep b * (ep b * ep d) = 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [if_true, hs, one_smul, Emir, ep_sq, neg_sub_neg]`. Establish `hs : ep a * ep b * (ep b * ep d) = ep a * ep d`.

Combine the equalities or inequalities in the displayed calculation. Establish `had : ¬ a = d` using `fun e => hda e.symm`. Simplify using `only [if_true, had, hda, if_false, hs, Emir, zero_sub, sub_zero, smul_neg]`. Distinguish the cases in `hda : d = a`. Substitute `a` using the available equality.

Establish `hs : ep d * ep b * (ep c * ep d) = ep c * ep b`. Combine the equalities or inequalities in the displayed calculation. Establish `hcb : ¬ c = b` using `fun e => hbc e.symm`. Simplify using `only [if_true, hcb, hbc, if_false, hs, Emir, zero_sub, sub_zero, neg_neg]`. Establish `had : ¬ a = d` using `fun e => hda e.symm`.

Establish `hcb : ¬ c = b` using `fun e => hbc e.symm`. Simplify using `only [had, hcb, hbc, hda, if_false, sub_zero, smul_zero]`.
-/
theorem Emir_gl {E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A} (hE : Formalism.REAL.GlRel E) :
    Formalism.REAL.GlRel (Emir E) := by
  intro a b c d
  have hinj : ∀ x y : Fin (2 * r + k + 1), rv x = rv y ↔ x = y := fun x y =>
    ⟨fun h => by rw [← rv_rv x, h, rv_rv], fun h => h ▸ rfl⟩
  have key := hE (rv b) (rv a) (rv d) (rv c)
  simp only [hinj] at key
  have h1 : Emir E a b * Emir E c d - Emir E c d * Emir E a b =
      (ep a * ep b * (ep c * ep d)) •
        (E (rv b) (rv a) * E (rv d) (rv c) - E (rv d) (rv c) * E (rv b) (rv a)) := by
    simp only [Emir, neg_mul_neg, smul_mul_smul_comm, smul_sub, mul_comm (ep c * ep d) (ep a * ep b)]
  rw [h1, key]
  by_cases hbc : b = c
  · subst c
    by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep b * ep d) = 1 := by
        calc _ = (ep d * ep d) * (ep b * ep b) := by ring
          _ = 1 := by rw [ep_sq, ep_sq, mul_one]
      simp only [if_true, hs, one_smul, Emir, ep_sq, neg_sub_neg]
    · have hs : ep a * ep b * (ep b * ep d) = ep a * ep d := by
        calc _ = ep a * ep d * (ep b * ep b) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have had : ¬ a = d := fun e => hda e.symm
      simp only [if_true, had, hda, if_false, hs, Emir, zero_sub, sub_zero, smul_neg]
  · by_cases hda : d = a
    · subst a
      have hs : ep d * ep b * (ep c * ep d) = ep c * ep b := by
        calc _ = ep c * ep b * (ep d * ep d) := by ring
          _ = _ := by rw [ep_sq, mul_one]
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [if_true, hcb, hbc, if_false, hs, Emir, zero_sub, sub_zero, neg_neg]
    · have had : ¬ a = d := fun e => hda e.symm
      have hcb : ¬ c = b := fun e => hbc e.symm
      simp only [had, hcb, hbc, hda, if_false, sub_zero, smul_zero]

/- English proof (translation)
Distinguish the cases in `h : p = q`. Substitute `q` using the available equality. Simplify using `only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, if_true, ep_sq, one_smul]`. Establish `h' : ¬ rv p = rv q` using `fun e => h (by rw [← rv_rv p, e, rv_rv])`. Simplify using `only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, h, h', if_false, zero_add, smul_neg]`.
-/
theorem Tm_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (v : ℂ) (p q : Fin (2 * r + k + 1)) :
    Tm (Emir E) v p q = (ep p * ep q) • Tm (Formalism.FourierDecayAlt.P.Qx5.Eop E) v (rv p) (rv q) := by
  by_cases h : p = q
  · subst q
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, if_true, ep_sq, one_smul]
  · have h' : ¬ rv p = rv q := fun e => h (by rw [← rv_rv p, e, rv_rv])
    simp only [Tm, Emir, Formalism.FourierDecayAlt.P.Qx5.Eop, h, h', if_false, zero_add, smul_neg]

/- English proof (translation)
The claim follows from `| 0, c, X => by simp | n + 1, c, X => by rw [List.ofFn_succ, List.prod_cons, ofFn_prod_smul' (fun i => c i.succ) (fun i => X i.succ), Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]`.
-/
theorem ofFn_prod_smul' : ∀ {n : ℕ} (c : Fin n → ℂ) (X : Fin n → A),
    (List.ofFn fun i => c i • X i).prod = (∏ i, c i) • (List.ofFn X).prod
  | 0, c, X => by simp
  | n + 1, c, X => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_smul' (fun i => c i.succ) (fun i => X i.succ), Fin.prod_univ_succ,
      List.ofFn_succ, List.prod_cons, smul_mul_smul_comm]

/- English proof (translation)
Unfold `qminor`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Tm_Emir, ofFn_prod_smul', Function.comp_apply]`. Rewrite using `[mul_smul_comm]`.

Use `congr 1`. Rewrite using `[Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ep (a i))]`.
-/
theorem qminor_Emir (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) {t : ℕ} (a b : Fin t → Fin (2 * r + k + 1))
    (u : ℂ) : qminor (Emir E) a b u =
      ((∏ i, ep (a i)) * (∏ i, ep (b i))) • qminor (Formalism.FourierDecayAlt.P.Qx5.Eop E) (rv ∘ a) (rv ∘ b) u := by
  unfold qminor
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Tm_Emir, ofFn_prod_smul', Function.comp_apply]
  rw [mul_smul_comm]
  congr 1
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ (fun i => ep (a i))]

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun l _ => ep_sq _`.
-/
theorem prod_ep_sq {m : ℕ} (c : Fin m → Fin (2 * r + k + 1)) : (∏ l, ep (c l)) * (∏ l, ep (c l)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun l _ => ep_sq _

/- English proof (translation)
Use function extensionality and compare the values at `l`. Conclude with `rv_eI (Fin.castLE hm l)`.
-/
theorem rv_xR (m : ℕ) (hm : m ≤ r) : rv ∘ xR k r m hm = sR k r m hm := by
  funext l
  exact rv_eI (Fin.castLE hm l)

open scoped Classical in

/- English proof (translation)
Unfold `C3.AAx C3.AAv`. Rewrite using `[Finset.smul_sum]`. Use `Fintype.sum_equiv ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) _ _ (fun c => ?_)` and prove the remaining obligations. Establish `hB : ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) c = rv ∘ c`. Use function extensionality and compare the values at `l`.

Simplify using `[Equiv.arrowCongr_apply, rv]`. Rewrite using `[hB]`. Use `set Yc : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a l => y (Fin.castLE hm a) (rv (c l)) with hYc`. Establish `hdet : (Matrix.of fun a l : Fin m => ep (c l) * y (Fin.castLE hm a) (rv (c l))).det = (∏ l, ep (c l)) * Yc.det` using `Matrix.det_mul_row _ _`. Establish `hq : qminor (Emir E) (xR k r m hm) c (-ℓ) = (((∏ l, ep (xR k r m hm l)) * (∏ l, ep (c l))) * (-1) ^ m) • qminor E (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1)`.

Rewrite using `[qminor_Emir, rv_xR, Formalism.FourierDecayAlt.P.Qx5.duality hG (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1), smul_smul]`. Establish `hp : ((m : ℂ) - 1 - (ℓ + (m : ℂ) - 1)) = -ℓ` using `by ring`. Establish `hs : ((-1 : ℂ) ^ m * (-1) ^ m) = 1` using `by rw [← mul_pow]; norm_num`. Rewrite using `[hp, mul_assoc, hs, mul_one]`. Distinguish the cases in `hY : Yc.det = 0`.

Establish `h1 : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = 0` using `hY`. Rewrite using `[hdet, hY, mul_zero]`. Simplify using `only [h1, zero_smul, ite_self, smul_zero]`. Establish `hcol : ∀ l, (c l).val < r`. Introduce `l`.

Assume the negation of the conclusion as `hl`. Apply `hY` to reduce the goal to its premises. Apply `Matrix.det_eq_zero_of_column_eq_zero l` to reduce the goal to its premises. Introduce `a`. Simplify using `only [hYc, Matrix.of_apply]`.

Assume the negation of the conclusion as `hne`. Use `hsupp _ _ (by simp) hne` as an intermediate fact. Rewrite `this` using `[rv_val]`. Use linear arithmetic over natural numbers and integers. Establish `hkey : ∀ l, C3.keyS k r ((rv ∘ c) l) = (c l).val`.

Introduce `l`. Simplify using `only [Function.comp_apply, C3.keyS, rv_val]`. Rewrite using `[if_pos (by have := hcol l; omega)]`. Use `(c l).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hmono : StrictMono c ↔ StrictMono (fun l => C3.keyS k r ((rv ∘ c) l))`. Simplify using `only [hkey]`. Conclude with `⟨fun h a b hab => h hab, fun h a b hab => h hab⟩`. Distinguish the cases in `hS : StrictMono c`. Establish `hYc' : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = Yc.det` using `rfl`.

Rewrite using `[if_pos hS, if_pos (hmono.1 hS), hdet, hq, smul_smul, smul_smul, hYc']`. Use `congr 1`. Establish `h2` using `prod_ep_sq (k := k) (r := r) c`. Take the linear combination `((∏ l, ep (xR k r m hm l)) * (-1) ^ m * Yc.det) * h2`. Rewrite using `[if_neg hS, if_neg (fun h => hS (hmono.2 h)), smul_zero]`.
-/
theorem AAx_mirror (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : Formalism.REAL.GlRel E)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (hsupp : ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m → y a p ≠ 0 → r + k < p.val) :
    C3.AAx k r (Emir E) (fun a q => ep q * y a (rv q)) m hm (-ℓ) =
      ((∏ l : Fin m, ep (xR k r m hm l)) * (-1) ^ m) • C3.AAv k r E y m hm ℓ := by
  unfold C3.AAx C3.AAv
  rw [Finset.smul_sum]
  refine Fintype.sum_equiv ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) _ _
    (fun c => ?_)
  have hB : ((Equiv.refl (Fin m)).arrowCongr (Fin.revPerm : Equiv.Perm (Fin (2 * r + k + 1)))) c = rv ∘ c := by
    funext l; simp [Equiv.arrowCongr_apply, rv]
  rw [hB]
  set Yc : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a l => y (Fin.castLE hm a) (rv (c l)) with hYc
  have hdet : (Matrix.of fun a l : Fin m => ep (c l) * y (Fin.castLE hm a) (rv (c l))).det =
      (∏ l, ep (c l)) * Yc.det := Matrix.det_mul_row _ _

  have hq : qminor (Emir E) (xR k r m hm) c (-ℓ) =
      (((∏ l, ep (xR k r m hm l)) * (∏ l, ep (c l))) * (-1) ^ m) • qminor E (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1) := by
    rw [qminor_Emir, rv_xR, Formalism.FourierDecayAlt.P.Qx5.duality hG (rv ∘ c) (sR k r m hm) (ℓ + (m : ℂ) - 1), smul_smul]
    have hp : ((m : ℂ) - 1 - (ℓ + (m : ℂ) - 1)) = -ℓ := by ring
    have hs : ((-1 : ℂ) ^ m * (-1) ^ m) = 1 := by rw [← mul_pow]; norm_num
    rw [hp, mul_assoc, hs, mul_one]
  by_cases hY : Yc.det = 0
  · have h1 : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = 0 := hY
    rw [hdet, hY, mul_zero]
    simp only [h1, zero_smul, ite_self, smul_zero]
  ·
    have hcol : ∀ l, (c l).val < r := by
      intro l
      by_contra hl
      apply hY
      apply Matrix.det_eq_zero_of_column_eq_zero l
      intro a
      simp only [hYc, Matrix.of_apply]
      by_contra hne
      have := hsupp _ _ (by simp) hne
      rw [rv_val] at this
      omega
    have hkey : ∀ l, C3.keyS k r ((rv ∘ c) l) = (c l).val := by
      intro l
      simp only [Function.comp_apply, C3.keyS, rv_val]
      rw [if_pos (by have := hcol l; omega)]
      have := (c l).isLt
      omega
    have hmono : StrictMono c ↔ StrictMono (fun l => C3.keyS k r ((rv ∘ c) l)) := by
      simp only [hkey]
      exact ⟨fun h a b hab => h hab, fun h a b hab => h hab⟩
    by_cases hS : StrictMono c
    · have hYc' : (Matrix.of fun a l : Fin m => y (Fin.castLE hm a) ((rv ∘ c) l)).det = Yc.det := rfl
      rw [if_pos hS, if_pos (hmono.1 hS), hdet, hq, smul_smul, smul_smul, hYc']
      congr 1
      have h2 := prod_ep_sq (k := k) (r := r) c
      linear_combination ((∏ l, ep (xR k r m hm l)) * (-1) ^ m * Yc.det) * h2
    · rw [if_neg hS, if_neg (fun h => hS (hmono.2 h)), smul_zero]

/- English proof (translation)
Use `Finset.prod_congr rfl fun l _ => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem prod_ep_xR (m : ℕ) (hm : m ≤ r) :
    ∏ l : Fin m, ep (xR k r m hm l) = ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) := by
  refine Finset.prod_congr rfl fun l _ => ?_
  rfl

/- English proof (translation)
Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.
-/
theorem prod_neg_one_sq (m : ℕ) : (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun l _ => ?_
  rw [← mul_pow]
  norm_num

end mirror

def HeadAlgV : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (M : Type) [AddCommGroup M] [Module ℂ M] (k r m : ℕ) (hm : m + 2 ≤ r)
    (z' : Fin (2 * r + k + 1) → ℂ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (La : A →ₗ[ℂ] M)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (W : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (d ℓ : ℂ),
    Formalism.REAL.GlRel E → C3.RightRuleFn k r z' E La → W.det ≠ 0 → d ≠ 0 →
    (∀ (b : Fin (m + 1)) (x : A), La (E (esI k r ⟨b, by omega⟩) (esI k r ⟨m + 1, by omega⟩) * x) =
      (d * W⁻¹ b (Fin.last m)) • La x) →
    (∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), y ⟨a, by omega⟩ q =
      if h : r + k < q.val ∧ 2 * r + k - q.val < m + 1 then W a ⟨2 * r + k - q.val, h.2⟩ else 0) →
    (∀ q : Fin (2 * r + k + 1), y ⟨m + 1, by omega⟩ q = if q.val = 2 * r + k - (m + 1) then d else 0) →
    (W.det * d)⁻¹ • La (C3.AAv k r E y (m + 2) hm ℓ) =
      W.det⁻¹ • La (C3.AAv k r E y (m + 1) (by omega) ℓ *
          (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) -
        (d * W.det⁻¹) • La (C3.AAv k r E y m (by omega) ℓ)

/- English proof (translation)
Introduce `A _ _ M _ _ k r m hm z' E La y W d ℓ hG hR hW hd hL hy hyl`. Use `set xi'' : Fin r → Fin (2 * r + k + 1) → ℂ := fun a q => ep q * y a (rv q) with hxidef`. Use `set εv : Fin (m + 1) → ℂ := fun b => (-1 : ℂ) ^ (b : ℕ) with hεv`. Use `set Z'' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := W * Matrix.diagonal εv with hZdef`. Establish `hεsq : ∀ b, εv b * εv b = 1` using `by intro b; simp only [hεv]; rw [← pow_add, ← two_mul, pow_mul]; norm_num`.

Establish `hDinv : (Matrix.diagonal εv)⁻¹ = Matrix.diagonal εv`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_apply, hεsq, Matrix.one_apply]`.

Establish `hDdet : (Matrix.diagonal εv).det = ∏ b : Fin (m + 1), εv b` using `Matrix.det_diagonal`. Establish `hZdet : Z''.det = W.det * ∏ b : Fin (m + 1), εv b` using `by rw [hZdef, Matrix.det_mul, hDdet]`. Establish `hεne : (∏ b : Fin (m + 1), εv b) ≠ 0` using `Finset.prod_ne_zero_iff.2 (fun b _ => by`. Simplify using `only [hεv]; exact pow_ne_zero _ (by norm_num))`. Establish `hZ : Z''.det ≠ 0` using `by rw [hZdet]; exact mul_ne_zero hW hεne`.

Establish `hZinv : ∀ b, Z''⁻¹ b (Fin.last m) = εv b * W⁻¹ b (Fin.last m)`. Introduce `b`. Establish `hWu : IsUnit W.det` using `isUnit_iff_ne_zero.2 hW`. Establish `hDu : IsUnit (Matrix.diagonal εv).det` using `isUnit_iff_ne_zero.2 (by rw [hDdet]; exact hεne)`. Rewrite using `[hZdef, Matrix.mul_inv_rev, hDinv, Matrix.diagonal_mul]`.

Use `set c : ℂ := (-1 : ℂ) ^ (m + 1) * d with hcdef`. Use `set c' : ℂ := -((-1 : ℂ) ^ (m + 1) * d) with hc'def`. Establish `hc : c ≠ 0` using `mul_ne_zero (pow_ne_zero _ (by norm_num)) hd`. Establish `hR'' : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r → La (x * Emir E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x`. Introduce `x p q hpq hqr`.

Establish `hin : C3.InNp k r (rv q) (rv p)`. Unfold `C3.InNp`. Rewrite using `[rv_val, rv_val]`. Use linear arithmetic over natural numbers and integers. Unfold `Emir`.

Rewrite using `[mul_neg, mul_smul_comm, map_neg, map_smul, hR x _ _ hin]`. Establish `hdp : C3.dpsiP k r z' (rv q) (rv p) = if q.val = p.val + 1 then 1 else 0`. Unfold `C3.dpsiP`. Rewrite using `[rv_val, rv_val]`. Rewrite using `[if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]`.

Distinguish the cases in `h : q.val = p.val + 1`. Rewrite using `[if_pos (by omega), if_pos h]`. Rewrite using `[if_neg (by omega), if_neg h]`. Rewrite using `[hdp]`. Distinguish the cases in `h : q.val = p.val + 1`.

Simplify using `only [if_pos h, one_smul]`. Establish `: ep p * ep q = -1`. Unfold `ep`. Rewrite using `[h, pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]`. Evaluate the numerical expressions.

Rewrite using `[this, neg_one_smul, neg_neg]`. Simplify using `only [if_neg h, zero_smul, smul_zero, neg_zero]`. Establish `hepI : ∀ (b : ℕ) (hb : b < r), ep (eI k r ⟨b, hb⟩) = (-1 : ℂ) ^ b` using `by intro b hb; simp [ep, eI]`. Establish `hL'' : ∀ (b : Fin (m + 1)) (x : A), La (Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) = (c' * Z''⁻¹ b (Fin.last m)) • La x`. Introduce `b x`.

Unfold `Emir`. Rewrite using `[neg_mul, smul_mul_assoc, map_neg, map_smul, rv_eI, rv_eI, hL b x, hZinv b, smul_smul, hepI, hepI]`. Rewrite using `[← neg_smul]`. Use `congr 1`. Simplify using `only [hc'def, hεv]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hxi'' : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi'' ⟨a, by omega⟩ q = if h : q.val < m + 1 then Z'' a ⟨q, h⟩ else 0`. Introduce `a q`. Simplify using `only [hxidef]`. Rewrite using `[hy a (rv q)]`.

Distinguish the cases in `hq : q.val < m + 1`. Rewrite using `[dif_pos (by rw [rv_val]; omega), dif_pos hq, hZdef, Matrix.mul_diagonal]`. Establish `e1 : (⟨2 * r + k - (rv q).val, by rw [rv_val]; omega⟩ : Fin (m + 1)) = ⟨q.val, hq⟩` using `Fin.ext (by simp only; rw [rv_val]; omega)`. Rewrite using `[e1]`. Simplify using `only [hεv, ep]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[dif_neg (by rw [rv_val]; omega), dif_neg hq, mul_zero]`. Establish `hxl'' : ∀ q : Fin (2 * r + k + 1), xi'' ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0`. Introduce `q`. Simplify using `only [hxidef]`.

Rewrite using `[hyl (rv q)]`. Distinguish the cases in `hq : q.val = m + 1`. Rewrite using `[if_pos (by rw [rv_val]; omega), if_pos hq, hcdef]`. Simplify using `only [ep, hq]`. Rewrite using `[if_neg (by rw [rv_val]; omega), if_neg hq, mul_zero]`.

Establish `hmain` using `headAlg_gen A M k r m hm (Emir E) La xi'' Z'' c c' (-ℓ) (Emir_gl hG) hR'' hZ hc hL'' hxi'' hxl''`. Establish `hsupp : ∀ m' : ℕ, m' ≤ m + 2 → ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m' → y a p ≠ 0 → r + k < p.val`. Introduce `m' hm' a p ha hne`. Distinguish the cases in `h1 : a.val < m + 1`. Establish `e : a = ⟨((⟨a.val, h1⟩ : Fin (m + 1)) : ℕ), by omega⟩` using `Fin.ext rfl`.

Rewrite `hne` using `[e, hy]`. Use `split_ifs at hne with hc0`. Conclude with `hc0.1`. Conclude with `absurd rfl hne`. Establish `e : a = ⟨m + 1, by omega⟩` using `Fin.ext (by simp; omega)`.

Rewrite `hne` using `[e, hyl]`. Use `split_ifs at hne with hc0`. Use linear arithmetic over natural numbers and integers. Conclude with `absurd rfl hne`. Simplify using `only [hxidef] at hmain`.

Rewrite `hmain` using `[AAx_mirror E hG y (m + 2) hm ℓ (hsupp _ le_rfl), AAx_mirror E hG y (m + 1) _ ℓ (hsupp _ (by omega)), AAx_mirror E hG y m _ ℓ (hsupp _ (by omega))]`. Establish `hEd : Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) = -E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩)`. Unfold `Emir`. Rewrite using `[ep_sq, one_smul, rv_eI]`. Establish `hal : algebraMap ℂ A (-ℓ - ((m + 1 : ℕ) : ℂ)) = -algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ))`.

Rewrite using `[← map_neg]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hmain` using `[hEd, hal, ← neg_add, mul_neg, map_neg, smul_mul_assoc, map_smul, map_smul, map_smul]`. Simplify using `only [prod_ep_xR] at hmain`.

Rewrite `hmain` using `[hZdet]`. Establish `hPe : (∏ b : Fin (m + 1), εv b) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m`. Simplify using `only [hεv]`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using the standard rewrite rules.

Establish `hP1 : (∏ l : Fin (m + 1), (-1 : ℂ) ^ (l : ℕ)) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using the standard rewrite rules. Establish `hP2 : (∏ l : Fin (m + 2), (-1 : ℂ) ^ (l : ℕ)) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m * (-1) ^ (m + 1)`. Rewrite using `[Fin.prod_univ_castSucc]`.

Simplify using `only [Fin.val_castSucc, Fin.val_last]`. Rewrite using `[hP1]`. Rewrite `hmain` using `[hPe, hP2]`. Apply the tactic sequence `try rw [hP1] at hmain`. Use `set P0 := ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) with hP0`.

Use `set e := (-1 : ℂ) ^ m with he`. Establish `hP0sq : P0 * P0 = 1` using `prod_neg_one_sq m`. Establish `hesq : e * e = 1` using `by rw [he, ← mul_pow]; norm_num`. Establish `hP0ne : P0 ≠ 0` using `fun h => by rw [h, zero_mul] at hP0sq; exact zero_ne_one hP0sq`. Establish `hene : e ≠ 0` using `pow_ne_zero _ (by norm_num)`.

Establish `hm1 : (-1 : ℂ) ^ (m + 1) = -e` using `by rw [pow_succ, he]; ring`. Establish `hm2 : (-1 : ℂ) ^ (m + 2) = e` using `by rw [pow_add, he]; norm_num`. Rewrite `hmain` using `[hcdef, hc'def]`. Apply the tactic sequence `try simp only [hm1, hm2] at hmain`. Use `set V2 := La (C3.AAv k r E y (m + 2) hm ℓ) with hV2`.

Use `set V1 := La (C3.AAv k r E y (m + 1) (by omega) ℓ * (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) with hV1`. Use `set V0 := La (C3.AAv k r E y m (by omega) ℓ) with hV0`. Rewrite `hmain` using `[smul_smul, smul_neg, smul_smul, smul_smul, ← neg_smul]`. Establish `e1 : ((W.det * (P0 * e)) * (-e * d))⁻¹ * (P0 * e * -e * e) = e * (W.det * d)⁻¹`. Clear the denominators using the available nonvanishing facts.

Establish `e2 : -((W.det * (P0 * e))⁻¹ * (P0 * e * -e)) = e * W.det⁻¹`. Clear the denominators using the available nonvanishing facts. Establish `e3 : -(-e * d) * (W.det * (P0 * e))⁻¹ * (P0 * e) = e * (d * W.det⁻¹)`. Clear the denominators using the available nonvanishing facts. Rewrite `hmain` using `[e1, e2, e3, ← smul_smul, ← smul_smul, ← smul_smul, ← smul_sub]`.

Conclude with `smul_right_injective M hene hmain`.
-/
theorem _root_.Formalism.FourierDecayAlt.P.head_algebra_relations_vector : HeadAlgV := by
  intro A _ _ M _ _ k r m hm z' E La y W d ℓ hG hR hW hd hL hy hyl
  set xi'' : Fin r → Fin (2 * r + k + 1) → ℂ := fun a q => ep q * y a (rv q) with hxidef
  set εv : Fin (m + 1) → ℂ := fun b => (-1 : ℂ) ^ (b : ℕ) with hεv
  set Z'' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ := W * Matrix.diagonal εv with hZdef
  have hεsq : ∀ b, εv b * εv b = 1 := by intro b; simp only [hεv]; rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hDinv : (Matrix.diagonal εv)⁻¹ = Matrix.diagonal εv := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    ext i j; simp [Matrix.diagonal_apply, hεsq, Matrix.one_apply]
  have hDdet : (Matrix.diagonal εv).det = ∏ b : Fin (m + 1), εv b := Matrix.det_diagonal
  have hZdet : Z''.det = W.det * ∏ b : Fin (m + 1), εv b := by rw [hZdef, Matrix.det_mul, hDdet]
  have hεne : (∏ b : Fin (m + 1), εv b) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun b _ => by
    simp only [hεv]; exact pow_ne_zero _ (by norm_num))
  have hZ : Z''.det ≠ 0 := by rw [hZdet]; exact mul_ne_zero hW hεne
  have hZinv : ∀ b, Z''⁻¹ b (Fin.last m) = εv b * W⁻¹ b (Fin.last m) := by
    intro b
    have hWu : IsUnit W.det := isUnit_iff_ne_zero.2 hW
    have hDu : IsUnit (Matrix.diagonal εv).det := isUnit_iff_ne_zero.2 (by rw [hDdet]; exact hεne)
    rw [hZdef, Matrix.mul_inv_rev, hDinv, Matrix.diagonal_mul]
  set c : ℂ := (-1 : ℂ) ^ (m + 1) * d with hcdef
  set c' : ℂ := -((-1 : ℂ) ^ (m + 1) * d) with hc'def
  have hc : c ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) hd

  have hR'' : ∀ (x : A) (p q : Fin (2 * r + k + 1)), p.val < q.val → q.val < r →
      La (x * Emir E p q) = (if q.val = p.val + 1 then (1 : ℂ) else 0) • La x := by
    intro x p q hpq hqr
    have hin : C3.InNp k r (rv q) (rv p) := by
      unfold C3.InNp; rw [rv_val, rv_val]; omega
    unfold Emir
    rw [mul_neg, mul_smul_comm, map_neg, map_smul, hR x _ _ hin]
    have hdp : C3.dpsiP k r z' (rv q) (rv p) = if q.val = p.val + 1 then 1 else 0 := by
      unfold C3.dpsiP
      rw [rv_val, rv_val]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      by_cases h : q.val = p.val + 1
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
    rw [hdp]
    by_cases h : q.val = p.val + 1
    · simp only [if_pos h, one_smul]
      have : ep p * ep q = -1 := by
        unfold ep; rw [h, pow_succ, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
      rw [this, neg_one_smul, neg_neg]
    · simp only [if_neg h, zero_smul, smul_zero, neg_zero]
  have hepI : ∀ (b : ℕ) (hb : b < r), ep (eI k r ⟨b, hb⟩) = (-1 : ℂ) ^ b := by intro b hb; simp [ep, eI]
  have hL'' : ∀ (b : Fin (m + 1)) (x : A), La (Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨b, by omega⟩) * x) =
      (c' * Z''⁻¹ b (Fin.last m)) • La x := by
    intro b x
    unfold Emir
    rw [neg_mul, smul_mul_assoc, map_neg, map_smul, rv_eI, rv_eI, hL b x, hZinv b, smul_smul, hepI, hepI]
    rw [← neg_smul]
    congr 1
    simp only [hc'def, hεv]
    ring
  have hxi'' : ∀ (a : Fin (m + 1)) (q : Fin (2 * r + k + 1)), xi'' ⟨a, by omega⟩ q =
      if h : q.val < m + 1 then Z'' a ⟨q, h⟩ else 0 := by
    intro a q
    simp only [hxidef]
    rw [hy a (rv q)]
    by_cases hq : q.val < m + 1
    · rw [dif_pos (by rw [rv_val]; omega), dif_pos hq, hZdef, Matrix.mul_diagonal]
      have e1 : (⟨2 * r + k - (rv q).val, by rw [rv_val]; omega⟩ : Fin (m + 1)) = ⟨q.val, hq⟩ :=
        Fin.ext (by simp only; rw [rv_val]; omega)
      rw [e1]
      simp only [hεv, ep]
      ring
    · rw [dif_neg (by rw [rv_val]; omega), dif_neg hq, mul_zero]
  have hxl'' : ∀ q : Fin (2 * r + k + 1), xi'' ⟨m + 1, by omega⟩ q = if q.val = m + 1 then c else 0 := by
    intro q
    simp only [hxidef]
    rw [hyl (rv q)]
    by_cases hq : q.val = m + 1
    · rw [if_pos (by rw [rv_val]; omega), if_pos hq, hcdef]
      simp only [ep, hq]
    · rw [if_neg (by rw [rv_val]; omega), if_neg hq, mul_zero]
  have hmain := headAlg_gen A M k r m hm (Emir E) La xi'' Z'' c c' (-ℓ) (Emir_gl hG) hR'' hZ hc hL'' hxi'' hxl''
  have hsupp : ∀ m' : ℕ, m' ≤ m + 2 → ∀ (a : Fin r) (p : Fin (2 * r + k + 1)), a.val < m' → y a p ≠ 0 →
      r + k < p.val := by
    intro m' hm' a p ha hne
    by_cases h1 : a.val < m + 1
    · have e : a = ⟨((⟨a.val, h1⟩ : Fin (m + 1)) : ℕ), by omega⟩ := Fin.ext rfl
      rw [e, hy] at hne
      split_ifs at hne with hc0
      · exact hc0.1
      · exact absurd rfl hne
    · have e : a = ⟨m + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [e, hyl] at hne
      split_ifs at hne with hc0
      · omega
      · exact absurd rfl hne
  simp only [hxidef] at hmain
  rw [AAx_mirror E hG y (m + 2) hm ℓ (hsupp _ le_rfl), AAx_mirror E hG y (m + 1) _ ℓ (hsupp _ (by omega)),
    AAx_mirror E hG y m _ ℓ (hsupp _ (by omega))] at hmain
  have hEd : Emir E (eI k r ⟨m + 1, by omega⟩) (eI k r ⟨m + 1, by omega⟩) =
      -E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩) := by
    unfold Emir; rw [ep_sq, one_smul, rv_eI]
  have hal : algebraMap ℂ A (-ℓ - ((m + 1 : ℕ) : ℂ)) = -algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) := by
    rw [← map_neg]; congr 1; ring
  rw [hEd, hal, ← neg_add, mul_neg, map_neg, smul_mul_assoc, map_smul, map_smul, map_smul] at hmain
  simp only [prod_ep_xR] at hmain
  rw [hZdet] at hmain
  have hPe : (∏ b : Fin (m + 1), εv b) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m := by
    simp only [hεv]; rw [Fin.prod_univ_castSucc]; simp
  have hP1 : (∏ l : Fin (m + 1), (-1 : ℂ) ^ (l : ℕ)) = (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m := by
    rw [Fin.prod_univ_castSucc]; simp
  have hP2 : (∏ l : Fin (m + 2), (-1 : ℂ) ^ (l : ℕ)) =
      (∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ)) * (-1) ^ m * (-1) ^ (m + 1) := by
    rw [Fin.prod_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]; rw [hP1]
  rw [hPe, hP2] at hmain
  try rw [hP1] at hmain
  set P0 := ∏ l : Fin m, (-1 : ℂ) ^ (l : ℕ) with hP0
  set e := (-1 : ℂ) ^ m with he
  have hP0sq : P0 * P0 = 1 := prod_neg_one_sq m
  have hesq : e * e = 1 := by rw [he, ← mul_pow]; norm_num
  have hP0ne : P0 ≠ 0 := fun h => by rw [h, zero_mul] at hP0sq; exact zero_ne_one hP0sq
  have hene : e ≠ 0 := pow_ne_zero _ (by norm_num)
  have hm1 : (-1 : ℂ) ^ (m + 1) = -e := by rw [pow_succ, he]; ring
  have hm2 : (-1 : ℂ) ^ (m + 2) = e := by rw [pow_add, he]; norm_num
  rw [hcdef, hc'def] at hmain
  try simp only [hm1, hm2] at hmain
  set V2 := La (C3.AAv k r E y (m + 2) hm ℓ) with hV2
  set V1 := La (C3.AAv k r E y (m + 1) (by omega) ℓ *
    (algebraMap ℂ A (ℓ + ((m + 1 : ℕ) : ℂ)) + E (esI k r ⟨m + 1, by omega⟩) (esI k r ⟨m + 1, by omega⟩))) with hV1
  set V0 := La (C3.AAv k r E y m (by omega) ℓ) with hV0
  rw [smul_smul, smul_neg, smul_smul, smul_smul, ← neg_smul] at hmain
  have e1 : ((W.det * (P0 * e)) * (-e * d))⁻¹ * (P0 * e * -e * e) = e * (W.det * d)⁻¹ := by
    field_simp
  have e2 : -((W.det * (P0 * e))⁻¹ * (P0 * e * -e)) = e * W.det⁻¹ := by
    field_simp
  have e3 : -(-e * d) * (W.det * (P0 * e))⁻¹ * (P0 * e) = e * (d * W.det⁻¹) := by
    field_simp
  rw [e1, e2, e3, ← smul_smul, ← smul_smul, ← smul_smul, ← smul_sub] at hmain
  exact smul_right_injective M hene hmain

end Formalism.FourierDecayAlt.P.PBG
