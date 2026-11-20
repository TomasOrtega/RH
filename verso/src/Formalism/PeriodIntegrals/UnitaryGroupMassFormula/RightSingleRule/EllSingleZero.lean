import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.PatEntryZero

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace Formalism.FourierDecayAlt.Q.QRR

variable {k r : ℕ}

/- English proof (translation)
Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply]`. Simplify using `[Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]`.
-/
lemma mulVec_single' (a b : Fin (2 * r + k + 1)) (c : ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (i : Fin (2 * r + k + 1)) : (Matrix.single a b c *ᵥ z) i = if i = a then c * z b else 0 := by
  by_cases h : i = a
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h, Ne.symm h]

/- English proof (translation)
Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a' _`. Use `split_ifs with h`. Rewrite using `[Matrix.single_apply, if_neg]`.

Introduce and unpack `⟨-, hb'⟩`. Establish `h'` using `congrArg Fin.val hb'`. Simplify using `only [eI] at h'`. Use linear arithmetic over natural numbers and integers. Rewrite using `[mulVec_single', hzb]`.

Simplify using the standard rewrite rules.
-/
lemma ell_single_zero (z : Fin (2 * r + k + 1) → ℂ) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (hb : r ≤ b.val) (hzb : z b = 0) : ell k r z (Matrix.single a b c) = 0 := by
  unfold ell
  apply Finset.sum_eq_zero
  intro a' _
  split_ifs with h
  · rw [Matrix.single_apply, if_neg]
    rintro ⟨-, hb'⟩
    have h' := congrArg Fin.val hb'
    simp only [eI] at h'
    omega
  · rw [mulVec_single', hzb]
    simp

/- English proof (translation)
Unfold `ell`. Rewrite using `[Finset.sum_eq_single l]`. Distinguish the cases in `h : l.val + 1 < r`. Rewrite using `[dif_pos h, dif_pos h, Matrix.single_apply]`. Simplify using the standard rewrite rules.

Rewrite using `[dif_neg h, dif_neg h, mulVec_single']`. Simplify using the standard rewrite rules. Introduce `a' _ ha'`. Establish `hne : eI k r l ≠ eI k r a'` using `fun h => ha' (Fin.ext (by`. Establish `h'` using `congrArg Fin.val h`.

Simplify using `only [eI] at h'`. Use the proof step `omega))`. Distinguish the cases in `h : a'.val + 1 < r`. Rewrite using `[dif_pos h, Matrix.single_apply, if_neg]`. Introduce and unpack `⟨h1, -⟩`.

Conclude with `hne h1`. Rewrite using `[dif_neg h, mulVec_single', if_neg (Ne.symm hne)]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ l) h`.
-/
lemma ell_single_row (z : Fin (2 * r + k + 1) → ℂ) (l : Fin r) (b : Fin (2 * r + k + 1)) (c : ℂ) :
    ell k r z (Matrix.single (eI k r l) b c) =
      if h : l.val + 1 < r then (if b = eI k r ⟨l.val + 1, h⟩ then c else 0) else c * z b := by
  unfold ell
  rw [Finset.sum_eq_single l]
  · by_cases h : l.val + 1 < r
    · rw [dif_pos h, dif_pos h, Matrix.single_apply]
      simp
    · rw [dif_neg h, dif_neg h, mulVec_single']
      simp
  · intro a' _ ha'
    have hne : eI k r l ≠ eI k r a' := fun h => ha' (Fin.ext (by
      have h' := congrArg Fin.val h
      simp only [eI] at h'
      omega))
    by_cases h : a'.val + 1 < r
    · rw [dif_pos h, Matrix.single_apply, if_neg]
      rintro ⟨h1, -⟩
      exact hne h1
    · rw [dif_neg h, mulVec_single', if_neg (Ne.symm hne)]
  · intro h
    exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Establish `hi` using `i.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [tau_val_lemma]`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private lemma tau_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.tau k r (WeylGroupFacts.tau k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [tau_val_lemma]
  split_ifs <;> omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Unfold `WeylGroupFacts.sgn`. Simplify using `only [tau_val_lemma]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
private lemma sgn_tau_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r i) = WeylGroupFacts.sgn k r i := by
  have hi := i.isLt
  unfold WeylGroupFacts.sgn
  simp only [tau_val_lemma]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Unfold `Hpk WeylGroupFacts.sgn`. Simplify using `only [Fin.ext_iff, tau_val_lemma]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega | norm_num`.
-/
private lemma hpk_eq_lemma (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = WeylGroupFacts.tau k r i then WeylGroupFacts.sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk WeylGroupFacts.sgn
  simp only [Fin.ext_iff, tau_val_lemma]
  split_ifs <;> first | rfl | omega | norm_num

/- English proof (translation)
Rewrite using `[hpk_eq_lemma]`. Distinguish the cases in `h : x = WeylGroupFacts.tau k r y`. Substitute `h` using the available equality. Simplify using `[tau_tau_lemma, sgn_tau_lemma]`. Rewrite using `[if_neg h, if_neg]`.

Introduce `h'`. Apply `h` to reduce the goal to its premises. Rewrite using `[h', tau_tau_lemma]`.
-/
private lemma hpk_col_lemma (x y : Fin (2 * r + k + 1)) :
    Hpk k r x y = if x = WeylGroupFacts.tau k r y then WeylGroupFacts.sgn k r y else 0 := by
  rw [hpk_eq_lemma]
  by_cases h : x = WeylGroupFacts.tau k r y
  · subst h
    simp [tau_tau_lemma, sgn_tau_lemma]
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    rw [h', tau_tau_lemma]

/- English proof (translation)
Unfold `WeylGroupFacts.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma, sgn_tau_lemma]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[sgn_sq_lemma]`. Simplify using `[h, Ne.symm h]`.
-/
private lemma hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [hpk_eq_lemma, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma, sgn_tau_lemma]
  by_cases h : i = j
  · subst h
    simp [sgn_sq_lemma]
  · simp [h, Ne.symm h]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv hpk_sq_lemma`.
-/
private lemma hpk_inv_lemma : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq_lemma

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]`. Distinguish the cases in `h : a = y ∧ b = x`. Rewrite using `[if_pos h, if_pos ⟨h.2, h.1⟩]`. Rewrite using `[if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]`.
-/
private lemma single_ct_lemma (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases h : a = y ∧ b = x
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), star_zero]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private lemma conj_single_lemma (A B : Mx k r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (p q : Fin (2 * r + k + 1)) : (A * Matrix.single a b c * B) p q = A p a * c * B b q := by
  simp only [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_ite, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Unfold `dag`. Rewrite using `[hpk_inv_lemma, single_ct_lemma]`. Use extensionality with `p q`. Rewrite using `[conj_single_lemma, hpk_eq_lemma, hpk_eq_lemma, Matrix.single_apply]`. Distinguish the cases in `hp : p = WeylGroupFacts.tau k r b`.

Substitute `hp` using the available equality. Distinguish the cases in `hq : q = WeylGroupFacts.tau k r a`. Substitute `hq` using the available equality. Simplify using `[tau_tau_lemma, sgn_tau_lemma]`. Simplify using `[hq, Ne.symm hq]`.

Establish `hb : b ≠ WeylGroupFacts.tau k r p` using `fun h => hp (by rw [h, tau_tau_lemma])`. Simplify using `[hb, Ne.symm hp]`.
-/
lemma dag_single (a b : Fin (2 * r + k + 1)) (c : ℂ) :
    dag k r (Matrix.single a b c) = Matrix.single (WeylGroupFacts.tau k r b) (WeylGroupFacts.tau k r a)
      (WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r b) * star c * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r a)) := by
  unfold dag
  rw [hpk_inv_lemma, single_ct_lemma]
  ext p q
  rw [conj_single_lemma, hpk_eq_lemma, hpk_eq_lemma, Matrix.single_apply]
  by_cases hp : p = WeylGroupFacts.tau k r b
  · subst hp
    by_cases hq : q = WeylGroupFacts.tau k r a
    · subst hq
      simp [tau_tau_lemma, sgn_tau_lemma]
    · simp [hq, Ne.symm hq]
  · have hb : b ≠ WeylGroupFacts.tau k r p := fun h => hp (by rw [h, tau_tau_lemma])
    simp [hb, Ne.symm hp]

/- English proof (translation)
Introduce `i j hij`. Rewrite `hij` using `[Matrix.single_apply]`. Use `split_ifs at hij with h'`. Take `⟨rfl, rfl⟩` from `h'`. Conclude with `h`.

Conclude with `absurd rfl hij`.
-/
lemma pat_single (l : Fin r) (a b : Fin (2 * r + k + 1)) (c : ℂ)
    (h : (a.val = l.val ∧ l.val < b.val ∧ b.val ≤ 2 * r + k - l.val) ∨
      (b.val = 2 * r + k - l.val ∧ l.val ≤ a.val ∧ a.val < 2 * r + k - l.val)) :
    Pat k r l (Matrix.single a b c) := by
  intro i j hij
  rw [Matrix.single_apply] at hij
  split_ifs at hij with h'
  · obtain ⟨rfl, rfl⟩ := h'
    exact h
  · exact absurd rfl hij

/- English proof (translation)
Establish `hj : j.val < 2 * (r - (l.val + 1)) + k + 1` using `j.isLt`. Establish `hl` using `l.isLt`. Use `⟨rfl, ?_⟩` and prove the remaining obligations. Use `show j.val + (l.val + 1) < 2 * r + k - l.val`. Use linear arithmetic over natural numbers and integers.
-/
lemma posL_val (l : Fin r) (j : Fin (mdim k r l.succ)) :
    (posL k r l.succ j).val = j.val + (l.val + 1) ∧ j.val + (l.val + 1) < 2 * r + k - l.val := by
  have hj : j.val < 2 * (r - (l.val + 1)) + k + 1 := j.isLt
  have hl := l.isLt
  refine ⟨rfl, ?_⟩
  show j.val + (l.val + 1) < 2 * r + k - l.val
  omega

/- English proof (translation)
Establish `hl` using `l.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[tau_val_lemma]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `absurd (Or.inl hl) h`.
-/
lemma tau_eI (l : Fin r) : WeylGroupFacts.tau k r (eI k r l) = esI k r l := by
  have hl := l.isLt
  apply Fin.ext
  rw [tau_val_lemma]
  split_ifs with h
  · rfl
  · exact absurd (Or.inl hl) h

/- English proof (translation)
Establish `hl` using `l.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[tau_val_lemma]`. Use `split_ifs with h`. Use `show 2 * r + k - (2 * r + k - l.val) = l.val`.

Use linear arithmetic over natural numbers and integers. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Use `right`. Use `show r + k < 2 * r + k - l.val`.

Use linear arithmetic over natural numbers and integers.
-/
lemma tau_esI (l : Fin r) : WeylGroupFacts.tau k r (esI k r l) = eI k r l := by
  have hl := l.isLt
  apply Fin.ext
  rw [tau_val_lemma]
  split_ifs with h
  · show 2 * r + k - (2 * r + k - l.val) = l.val
    omega
  · exfalso
    apply h
    right
    show r + k < 2 * r + k - l.val
    omega

/- English proof (translation)
Establish `hl` using `l.isLt`. Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_esI (l : Fin r) : WeylGroupFacts.sgn k r (esI k r l) = 1 := by
  have hl := l.isLt
  unfold WeylGroupFacts.sgn
  rw [if_neg]
  simp only [esI]
  omega

/- English proof (translation)
Establish `hl` using `l.isLt`. Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Simplify using `only [eI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_eI (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  have hl := l.isLt
  unfold WeylGroupFacts.sgn
  rw [if_neg]
  simp only [eI]
  omega

/- English proof (translation)
Unfold `WeylGroupFacts.sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma star_sgn (i : Fin (2 * r + k + 1)) : star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> simp

/- English proof (translation)
Establish `hl` using `l.isLt`. Conclude with `hz _ (Or.inr (show r + k < 2 * r + k - l.val by omega))`.
-/
lemma esI_zero (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) : z (esI k r l) = 0 := by
  have hl := l.isLt
  exact hz _ (Or.inr (show r + k < 2 * r + k - l.val by omega))

/- English proof (translation)
Establish `hl` using `l.isLt`. Use `show r ≤ 2 * r + k - l.val`. Use linear arithmetic over natural numbers and integers.
-/
lemma esI_ge (l : Fin r) : r ≤ (esI k r l).val := by
  have hl := l.isLt
  show r ≤ 2 * r + k - l.val
  omega

/- English proof (translation)
Unfold `herm`. Simplify using `only [dotProduct, Matrix.mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, hpk_col_lemma, Pi.star_apply]`.
-/
lemma herm_bvec_left (x : Fin (2 * r + k + 1) → ℂ) (v : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec v) x = star (x (WeylGroupFacts.tau k r v)) * WeylGroupFacts.sgn k r v := by
  unfold herm
  simp only [dotProduct, Matrix.mulVec, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hpk_col_lemma, Pi.star_apply]

/- English proof (translation)
Rewrite using `[dag_single, tau_eI, ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero, add_zero, ell_single_row]`. Unfold `xv fvec`. Distinguish the cases in `h : l.val + 1 < r`. Rewrite using `[dif_pos h, dif_pos (show l.succ.val < r from h)]`. Simplify using `only [bvec, Pi.single_apply]`.

Both sides reduce to the same expression. Rewrite using `[dif_neg h, dif_neg (show ¬ l.succ.val < r from h), one_mul]`.
-/
lemma val_ev (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (eI k r l) (posL k r l.succ j) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (posL k r l.succ j) 1))) = xv k r z l.succ j := by
  rw [dag_single, tau_eI, ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero, add_zero,
    ell_single_row]
  unfold xv fvec
  by_cases h : l.val + 1 < r
  · rw [dif_pos h, dif_pos (show l.succ.val < r from h)]
    simp only [bvec, Pi.single_apply]
    rfl
  · rw [dif_neg h, dif_neg (show ¬ l.succ.val < r from h), one_mul]

/- English proof (translation)
Establish `hc : WeylGroupFacts.sgn k r (eI k r l) * star (1 : ℂ) * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r (posL k r l.succ j)) = WeylGroupFacts.sgn k r (posL k r l.succ j)`. Rewrite using `[sgn_eI, star_one, one_mul, one_mul, sgn_tau_lemma]`. Rewrite using `[ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_esI, hc, ell_single_row]`. Unfold `xbv`. Rewrite using `[herm_bvec_left]`.

Unfold `fvec`. Distinguish the cases in `h : l.val + 1 < r`. Rewrite using `[dif_pos h, dif_pos (show l.succ.val < r from h)]`. Simplify using `only [bvec, Pi.single_apply]`. Use `split_ifs with h1 h2 h3`.

Apply the tactic sequence `all_goals first`. Consider the case `exact absurd h1 h2`. Consider the case `exact absurd h3 h1`. Consider the case `(rw [star_one, one_mul, star_sgn])`. Consider the case `simp`.

Rewrite using `[dif_neg h, dif_neg (show ¬ l.succ.val < r from h), star_mul', star_sgn, mul_comm]`.
-/
lemma val_ve (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) (j : Fin (mdim k r l.succ)) :
    ell k r z (Matrix.single (posL k r l.succ j) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (posL k r l.succ j) (esI k r l) 1))) = xbv k r z l.succ j := by
  have hc : WeylGroupFacts.sgn k r (eI k r l) * star (1 : ℂ) * WeylGroupFacts.sgn k r (WeylGroupFacts.tau k r (posL k r l.succ j)) =
      WeylGroupFacts.sgn k r (posL k r l.succ j) := by
    rw [sgn_eI, star_one, one_mul, one_mul, sgn_tau_lemma]
  rw [ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_esI, hc,
    ell_single_row]
  unfold xbv
  rw [herm_bvec_left]
  unfold fvec
  by_cases h : l.val + 1 < r
  · rw [dif_pos h, dif_pos (show l.succ.val < r from h)]
    simp only [bvec, Pi.single_apply]
    split_ifs with h1 h2 h3
    all_goals first
      | exact absurd h1 h2
      | exact absurd h3 h1
      | (rw [star_one, one_mul, star_sgn])
      | simp
  · rw [dif_neg h, dif_neg (show ¬ l.succ.val < r from h), star_mul', star_sgn, mul_comm]

/- English proof (translation)
Rewrite using `[ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_eI, ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero]`.
-/
lemma val_ees (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (l : Fin r) :
    ell k r z (Matrix.single (eI k r l) (esI k r l) 1) +
      star (ell k r z (dag k r (Matrix.single (eI k r l) (esI k r l) 1))) = 0 := by
  rw [ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), zero_add, dag_single, tau_eI,
    ell_single_zero z _ _ _ (esI_ge l) (esI_zero z hz l), star_zero]

/- English proof (translation)
Establish `h` using `posL_val (k := k) l j`. Apply `pat_single` to reduce the goal to its premises. Use `left`. Conclude with `⟨rfl, by omega, by omega⟩`.
-/
lemma pat_ev (l : Fin r) (j : Fin (mdim k r l.succ)) :
    Pat k r l (Matrix.single (eI k r l) (posL k r l.succ j) 1) := by
  have h := posL_val (k := k) l j
  apply pat_single
  left
  exact ⟨rfl, by omega, by omega⟩

/- English proof (translation)
Establish `h` using `posL_val (k := k) l j`. Establish `hl` using `l.isLt`. Apply `pat_single` to reduce the goal to its premises. Use `right`. Conclude with `⟨rfl, by omega, by omega⟩`.
-/
lemma pat_ve (l : Fin r) (j : Fin (mdim k r l.succ)) :
    Pat k r l (Matrix.single (posL k r l.succ j) (esI k r l) 1) := by
  have h := posL_val (k := k) l j
  have hl := l.isLt
  apply pat_single
  right
  exact ⟨rfl, by omega, by omega⟩

/- English proof (translation)
Establish `hl` using `l.isLt`. Apply `pat_single` to reduce the goal to its premises. Use `left`. Conclude with `⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩`.
-/
lemma pat_ees (l : Fin r) : Pat k r l (Matrix.single (eI k r l) (esI k r l) 1) := by
  have hl := l.isLt
  apply pat_single
  left
  exact ⟨rfl, show l.val < 2 * r + k - l.val by omega, le_refl _⟩

/- English proof (translation)
Introduce `E _ _ k r z' l D f hz _ _ hR g hg`. Use `⟨fun j => ?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Use `show RdV _ f g + Complex.I • RdV _ f g = _`. Rewrite using `[lam z' hz l D f hR g hg _ (pat_ev l j), val_ev z' hz l j]`. Use `show RdV _ f g + Complex.I • RdV _ f g = _`.

Rewrite using `[lam z' hz l D f hR g hg _ (pat_ve l j), val_ve z' hz l j]`. Use `show RdV _ f g + Complex.I • RdV _ f g = _`. Rewrite using `[lam z' hz l D f hR g hg _ (pat_ees l), val_ees z' hz l, zero_smul]`.
-/
theorem ruleRight_main : RuleRight := by
  intro E _ _ k r z' l D f hz _ _ hR g hg
  refine ⟨fun j => ?_, fun j => ?_, ?_⟩
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ev l j), val_ev z' hz l j]
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ve l j), val_ve z' hz l j]
  · show RdV _ f g + Complex.I • RdV _ f g = _
    rw [lam z' hz l D f hR g hg _ (pat_ees l), val_ees z' hz l, zero_smul]

end Formalism.FourierDecayAlt.Q.QRR
