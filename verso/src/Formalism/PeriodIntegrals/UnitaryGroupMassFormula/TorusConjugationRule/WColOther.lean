import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.QnRT

variable {k r : ℕ}

/- English proof (translation)
Introduce `h`. Establish `hl` using `l.isLt`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [eI, esI] at h'`. Use linear arithmetic over natural numbers and integers.
-/
lemma e_ne_es (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h
  have hl := l.isLt
  have h' := congrArg Fin.val h
  simp only [eI, esI] at h'
  omega

/- English proof (translation)
The claim follows from `(e_ne_es l).symm`.
-/
lemma es_ne_e (l : Fin r) : esI k r l ≠ eI k r l := (e_ne_es l).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma tau_val_lemma (i : Fin (2 * r + k + 1)) :
    (WeylGroupFacts.tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Establish `hl` using `l.isLt`. Apply `Fin.ext` to reduce the goal to its premises. Rewrite using `[tau_val_lemma]`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `absurd (Or.inl hl) h`.
-/
lemma tau_e (l : Fin r) : WeylGroupFacts.tau k r (eI k r l) = esI k r l := by
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
lemma tau_es (l : Fin r) : WeylGroupFacts.tau k r (esI k r l) = eI k r l := by
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
Establish `hl` using `l.isLt`. Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Simplify using `only [eI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_e (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  have hl := l.isLt
  unfold WeylGroupFacts.sgn
  rw [if_neg]
  simp only [eI]
  omega

/- English proof (translation)
Establish `hl` using `l.isLt`. Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Simplify using `only [esI]`. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_es (l : Fin r) : WeylGroupFacts.sgn k r (esI k r l) = 1 := by
  have hl := l.isLt
  unfold WeylGroupFacts.sgn
  rw [if_neg]
  simp only [esI]
  omega

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `w1`. Distinguish the cases in `h : s = esI k r l`. Substitute `h` using the available equality. Simplify using `[hne, hne.symm]`.

Simplify using `[h, hne, hne.symm]`.
-/
lemma w_col_e (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (eI k r l) = if s = esI k r l then a else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : s = esI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `w1`. Distinguish the cases in `h : s = eI k r l`. Substitute `h` using the available equality. Simplify using `[hne, hne.symm]`.

Simplify using `[h, hne, hne.symm]`.
-/
lemma w_col_es (l : Fin r) (a : ℂ) (s : Fin (2 * r + k + 1)) :
    w1 k r l a s (esI k r l) = if s = eI k r l then (star a)⁻¹ else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : s = eI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]

/- English proof (translation)
Unfold `w1`. Distinguish the cases in `h : s = p`. Substitute `h` using the available equality. Simplify using `[hp1, hp2]`. Simplify using `[h, hp1, hp2]`.
-/
lemma w_col_other (l : Fin r) (a : ℂ) (s p : Fin (2 * r + k + 1)) (hp1 : p ≠ eI k r l)
    (hp2 : p ≠ esI k r l) : w1 k r l a s p = if s = p then 1 else 0 := by
  unfold w1
  by_cases h : s = p
  · subst h
    simp [hp1, hp2]
  · simp [h, hp1, hp2]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `w1`. Distinguish the cases in `h : q = esI k r l`. Substitute `h` using the available equality. Simplify using `[hne, hne.symm]`.

Simplify using `[h, hne, hne.symm]`.
-/
lemma w_row_e (l : Fin r) (a : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l a (eI k r l) q = if q = esI k r l then (star a)⁻¹ else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : q = esI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `w1`. Distinguish the cases in `h : q = eI k r l`. Substitute `h` using the available equality. Simplify using `[hne, hne.symm]`.

Simplify using `[h, hne, hne.symm]`.
-/
lemma w_row_es (l : Fin r) (a : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l a (esI k r l) q = if q = eI k r l then a else 0 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold w1
  by_cases h : q = eI k r l
  · subst h
    simp [hne, hne.symm]
  · simp [h, hne, hne.symm]

/- English proof (translation)
Unfold `w1`. Distinguish the cases in `h : s = q`. Substitute `h` using the available equality. Simplify using `[hs1, hs2]`. Simplify using `[h, hs1, hs2]`.
-/
lemma w_row_other (l : Fin r) (a : ℂ) (s q : Fin (2 * r + k + 1)) (hs1 : s ≠ eI k r l)
    (hs2 : s ≠ esI k r l) : w1 k r l a s q = if s = q then 1 else 0 := by
  unfold w1
  by_cases h : s = q
  · subst h
    simp [hs1, hs2]
  · simp [h, hs1, hs2]

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
Unfold `WeylGroupFacts.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `WeylGroupFacts.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma sgn_ne_zero' (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i ≠ 0 := by
  unfold WeylGroupFacts.sgn
  split_ifs <;> norm_num

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
Establish `h` using `congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_ne_zero.mpr fun h0 => by`. Rewrite `h` using `[h0, zero_mul]`. Conclude with `zero_ne_one h`.
-/
private lemma isUnit_det_Hpk' : IsUnit (Hpk k r).det := by
  have h := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_iff_ne_zero.mpr fun h0 => by
    rw [h0, zero_mul] at h
    exact zero_ne_one h

/- English proof (translation)
Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.conjTranspose_apply, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private lemma conjTranspose_mul_Hpk_mul_apply (A : Mx k r) (p q : Fin (2 * r + k + 1)) :
    (Aᴴ * Hpk k r * A) p q = ∑ y, star (A (WeylGroupFacts.tau k r y) p) * WeylGroupFacts.sgn k r y * A y q := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, hpk_col_lemma, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `hh' : hᴴ * Hpk k r * h = Hpk k r` using `hh`. Use `show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hg', hh']`.
-/
private lemma mul_mem_uh {g h : Mx k r} (hg : g ∈ UH (Hpk k r)) (hh : h ∈ UH (Hpk k r)) :
    g * h ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hh' : hᴴ * Hpk k r * h = Hpk k r := hh
  show (g * h)ᴴ * Hpk k r * (g * h) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc hᴴ * gᴴ * Hpk k r * (g * h) = hᴴ * (gᴴ * Hpk k r * g) * h := by
        simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hh']

/- English proof (translation)
Use `show (w1 k r l a)ᴴ * Hpk k r * w1 k r l a = Hpk k r`. Use extensionality with `p q`. Rewrite using `[conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma]`. Distinguish the cases in `hq1 : q = eI k r l`. Substitute `hq1` using the available equality.

Simplify using `only [w_col_e, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_es, sgn_es, w_row_e, tau_e, sgn_e]`. Distinguish the cases in `hp : p = esI k r l`. Rewrite using `[if_pos hp, if_pos hp, mul_one] first`. Consider the case `rw [star_inv₀, star_star, inv_mul_cancel₀ ha]`. Consider the case `rw [star_inv', star_star, inv_mul_cancel₀ ha]`.

Simplify using `[hp]`. Distinguish the cases in `hq2 : q = esI k r l`. Substitute `hq2` using the available equality. Simplify using `only [w_col_es, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_e, sgn_e, w_row_es, tau_es, sgn_es]`. Distinguish the cases in `hp : p = eI k r l`.

Rewrite using `[if_pos hp, if_pos hp, mul_one]`. Conclude with `mul_inv_cancel₀ (star_ne_zero.mpr ha)`. Simplify using `[hp]`. Establish `hcol : ∀ x, w1 k r l a x q = if x = q then 1 else 0` using `fun x => w_col_other l a x q hq1 hq2`. Simplify using `only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Establish `ht1 : WeylGroupFacts.tau k r q ≠ eI k r l` using `fun h => hq2 (by rw [← tau_tau_lemma q, h, tau_e])`. Establish `ht2 : WeylGroupFacts.tau k r q ≠ esI k r l` using `fun h => hq1 (by rw [← tau_tau_lemma q, h, tau_es])`. Rewrite using `[w_row_other l a _ p ht1 ht2]`. Distinguish the cases in `h : p = WeylGroupFacts.tau k r q`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Establish `h' : WeylGroupFacts.tau k r q ≠ p` using `Ne.symm h`. Simplify using `[h, h']`.
-/
lemma w_uh (l : Fin r) (a : ℂ) (ha : a ≠ 0) : w1 k r l a ∈ UH (Hpk k r) := by
  show (w1 k r l a)ᴴ * Hpk k r * w1 k r l a = Hpk k r
  ext p q
  rw [conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma]
  by_cases hq1 : q = eI k r l
  · subst hq1
    simp only [w_col_e, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_es, sgn_es, w_row_e, tau_e, sgn_e]
    by_cases hp : p = esI k r l
    · rw [if_pos hp, if_pos hp, mul_one]
      first
        | rw [star_inv₀, star_star, inv_mul_cancel₀ ha]
        | rw [star_inv', star_star, inv_mul_cancel₀ ha]
    · simp [hp]
  by_cases hq2 : q = esI k r l
  · subst hq2
    simp only [w_col_es, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_e, sgn_e, w_row_es, tau_es, sgn_es]
    by_cases hp : p = eI k r l
    · rw [if_pos hp, if_pos hp, mul_one]
      exact mul_inv_cancel₀ (star_ne_zero.mpr ha)
    · simp [hp]
  have hcol : ∀ x, w1 k r l a x q = if x = q then 1 else 0 := fun x => w_col_other l a x q hq1 hq2
  simp only [hcol, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have ht1 : WeylGroupFacts.tau k r q ≠ eI k r l := fun h => hq2 (by rw [← tau_tau_lemma q, h, tau_e])
  have ht2 : WeylGroupFacts.tau k r q ≠ esI k r l := fun h => hq1 (by rw [← tau_tau_lemma q, h, tau_es])
  rw [w_row_other l a _ p ht1 ht2]
  by_cases h : p = WeylGroupFacts.tau k r q
  · subst h
    simp
  · have h' : WeylGroupFacts.tau k r q ≠ p := Ne.symm h
    simp [h, h']

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `w_col_other l a p x h1 h2`.
-/
lemma w_fix (l : Fin r) (a : ℂ) (x : Fin (2 * r + k + 1)) (h1 : x ≠ eI k r l) (h2 : x ≠ esI k r l) :
    w1 k r l a *ᵥ bvec x = bvec x := by
  funext p
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact w_col_other l a p x h1 h2

/- English proof (translation)
Establish `hl` using `l.isLt`. Simplify using `only [Glev, Set.mem_setOf_eq] at hg ⊢`. Take `⟨hU, hfix⟩` from `hg`. Use `⟨mul_mem_uh (w_uh l a ha) hU, fun b hb => ?_⟩` and prove the remaining obligations. Establish `hbl` using `b.isLt`.

Simplify using `only [Fin.coe_castSucc] at hb`. Establish `hfb` using `hfix b (by simp; omega)`. Establish `h1 : eI k r b ≠ eI k r l` using `fun h => by`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [eI] at h'`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : eI k r b ≠ esI k r l` using `fun h => by`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [eI, esI] at h'`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : esI k r b ≠ eI k r l` using `fun h => by`. Establish `h'` using `congrArg Fin.val h`. Simplify using `only [eI, esI] at h'`. Use linear arithmetic over natural numbers and integers. Establish `h4 : esI k r b ≠ esI k r l` using `fun h => by`.

Establish `h'` using `congrArg Fin.val h`. Simplify using `only [esI] at h'`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Matrix.mulVec_mulVec, hfb.1, w_fix l a _ h1 h2]`.

Rewrite using `[← Matrix.mulVec_mulVec, hfb.2, w_fix l a _ h3 h4]`.
-/
lemma w_mul_mem (l : Fin r) (a : ℂ) (ha : a ≠ 0) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l a * g₁ ∈ Glev k r l.castSucc := by
  have hl := l.isLt
  simp only [Glev, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hU, hfix⟩ := hg
  refine ⟨mul_mem_uh (w_uh l a ha) hU, fun b hb => ?_⟩
  have hbl := b.isLt
  simp only [Fin.coe_castSucc] at hb
  have hfb := hfix b (by simp; omega)
  have h1 : eI k r b ≠ eI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI] at h'
    omega
  have h2 : eI k r b ≠ esI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    omega
  have h3 : esI k r b ≠ eI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [eI, esI] at h'
    omega
  have h4 : esI k r b ≠ esI k r l := fun h => by
    have h' := congrArg Fin.val h
    simp only [esI] at h'
    omega
  constructor
  · rw [← Matrix.mulVec_mulVec, hfb.1, w_fix l a _ h1 h2]
  · rw [← Matrix.mulVec_mulVec, hfb.2, w_fix l a _ h3 h4]

def dg (l : Fin r) (u v : ℂ) : Mx k r :=
  diagonal (fun p => if p = eI k r l then u else if p = esI k r l then v else 1)

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `dg`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_diagonal]`. Distinguish the cases in `hq1 : q = eI k r l`.

Substitute `hq1` using the available equality. Rewrite using `[w_col_e, w_col_e]`. Apply the tactic sequence `by_cases hp : p = esI k r l <;> simp [hp]`. Distinguish the cases in `hq2 : q = esI k r l`. Substitute `hq2` using the available equality.

Rewrite using `[w_col_es, w_col_es]`. Apply the tactic sequence `by_cases hp : p = eI k r l <;> simp [hp, hne.symm, mul_inv, mul_comm]`. Rewrite using `[w_col_other l a p q hq1 hq2, w_col_other l (a * u) p q hq1 hq2]`. Simplify using `[hq1, hq2]`.
-/
lemma w_mul_dg (l : Fin r) (a u : ℂ) :
    w1 k r l a * dg l u (star u)⁻¹ = w1 k r l (a * u) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold dg
  ext p q
  rw [Matrix.mul_diagonal]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [w_col_e, w_col_e]
    by_cases hp : p = esI k r l <;> simp [hp]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [w_col_es, w_col_es]
    by_cases hp : p = eI k r l <;> simp [hp, hne.symm, mul_inv, mul_comm]
  rw [w_col_other l a p q hq1 hq2, w_col_other l (a * u) p q hq1 hq2]
  simp [hq1, hq2]

/- English proof (translation)
Establish `h'` using `congrFun h q`. Simplify using `only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h'`. Conclude with `h'`.
-/
private lemma apply_eq_ite_of_mulVec_bvec_eq (g : Mx k r) (v : Fin (2 * r + k + 1)) (h : g *ᵥ bvec v = bvec v)
    (q : Fin (2 * r + k + 1)) : g q v = if q = v then 1 else 0 := by
  have h' := congrFun h q
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h'
  exact h'

/- English proof (translation)
Establish `e` using `congrFun (congrFun hg q) (WeylGroupFacts.tau k r p)`. Rewrite `e` using `[conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma, tau_tau_lemma]`. Simplify using `only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma] at e`. Establish `hs` using `sgn_ne_zero' (k := k) (r := r) (WeylGroupFacts.tau k r p)`. Distinguish the cases in `hpq : p = q`.

Substitute `hpq` using the available equality. Rewrite `e` using `[if_pos rfl]`. Establish `h1 : star (g p p) = 1` using `mul_right_cancel₀ hs (e.trans (one_mul _).symm)`. Establish `h2` using `congrArg star h1`. Rewrite `h2` using `[star_star, star_one]`.

Simplify using `[h2]`. Rewrite `e` using `[if_neg (Ne.symm hpq)]`. Establish `h1 : star (g p q) = 0` using `(mul_eq_zero.mp e).resolve_right hs`. Rewrite using `[if_neg hpq]`. Conclude with `star_eq_zero.mp h1`.
-/
private lemma apply_eq_ite_of_isometry_of_tau_column (g : Mx k r) (hg : gᴴ * Hpk k r * g = Hpk k r) (p : Fin (2 * r + k + 1))
    (h : ∀ q, g q (WeylGroupFacts.tau k r p) = if q = WeylGroupFacts.tau k r p then 1 else 0) (q : Fin (2 * r + k + 1)) :
    g p q = if p = q then 1 else 0 := by
  have e := congrFun (congrFun hg q) (WeylGroupFacts.tau k r p)
  rw [conjTranspose_mul_Hpk_mul_apply, hpk_col_lemma, tau_tau_lemma] at e
  simp only [h, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, tau_tau_lemma] at e
  have hs := sgn_ne_zero' (k := k) (r := r) (WeylGroupFacts.tau k r p)
  by_cases hpq : p = q
  · subst hpq
    rw [if_pos rfl] at e
    have h1 : star (g p p) = 1 := mul_right_cancel₀ hs (e.trans (one_mul _).symm)
    have h2 := congrArg star h1
    rw [star_star, star_one] at h2
    simp [h2]
  · rw [if_neg (Ne.symm hpq)] at e
    have h1 : star (g p q) = 0 := (mul_eq_zero.mp e).resolve_right hs
    rw [if_neg hpq]
    exact star_eq_zero.mp h1

/- English proof (translation)
Establish `hl` using `l.isLt`. Simplify using `only [Glev, Set.mem_setOf_eq] at hg`. Take `⟨hU, hfix⟩` from `hg`. Establish `hU' : g₁ᴴ * Hpk k r * g₁ = Hpk k r` using `hU`. Establish `hfe` using `hfix l (by simp)`.

Establish `ce` using `apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.1`. Establish `ces` using `apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.2`. Establish `re : ∀ q, g₁ (eI k r l) q = if eI k r l = q then 1 else 0` using `apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_e]; exact ces)`. Establish `res : ∀ q, g₁ (esI k r l) q = if esI k r l = q then 1 else 0` using `apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_es]; exact ce)`. Unfold `dg`.

Use extensionality with `p q`. Rewrite using `[Matrix.diagonal_mul, Matrix.mul_diagonal]`. Distinguish the cases in `hp1 : p = eI k r l`. Substitute `hp1` using the available equality. Rewrite using `[re q]`.

Distinguish the cases in `hq : eI k r l = q`. Substitute `hq` using the available equality. Simplify using `[mul_comm]`. Simplify using `[hq]`. Distinguish the cases in `hp2 : p = esI k r l`.

Substitute `hp2` using the available equality. Rewrite using `[res q]`. Distinguish the cases in `hq : esI k r l = q`. Substitute `hq` using the available equality. Simplify using `[mul_comm]`.

Simplify using `[hq]`. Distinguish the cases in `hq1 : q = eI k r l`. Substitute `hq1` using the available equality. Rewrite using `[ce p]`. Simplify using `[hp1]`.

Distinguish the cases in `hq2 : q = esI k r l`. Substitute `hq2` using the available equality. Rewrite using `[ces p]`. Simplify using `[hp2]`. Simplify using `[hp1, hp2, hq1, hq2]`.
-/
lemma dg_comm (l : Fin r) (u v : ℂ) (g₁ : Mx k r) (hg : g₁ ∈ Glev k r l.succ) :
    dg l u v * g₁ = g₁ * dg l u v := by
  have hl := l.isLt
  simp only [Glev, Set.mem_setOf_eq] at hg
  obtain ⟨hU, hfix⟩ := hg
  have hU' : g₁ᴴ * Hpk k r * g₁ = Hpk k r := hU
  have hfe := hfix l (by simp)
  have ce := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.1
  have ces := apply_eq_ite_of_mulVec_bvec_eq g₁ _ hfe.2
  have re : ∀ q, g₁ (eI k r l) q = if eI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_e]; exact ces)
  have res : ∀ q, g₁ (esI k r l) q = if esI k r l = q then 1 else 0 :=
    apply_eq_ite_of_isometry_of_tau_column g₁ hU' _ (by rw [tau_es]; exact ce)
  unfold dg
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [re q]
    by_cases hq : eI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hp2 : p = esI k r l
  · subst hp2
    rw [res q]
    by_cases hq : esI k r l = q
    · subst hq
      simp [mul_comm]
    · simp [hq]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [ce p]
    simp [hp1]
  by_cases hq2 : q = esI k r l
  · subst hq2
    rw [ces p]
    simp [hp2]
  simp [hp1, hp2, hq1, hq2]

/- English proof (translation)
Rewrite using `[Matrix.exp_diagonal]`. Unfold `dg`. Use `congr 1`. Use function extensionality and compare the values at `p`. Use `first`.

Consider the case `rw [Pi.exp_apply]`. Consider the case `rw [NormedSpace.Pi.exp_apply]`. Consider the case `rw [NormedSpace.exp_apply]`. Consider the case `simp only [Pi.exp_def]`. Apply the tactic sequence `split_ifs <;> simp [Complex.exp_eq_exp_ℂ]`.
-/
lemma exp_diag2 (l : Fin r) (x y : ℂ) :
    NormedSpace.exp (diagonal (fun p => if p = eI k r l then x else if p = esI k r l then y else 0) : Mx k r) =
      dg l (Complex.exp x) (Complex.exp y) := by
  rw [Matrix.exp_diagonal]
  unfold dg
  congr 1
  funext p
  first
    | rw [Pi.exp_apply]
    | rw [NormedSpace.Pi.exp_apply]
    | rw [NormedSpace.exp_apply]
    | simp only [Pi.exp_def]
  split_ifs <;> simp [Complex.exp_eq_exp_ℂ]

end PI.QnRT
