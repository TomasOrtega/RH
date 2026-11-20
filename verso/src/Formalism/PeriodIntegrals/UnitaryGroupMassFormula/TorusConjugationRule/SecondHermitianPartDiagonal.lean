import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusConjugationRule.WColOther

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Filter Topology
open scoped ContDiff

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.QnRT

variable {k r : ℕ}

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
Unfold `WeylGroupFacts.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private lemma sgn_sq_lemma (i : Fin (2 * r + k + 1)) : WeylGroupFacts.sgn k r i * WeylGroupFacts.sgn k r i = 1 := by
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
lemma hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_left_inv hpk_sq_lemma

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
Rewrite using `[single_ct_lemma, star_one]`. Use extensionality with `p q`. Rewrite using `[conj_single_lemma, hpk_eq_lemma, hpk_col_lemma, Matrix.single_apply]`. Distinguish the cases in `hp : p = WeylGroupFacts.tau k r x`. Substitute `hp` using the available equality.

Distinguish the cases in `hq : q = WeylGroupFacts.tau k r x`. Substitute `hq` using the available equality. Simplify using `[tau_tau_lemma, sgn_tau_lemma, sgn_sq_lemma]`. Establish `hq' : x ≠ WeylGroupFacts.tau k r q` using `fun h => hq (by rw [h, tau_tau_lemma])`. Simplify using `[hq', Ne.symm hq]`.

Establish `hp' : x ≠ WeylGroupFacts.tau k r p` using `fun h => hp (by rw [h, tau_tau_lemma])`. Simplify using `[hp', Ne.symm hp]`.
-/
lemma conj_single (x : Fin (2 * r + k + 1)) :
    Hpk k r * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by
  rw [single_ct_lemma, star_one]
  ext p q
  rw [conj_single_lemma, hpk_eq_lemma, hpk_col_lemma, Matrix.single_apply]
  by_cases hp : p = WeylGroupFacts.tau k r x
  · subst hp
    by_cases hq : q = WeylGroupFacts.tau k r x
    · subst hq
      simp [tau_tau_lemma, sgn_tau_lemma, sgn_sq_lemma]
    · have hq' : x ≠ WeylGroupFacts.tau k r q := fun h => hq (by rw [h, tau_tau_lemma])
      simp [hq', Ne.symm hq]
  · have hp' : x ≠ WeylGroupFacts.tau k r p := fun h => hp (by rw [h, tau_tau_lemma])
    simp [hp', Ne.symm hp]

/- English proof (translation)
Rewrite using `[hpk_inv, conj_single]`.
-/
lemma inv_conj_single (x : Fin (2 * r + k + 1)) :
    (Hpk k r)⁻¹ * (single x x (1 : ℂ))ᴴ * Hpk k r =
      single (WeylGroupFacts.tau k r x) (WeylGroupFacts.tau k r x) 1 := by
  rw [hpk_inv, conj_single]

def dz (l : Fin r) (κ κ' : ℂ) : Mx k r :=
  diagonal (fun p => if p = eI k r l then κ else if p = esI k r l then κ' else 0)

/- English proof (translation)
Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma half_eq : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
  push_cast
  ring

/- English proof (translation)
Rewrite using `[one_div, mul_inv, Complex.inv_I]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma quarter_eq : (1 / (2 * Complex.I) : ℂ) = ((-1 / 2 : ℝ) : ℂ) * Complex.I := by
  rw [one_div, mul_inv, Complex.inv_I]
  push_cast
  ring

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `hpart1 dz`. Rewrite using `[inv_conj_single, tau_e]`. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]`.

Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Distinguish the cases in `h1 : p = eI k r l`. Substitute `h1` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`.

Distinguish the cases in `h2 : p = esI k r l`. Substitute `h2` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`. Establish `a1 : ¬ (eI k r l = p ∧ eI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`.

Establish `a2 : ¬ (esI k r l = p ∧ esI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`. Simplify using `[a1, a2, hpq]`.
-/
lemma X1_eq (l : Fin r) : hpart1 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart1 dz
  rw [inv_conj_single, tau_e]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `hpart2 dz`. Rewrite using `[inv_conj_single, tau_e]`. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]`.

Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Distinguish the cases in `h1 : p = eI k r l`. Substitute `h1` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`.

Distinguish the cases in `h2 : p = esI k r l`. Substitute `h2` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`. Establish `a1 : ¬ (eI k r l = p ∧ eI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`.

Establish `a2 : ¬ (esI k r l = p ∧ esI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`. Simplify using `[a1, a2, hpq]`.
-/
lemma depthNumbers_threshold_eq (l : Fin r) : hpart2 (Hpk k r) (single (eI k r l) (eI k r l) 1) =
    dz l (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart2 dz
  rw [inv_conj_single, tau_e]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `hpart1 dz`. Rewrite using `[inv_conj_single, tau_es]`. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]`.

Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Distinguish the cases in `h1 : p = eI k r l`. Substitute `h1` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`.

Distinguish the cases in `h2 : p = esI k r l`. Substitute `h2` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`. Establish `a1 : ¬ (eI k r l = p ∧ eI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`.

Establish `a2 : ¬ (esI k r l = p ∧ esI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`. Simplify using `[a1, a2, hpq]`.
-/
lemma first_hermitian_part_diagonal (l : Fin r) : hpart1 (Hpk k r) (single (esI k r l) (esI k r l) 1) =
    dz l (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart1 dz
  rw [inv_conj_single, tau_es]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Unfold `hpart2 dz`. Rewrite using `[inv_conj_single, tau_es]`. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul]`.

Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Distinguish the cases in `h1 : p = eI k r l`. Substitute `h1` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`.

Distinguish the cases in `h2 : p = esI k r l`. Substitute `h2` using the available equality. Apply the tactic sequence `simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)`. Simplify using `[h1, h2, Ne.symm h1, Ne.symm h2]`. Establish `a1 : ¬ (eI k r l = p ∧ eI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`.

Establish `a2 : ¬ (esI k r l = p ∧ esI k r l = q)` using `fun h => hpq (h.1.symm.trans h.2)`. Simplify using `[a1, a2, hpq]`.
-/
lemma second_hermitian_part_diagonal (l : Fin r) : hpart2 (Hpk k r) (single (esI k r l) (esI k r l) 1) =
    dz l (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  unfold hpart2 dz
  rw [inv_conj_single, tau_es]
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.single_apply,
    Matrix.diagonal_apply, smul_eq_mul]
  by_cases hpq : p = q
  · subst hpq
    by_cases h1 : p = eI k r l
    · subst h1
      simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
    · by_cases h2 : p = esI k r l
      · subst h2
        simp [hne, hne.symm] <;> (try norm_num) <;> (try ring)
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  · have a1 : ¬ (eI k r l = p ∧ eI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    have a2 : ¬ (esI k r l = p ∧ esI k r l = q) := fun h => hpq (h.1.symm.trans h.2)
    simp [a1, a2, hpq]

/- English proof (translation)
Establish `hne : eI k r l ≠ esI k r l` using `e_ne_es l`. Use extensionality with `p q`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Unfold `w1`. Distinguish the cases in `hp1 : p = eI k r l`.

Substitute `hp1` using the available equality. Distinguish the cases in `hq2 : q = esI k r l`. Substitute `hq2` using the available equality. Simplify using `[hne, hne.symm]`. Simplify using `[hne, hne.symm, hq2, Ne.symm hq2]`.

Distinguish the cases in `hp2 : p = esI k r l`. Substitute `hp2` using the available equality. Distinguish the cases in `hq1 : q = eI k r l`. Substitute `hq1` using the available equality. Simplify using `[hne, hne.symm]`.

Simplify using `[hne, hne.symm, hq1, Ne.symm hq1]`. Simplify using `[hp1, hp2, Ne.symm hp1, Ne.symm hp2]`.
-/
lemma w_decomp (l : Fin r) (b : ℂ) :
    w1 k r l b = w1 k r l 0 + b • single (esI k r l) (eI k r l) 1 +
      (star b)⁻¹ • single (eI k r l) (esI k r l) 1 := by
  have hne : eI k r l ≠ esI k r l := e_ne_es l
  ext p q
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  unfold w1
  by_cases hp1 : p = eI k r l
  · subst hp1
    by_cases hq2 : q = esI k r l
    · subst hq2
      simp [hne, hne.symm]
    · simp [hne, hne.symm, hq2, Ne.symm hq2]
  · by_cases hp2 : p = esI k r l
    · subst hp2
      by_cases hq1 : q = eI k r l
      · subst hq1
        simp [hne, hne.symm]
      · simp [hne, hne.symm, hq1, Ne.symm hq1]
    · simp [hp1, hp2, Ne.symm hp1, Ne.symm hp2]

/- English proof (translation)
Establish `hfun : (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) = fun c' : Fin r → ℂ => (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) + (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ)) * g₁`. Use function extensionality and compare the values at `c'`. Rewrite using `[w_decomp]`. Rewrite using `[hfun]`. Establish `h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => c' l) c` using `differentiableAt_apply l c`.

Establish `hs : DifferentiableAt ℝ (fun c' : Fin r → ℂ => star (c' l)) c` using `Complex.conjCLE.differentiableAt.comp c h1`. Establish `h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (star (c' l))⁻¹) c` using `hs.inv (by simpa using hc)`. Establish `hin : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) + (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ) : Mx k r)) c` using `((differentiableAt_const _).add (h1.smul_const _)).add (h2.smul_const _)`. Set `Lm : Mx k r →L[ℝ] Mx k r` to `LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g₁)`. Conclude with `Lm.differentiableAt.comp c hin`.
-/
lemma w_diff (l : Fin r) (g₁ : Mx k r) (c : Fin r → ℂ) (hc : c l ≠ 0) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) c := by
  have hfun : (fun c' : Fin r → ℂ => w1 k r l (c' l) * g₁) = fun c' : Fin r → ℂ =>
      (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ)) * g₁ := by
    funext c'
    rw [w_decomp]
  rw [hfun]
  have h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => c' l) c := differentiableAt_apply l c
  have hs : DifferentiableAt ℝ (fun c' : Fin r → ℂ => star (c' l)) c :=
    Complex.conjCLE.differentiableAt.comp c h1
  have h2 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (star (c' l))⁻¹) c :=
    hs.inv (by simpa using hc)
  have hin : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (w1 k r l 0 + c' l • single (esI k r l) (eI k r l) (1 : ℂ) +
        (star (c' l))⁻¹ • single (eI k r l) (esI k r l) (1 : ℂ) : Mx k r)) c :=
    ((differentiableAt_const _).add (h1.smul_const _)).add (h2.smul_const _)
  let Lm : Mx k r →L[ℝ] Mx k r := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ g₁)
  exact Lm.differentiableAt.comp c hin

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf _ ⟨w_mul_mem l (c l) hc g₁ hg₁, hD⟩`. Establish `hγ` using `w_diff l g₁ c hc`. Apply the tactic sequence `have hFd : DifferentiableAt ℝ F (w1 k r l (c l) * g₁) := (hF.differentiableOn (by first | simp | exact le_top | norm_num)).differentiableAt (hU.mem_nhds hgU)`. Establish `hev1 : ∀ᶠ c' in 𝓝 c, w1 k r l (c' l) * g₁ ∈ U` using `hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)`. Establish `hev2 : ∀ᶠ c' in 𝓝 c, c' l ≠ 0` using `(continuous_apply l).continuousAt.eventually_ne hc`.

Establish `hev` using `hev1.and hev2`. Use `(hFd.comp c hγ).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hev] with c' hc'`. Conclude with `hfF _ hc'.1 (w_mul_mem l (c' l) hc'.2 g₁ hg₁)`.
-/
lemma phi_diff {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) :
    DifferentiableAt ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf _ ⟨w_mul_mem l (c l) hc g₁ hg₁, hD⟩
  have hγ := w_diff l g₁ c hc
  have hFd : DifferentiableAt ℝ F (w1 k r l (c l) * g₁) :=
    (hF.differentiableOn (by first | simp | exact le_top | norm_num)).differentiableAt
      (hU.mem_nhds hgU)
  have hev1 : ∀ᶠ c' in 𝓝 c, w1 k r l (c' l) * g₁ ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)
  have hev2 : ∀ᶠ c' in 𝓝 c, c' l ≠ 0 := (continuous_apply l).continuousAt.eventually_ne hc
  have hev := hev1.and hev2
  refine (hFd.comp c hγ).congr_of_eventuallyEq ?_
  filter_upwards [hev] with c' hc'
  exact hfF _ hc'.1 (w_mul_mem l (c' l) hc'.2 g₁ hg₁)

/- English proof (translation)
Establish `hsm : (t : ℂ) • dz l κ (-star κ) = (diagonal (fun p => if p = eI k r l then (t : ℂ) * κ else if p = esI k r l then (t : ℂ) * -star κ else 0) : Mx k r)`. Unfold `dz`. Use extensionality with `p q`. Simplify using `only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hconj : Complex.exp ((t : ℂ) * -star κ) = (star (Complex.exp ((t : ℂ) * κ)))⁻¹`. Rewrite using `[show (t : ℂ) * -star κ = -(star ((t : ℂ) * κ)) by simp, Complex.exp_neg]`. Use `congr 1`. Conclude with `Complex.exp_conj _`. Rewrite using `[hsm, exp_diag2, hconj, Matrix.mul_assoc, ← dg_comm l _ _ g₁ hg₁, ← Matrix.mul_assoc, w_mul_dg]`.
-/
lemma mul_exp_dz (l : Fin r) (a κ : ℂ) (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (t : ℝ) :
    w1 k r l a * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)) =
      w1 k r l (a * Complex.exp (t * κ)) * g₁ := by
  have hsm : (t : ℂ) • dz l κ (-star κ) = (diagonal (fun p => if p = eI k r l then (t : ℂ) * κ
      else if p = esI k r l then (t : ℂ) * -star κ else 0) : Mx k r) := by
    unfold dz
    ext p q
    simp only [Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
    split_ifs <;> simp
  have hconj : Complex.exp ((t : ℂ) * -star κ) = (star (Complex.exp ((t : ℂ) * κ)))⁻¹ := by
    rw [show (t : ℂ) * -star κ = -(star ((t : ℂ) * κ)) by simp, Complex.exp_neg]
    congr 1
    exact Complex.exp_conj _
  rw [hsm, exp_diag2, hconj, Matrix.mul_assoc, ← dg_comm l _ _ g₁ hg₁, ← Matrix.mul_assoc, w_mul_dg]

/- English proof (translation)
Establish `hφ` using `phi_diff l D f hf c hc g₁ hg₁ hD`. Establish `hηd : HasDerivAt (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ))) (Pi.single l (c l * κ)) 0`. Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Distinguish the cases in `hi : i = l`.

Substitute `hi` using the available equality. Simplify using `only [Function.update_apply, if_true, Pi.single_eq_same]`. Establish `h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * κ)) κ 0`. Establish `h2` using `(((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const κ).cexp).comp_ofReal`. Simplify using `using h2`.

Simplify using `using h1.const_mul (c i)`. Simplify using `only [Function.update_apply, hi, if_false, Pi.single_eq_of_ne hi]`. Conclude with `hasDerivAt_const _ _`. Establish `hη0 : Function.update c l (c l * Complex.exp (((0 : ℝ) : ℂ) * κ)) = c` using `by simp`. Establish `hcomp` using `hφ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hηd hη0.symm`.

Unfold `RdV`. Establish `hfun : (fun t : ℝ => f (w1 k r l (c l) * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)))) = (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) ∘ (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ)))`. Use function extensionality and compare the values at `t`. Rewrite using `[mul_exp_dz l (c l) κ g₁ hg₁ t]`. Simplify using `[Function.comp]`.

Rewrite using `[hfun, hcomp.deriv]`.
-/
lemma rdV_dz {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ : ℂ) :
    RdV (dz l κ (-star κ)) f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  have hφ := phi_diff l D f hf c hc g₁ hg₁ hD
  have hηd : HasDerivAt (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ)))
      (Pi.single l (c l * κ)) 0 := by
    rw [hasDerivAt_pi]
    intro i
    by_cases hi : i = l
    · subst hi
      simp only [Function.update_apply, if_true, Pi.single_eq_same]
      have h1 : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * κ)) κ 0 := by
        have h2 := (((hasDerivAt_id ((0 : ℝ) : ℂ)).mul_const κ).cexp).comp_ofReal
        simpa using h2
      simpa using h1.const_mul (c i)
    · simp only [Function.update_apply, hi, if_false, Pi.single_eq_of_ne hi]
      exact hasDerivAt_const _ _
  have hη0 : Function.update c l (c l * Complex.exp (((0 : ℝ) : ℂ) * κ)) = c := by simp
  have hcomp := hφ.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hηd hη0.symm
  unfold RdV
  have hfun : (fun t : ℝ => f (w1 k r l (c l) * g₁ * NormedSpace.exp ((t : ℂ) • dz l κ (-star κ)))) =
      (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) ∘
        (fun t : ℝ => Function.update c l (c l * Complex.exp ((t : ℂ) * κ))) := by
    funext t
    rw [mul_exp_dz l (c l) κ g₁ hg₁ t]
    simp [Function.comp]
  rw [hfun, hcomp.deriv]

/- English proof (translation)
Substitute `hκ` using the available equality. Conclude with `rdV_dz l D f hf c hc g₁ hg₁ hD κ`.
-/
lemma rdV_dz' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r) (D : Set (Mx k r))
    (f : Mx k r → E) (hf : SmoothLev k r l.castSucc D f) (c : Fin r → ℂ) (hc : c l ≠ 0)
    (g₁ : Mx k r) (hg₁ : g₁ ∈ Glev k r l.succ) (hD : w1 k r l (c l) * g₁ ∈ D) (κ κ' : ℂ)
    (hκ : κ' = -star κ) :
    RdV (dz l κ κ') f (w1 k r l (c l) * g₁) =
      fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c (Pi.single l (c l * κ)) := by
  subst hκ
  exact rdV_dz l D f hf c hc g₁ hg₁ hD κ

/- English proof (translation)
Establish `h : (Pi.single l z : Fin r → ℂ) = ((z.re : ℝ) • (Pi.single l (1 : ℂ) : Fin r → ℂ) + (z.im : ℝ) • (Pi.single l Complex.I : Fin r → ℂ) : Fin r → ℂ)`. Use extensionality with `i`. Distinguish the cases in `hi : i = l`. Substitute `hi` using the available equality. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]`.

Conclude with `(Complex.re_add_im z).symm`. Simplify using `[hi]`. Rewrite using `[h, map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]`.
-/
lemma lin_single {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (l : Fin r)
    (L : (Fin r → ℂ) →L[ℝ] E) (z : ℂ) :
    L (Pi.single l z) = (z.re : ℂ) • L (Pi.single l 1) + (z.im : ℂ) • L (Pi.single l Complex.I) := by
  have h : (Pi.single l z : Fin r → ℂ) =
      ((z.re : ℝ) • (Pi.single l (1 : ℂ) : Fin r → ℂ) +
        (z.im : ℝ) • (Pi.single l Complex.I : Fin r → ℂ) : Fin r → ℂ) := by
    ext i
    by_cases hi : i = l
    · subst hi
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    · simp [hi]
  rw [h, map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]

/- English proof (translation)
Introduce `E _ _ k r l D f hD hf c hcO g₁ hg₁ hcD`. Establish `hc : c l ≠ 0` using `hcO l`. Prove the components needed by the constructor for the conclusion. Use `show RdV _ f _ + Complex.I • RdV _ f _ = _`. Rewrite using `[X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hc g₁ hg₁ hcD ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) (by simp), rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) (by simp)]`.

Unfold `pOp wirt`. Rewrite using `[if_pos hcO]`. Generalize the expression as in `fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'`. Rewrite using `[lin_single l L' (c l * ((1 / 2 : ℝ) : ℂ)), lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]`. Generalize the expression as in `hA : L' (Pi.single l (1 : ℂ)) = A`.

Generalize the expression as in `hB : L' (Pi.single l Complex.I) = B`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]`. Use `push_cast`. Use `conv_rhs => rw [← Complex.re_add_im (c l)]`. Apply the tactic sequence `try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`.

Generalize the expression as in `(c l).re = a`. Generalize the expression as in `(c l).im = b`. Apply the tactic sequence `match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf`. Use `show RdV _ f _ + Complex.I • RdV _ f _ = _`. Rewrite using `[first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hc g₁ hg₁ hcD (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) (by simp), rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I) (by simp)]`.

Unfold `pbOp wirtBar`. Rewrite using `[if_pos hcO]`. Generalize the expression as in `fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'`. Rewrite using `[lin_single l L' (c l * -((1 / 2 : ℝ) : ℂ)), lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]`. Generalize the expression as in `hA : L' (Pi.single l (1 : ℂ)) = A`.

Generalize the expression as in `hB : L' (Pi.single l Complex.I) = B`. Simplify using `only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]`. Use `push_cast`. Use `conv_rhs => rw [← Complex.re_add_im (c l)]`. Apply the tactic sequence `try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]`.

Generalize the expression as in `(c l).re = a`. Generalize the expression as in `(c l).im = b`. Apply the tactic sequence `match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf`.
-/
theorem ruleTorus : RuleTorus := by
  intro E _ _ k r l D f hD hf c hcO g₁ hg₁ hcD
  have hc : c l ≠ 0 := hcO l
  constructor
  · show RdV _ f _ + Complex.I • RdV _ f _ = _
    rw [X1_eq, depthNumbers_threshold_eq, rdV_dz' l D f hf c hc g₁ hg₁ hcD ((1 / 2 : ℝ) : ℂ) (-((1 / 2 : ℝ) : ℂ)) (by simp),
      rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I)
        (by simp)]
    unfold pOp wirt
    rw [if_pos hcO]
    generalize fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'
    rw [lin_single l L' (c l * ((1 / 2 : ℝ) : ℂ)),
      lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize hA : L' (Pi.single l (1 : ℂ)) = A
    generalize hB : L' (Pi.single l Complex.I) = B
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    conv_rhs => rw [← Complex.re_add_im (c l)]
    try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    generalize (c l).re = a
    generalize (c l).im = b
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf
  · show RdV _ f _ + Complex.I • RdV _ f _ = _
    rw [first_hermitian_part_diagonal, second_hermitian_part_diagonal, rdV_dz' l D f hf c hc g₁ hg₁ hcD (-((1 / 2 : ℝ) : ℂ)) ((1 / 2 : ℝ) : ℂ) (by simp),
      rdV_dz' l D f hf c hc g₁ hg₁ hcD (((-1 / 2 : ℝ) : ℂ) * Complex.I) (((-1 / 2 : ℝ) : ℂ) * Complex.I)
        (by simp)]
    unfold pbOp wirtBar
    rw [if_pos hcO]
    generalize fderiv ℝ (fun c' : Fin r → ℂ => f (w1 k r l (c' l) * g₁)) c = L'
    rw [lin_single l L' (c l * -((1 / 2 : ℝ) : ℂ)),
      lin_single l L' (c l * (((-1 / 2 : ℝ) : ℂ) * Complex.I))]
    generalize hA : L' (Pi.single l (1 : ℂ)) = A
    generalize hB : L' (Pi.single l Complex.I) = B
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.neg_im]
    push_cast
    conv_rhs => rw [← Complex.re_add_im (c l)]
    try simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    generalize (c l).re = a
    generalize (c l).im = b
    match_scalars <;> ring_nf <;> (try simp only [Complex.I_sq]) <;> ring_nf

end PI.QnRT
