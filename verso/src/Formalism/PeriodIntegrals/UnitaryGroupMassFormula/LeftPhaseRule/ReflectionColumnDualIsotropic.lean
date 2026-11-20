import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LeftPhaseRule.MulApplyS

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.Q.LeftMultiplicationRule

variable {k r : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma tau_val (i : Fin (2 * r + k + 1)) :
    (tau k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := rfl

/- English proof (translation)
Apply the tactic sequence `apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega`.
-/
lemma tau_e (l : Fin r) : tau k r (eI k r l) = esI k r l := by
  apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega

/- English proof (translation)
Apply the tactic sequence `apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega`.
-/
lemma tau_es (l : Fin r) : tau k r (esI k r l) = eI k r l := by
  apply Fin.ext; rw [tau_val, eI_val, esI_val]; have := l.isLt; split_ifs <;> omega

/- English proof (translation)
Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Rewrite using `[eI_val]`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_e (l : Fin r) : WeylGroupFacts.sgn k r (eI k r l) = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg]; rw [eI_val]; have := l.isLt; omega

/- English proof (translation)
Unfold `WeylGroupFacts.sgn`. Rewrite using `[if_neg]`. Rewrite using `[esI_val]`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma sgn_es (l : Fin r) : WeylGroupFacts.sgn k r (esI k r l) = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg]; rw [esI_val]; have := l.isLt; omega

/- English proof (translation)
Apply the tactic sequence `unfold WeylGroupFacts.sgn; split_ifs <;> simp`.
-/
lemma star_sgn (i : Fin (2 * r + k + 1)) : star (WeylGroupFacts.sgn k r i) = WeylGroupFacts.sgn k r i := by
  unfold WeylGroupFacts.sgn; split_ifs <;> simp

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[eI_val, esI_val]`. Use `l.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
lemma e_ne_es (l : Fin r) : eI k r l ≠ esI k r l := by
  intro h; have := congrArg Fin.val h; rw [eI_val, esI_val] at this; have := l.isLt; omega

/- English proof (translation)
Unfold `w1`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Simplify using `[hq1, hq2]`. Simplify using `[hpq, hq1, hq2]`.
-/
lemma reflection_off_support (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) (hq1 : q ≠ eI k r l)
    (hq2 : q ≠ esI k r l) : w1 k r l c p q = if p = q then 1 else 0 := by
  unfold w1
  by_cases hpq : p = q
  · subst hpq; simp [hq1, hq2]
  · simp [hpq, hq1, hq2]

/- English proof (translation)
Unfold `w1`. Distinguish the cases in `hpq : p = q`. Substitute `hpq` using the available equality. Simplify using `[hp1, hp2]`. Simplify using `[hpq, hp1, hp2]`.
-/
lemma reflection_off_support_row (l : Fin r) (c : ℂ) (p q : Fin (2 * r + k + 1)) (hp1 : p ≠ eI k r l)
    (hp2 : p ≠ esI k r l) : w1 k r l c p q = if p = q then 1 else 0 := by
  unfold w1
  by_cases hpq : p = q
  · subst hpq; simp [hp1, hp2]
  · simp [hpq, hp1, hp2]

/- English proof (translation)
Establish `hne` using `e_ne_es (k := k) l`. Unfold `w1`. Distinguish the cases in `hp : p = esI k r l`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules.

Distinguish the cases in `hp' : p = eI k r l`. Substitute `hp'` using the available equality. Simplify using `[hp, hne]`. Simplify using `[hp, hp']`.
-/
lemma reflection_column_isotropic (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) :
    w1 k r l c p (eI k r l) = if p = esI k r l then c else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hp : p = esI k r l
  · subst hp; simp
  · by_cases hp' : p = eI k r l
    · subst hp'; simp [hp, hne]
    · simp [hp, hp']

/- English proof (translation)
Establish `hne` using `e_ne_es (k := k) l`. Unfold `w1`. Distinguish the cases in `hp : p = eI k r l`. Substitute `hp` using the available equality. Simplify using `[hne.symm]`.

Distinguish the cases in `hp' : p = esI k r l`. Substitute `hp'` using the available equality. Simplify using `[hp, hne.symm]`. Simplify using `[hp, hp']`.
-/
lemma reflection_column_dual_isotropic (l : Fin r) (c : ℂ) (p : Fin (2 * r + k + 1)) :
    w1 k r l c p (esI k r l) = if p = eI k r l then (star c)⁻¹ else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hp : p = eI k r l
  · subst hp; simp [hne.symm]
  · by_cases hp' : p = esI k r l
    · subst hp'; simp [hp, hne.symm]
    · simp [hp, hp']

/- English proof (translation)
Establish `hne` using `e_ne_es (k := k) l`. Unfold `w1`. Distinguish the cases in `hq : q = esI k r l`. Substitute `hq` using the available equality. Simplify using `[hne]`.

Simplify using `[hq, hne]`.
-/
lemma weyl_cell_apply_basis (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (eI k r l) q = if q = esI k r l then (star c)⁻¹ else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hq : q = esI k r l
  · subst hq; simp [hne]
  · simp [hq, hne]

/- English proof (translation)
Establish `hne` using `e_ne_es (k := k) l`. Unfold `w1`. Distinguish the cases in `hq : q = eI k r l`. Substitute `hq` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hq, hne.symm]`.
-/
lemma weyl_cell_apply_dual_basis (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) :
    w1 k r l c (esI k r l) q = if q = eI k r l then c else 0 := by
  have hne := e_ne_es (k := k) l
  unfold w1
  by_cases hq : q = eI k r l
  · subst hq; simp
  · simp [hq, hne.symm]

/- English proof (translation)
Establish `hsc : star c ≠ 0` using `star_ne_zero.2 hc`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Distinguish the cases in `hq1 : q = eI k r l`. Substitute `hq1` using the available equality.

Rewrite using `[Finset.sum_eq_single (esI k r l)]`. Rewrite using `[reflection_column_isotropic, if_pos rfl, reflection_column_dual_isotropic]`. Distinguish the cases in `hp : p = eI k r l`. Rewrite using `[if_pos hp, if_pos hp, inv_mul_cancel₀ hsc]`. Rewrite using `[if_neg hp, if_neg hp, zero_mul]`.

Introduce `t _ ht`. Rewrite using `[reflection_column_isotropic, if_neg ht, mul_zero]`. Simplify using the standard rewrite rules. Distinguish the cases in `hq2 : q = esI k r l`. Substitute `hq2` using the available equality.

Rewrite using `[Finset.sum_eq_single (eI k r l)]`. Rewrite using `[reflection_column_dual_isotropic, if_pos rfl, reflection_column_isotropic, star_star]`. Distinguish the cases in `hp : p = esI k r l`. Rewrite using `[if_pos hp, if_pos hp, mul_inv_cancel₀ hc]`. Rewrite using `[if_neg hp, if_neg hp, zero_mul]`.

Introduce `t _ ht`. Rewrite using `[reflection_column_dual_isotropic, if_neg ht, mul_zero]`. Simplify using the standard rewrite rules. Rewrite using `[Finset.sum_eq_single q]`. Rewrite using `[reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one, reflection_off_support _ _ p q hq1 hq2]`.

Introduce `t _ ht`. Rewrite using `[reflection_off_support _ _ t q hq1 hq2, if_neg ht, mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma reflection_mul_star (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c * w1 k r l (star c) = 1 := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  ext p q
  rw [Matrix.mul_apply, Matrix.one_apply]
  by_cases hq1 : q = eI k r l
  · subst hq1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, reflection_column_dual_isotropic]
      by_cases hp : p = eI k r l
      · rw [if_pos hp, if_pos hp, inv_mul_cancel₀ hsc]
      · rw [if_neg hp, if_neg hp, zero_mul]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, mul_zero]
    · simp
  · by_cases hq2 : q = esI k r l
    · subst hq2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, reflection_column_isotropic, star_star]
        by_cases hp : p = esI k r l
        · rw [if_pos hp, if_pos hp, mul_inv_cancel₀ hc]
        · rw [if_neg hp, if_neg hp, zero_mul]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, mul_zero]
      · simp
    · rw [Finset.sum_eq_single q]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one, reflection_off_support _ _ p q hq1 hq2]
      · intro t _ ht; rw [reflection_off_support _ _ t q hq1 hq2, if_neg ht, mul_zero]
      · simp

/- English proof (translation)
The claim follows from `Matrix.inv_eq_right_inv (reflection_mul_star l c hc)`.
-/
lemma weyl_cell_inv (l : Fin r) (c : ℂ) (hc : c ≠ 0) : (w1 k r l c)⁻¹ = w1 k r l (star c) :=
  Matrix.inv_eq_right_inv (reflection_mul_star l c hc)

/- English proof (translation)
Establish `hsc : star c ≠ 0` using `star_ne_zero.2 hc`. Use `show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply]`. Simplify using `only [conjTranspose_apply, hpk_mul_apply]`.

Rewrite using `[hpk_row]`. Distinguish the cases in `hp1 : p = eI k r l`. Substitute `hp1` using the available equality. Rewrite using `[Finset.sum_eq_single (esI k r l)]`. Rewrite using `[reflection_column_isotropic, if_pos rfl, tau_es, sgn_es, weyl_cell_apply_basis, tau_e, sgn_e]`.

Distinguish the cases in `hq : q = esI k r l`. Rewrite using `[if_pos hq, if_pos hq, one_mul, ← star_inv₀, ← star_mul, inv_mul_cancel₀ hc, star_one]`. Rewrite using `[if_neg hq, if_neg hq, mul_zero, mul_zero]`. Introduce `t _ ht`. Rewrite using `[reflection_column_isotropic, if_neg ht, star_zero, zero_mul]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hp2 : p = esI k r l`. Substitute `hp2` using the available equality. Rewrite using `[Finset.sum_eq_single (eI k r l)]`. Rewrite using `[reflection_column_dual_isotropic, if_pos rfl, tau_e, sgn_e, weyl_cell_apply_dual_basis, tau_es, sgn_es]`.

Distinguish the cases in `hq : q = eI k r l`. Rewrite using `[if_pos hq, if_pos hq, one_mul, star_inv₀, star_star, inv_mul_cancel₀ hc]`. Rewrite using `[if_neg hq, if_neg hq, mul_zero, mul_zero]`. Introduce `t _ ht`. Rewrite using `[reflection_column_dual_isotropic, if_neg ht, star_zero, zero_mul]`.

Simplify using the standard rewrite rules. Establish `ht1 : tau k r p ≠ eI k r l`. Introduce `h`. Apply `hp2` to reduce the goal to its premises. Rewrite using `[← tau_tau p, h, tau_e]`.

Establish `ht2 : tau k r p ≠ esI k r l`. Introduce `h`. Apply `hp1` to reduce the goal to its premises. Rewrite using `[← tau_tau p, h, tau_es]`. Rewrite using `[Finset.sum_eq_single p]`.

Rewrite using `[reflection_off_support _ _ p p hp1 hp2, if_pos rfl, star_one, one_mul, reflection_off_support_row _ _ (tau k r p) q ht1 ht2]`. Distinguish the cases in `hq : q = tau k r p`. Rewrite using `[if_pos hq, if_pos hq.symm, mul_one]`. Rewrite using `[if_neg hq, if_neg (Ne.symm hq), mul_zero]`. Introduce `t _ ht`.

Rewrite using `[reflection_off_support _ _ t p hp1 hp2, if_neg ht, star_zero, zero_mul]`. Simplify using the standard rewrite rules.
-/
lemma weyl_cell_mem_unitary (l : Fin r) (c : ℂ) (hc : c ≠ 0) : w1 k r l c ∈ UH (Hpk k r) := by
  have hsc : star c ≠ 0 := star_ne_zero.2 hc
  show (w1 k r l c)ᴴ * Hpk k r * w1 k r l c = Hpk k r
  ext p q
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [conjTranspose_apply, hpk_mul_apply]
  rw [hpk_row]
  by_cases hp1 : p = eI k r l
  · subst hp1
    rw [Finset.sum_eq_single (esI k r l)]
    · rw [reflection_column_isotropic, if_pos rfl, tau_es, sgn_es, weyl_cell_apply_basis, tau_e, sgn_e]
      by_cases hq : q = esI k r l
      · rw [if_pos hq, if_pos hq, one_mul, ← star_inv₀, ← star_mul, inv_mul_cancel₀ hc, star_one]
      · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
    · intro t _ ht; rw [reflection_column_isotropic, if_neg ht, star_zero, zero_mul]
    · simp
  · by_cases hp2 : p = esI k r l
    · subst hp2
      rw [Finset.sum_eq_single (eI k r l)]
      · rw [reflection_column_dual_isotropic, if_pos rfl, tau_e, sgn_e, weyl_cell_apply_dual_basis, tau_es, sgn_es]
        by_cases hq : q = eI k r l
        · rw [if_pos hq, if_pos hq, one_mul, star_inv₀, star_star, inv_mul_cancel₀ hc]
        · rw [if_neg hq, if_neg hq, mul_zero, mul_zero]
      · intro t _ ht; rw [reflection_column_dual_isotropic, if_neg ht, star_zero, zero_mul]
      · simp
    · have ht1 : tau k r p ≠ eI k r l := by
        intro h; apply hp2; rw [← tau_tau p, h, tau_e]
      have ht2 : tau k r p ≠ esI k r l := by
        intro h; apply hp1; rw [← tau_tau p, h, tau_es]
      rw [Finset.sum_eq_single p]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, star_one, one_mul,
          reflection_off_support_row _ _ (tau k r p) q ht1 ht2]
        by_cases hq : q = tau k r p
        · rw [if_pos hq, if_pos hq.symm, mul_one]
        · rw [if_neg hq, if_neg (Ne.symm hq), mul_zero]
      · intro t _ ht; rw [reflection_off_support _ _ t p hp1 hp2, if_neg ht, star_zero, zero_mul]
      · simp

/- English proof (translation)
Establish `hu` using `isUnit_of_uh hg.1`. Establish `key : ∀ b : Fin (2 * r + k + 1) → ℂ, g *ᵥ b = b → g⁻¹ *ᵥ b = b`. Introduce `b hb`. Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨uh_inv hg.1, fun a ha => ⟨key _ (hg.2 a ha).1, key _ (hg.2 a ha).2⟩⟩`.
-/
lemma glev_inv {i : Fin (r + 1)} {g : Mx k r} (hg : g ∈ Glev k r i) : g⁻¹ ∈ Glev k r i := by
  have hu := isUnit_of_uh hg.1
  have key : ∀ b : Fin (2 * r + k + 1) → ℂ, g *ᵥ b = b → g⁻¹ *ᵥ b = b := by
    intro b hb
    calc g⁻¹ *ᵥ b = g⁻¹ *ᵥ (g *ᵥ b) := by rw [hb]
      _ = b := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hg.1, fun a ha => ⟨key _ (hg.2 a ha).1, key _ (hg.2 a ha).2⟩⟩

/- English proof (translation)
Establish `hl` using `l.isLt`. Distinguish the cases in `h1 : p.val ≤ l.val`. Set `a : Fin r` to `⟨p.val, by omega⟩`. Establish `hpa : eI k r a = p` using `Fin.ext rfl`. Establish `ha : a.val < l.succ.val` using `by simp [a]; omega`.

Establish `hc1` using `col_of_fix (hg.2 a ha).1`. Establish `hc2` using `col_of_fix (hg.2 a ha).2`. Establish `hrow` using `row_of_fixed_col hg.1 (esI k r a) hc2`. Rewrite `hrow` using `[tau_es, hpa]`. Rewrite `hc1` using `[hpa]`.

Conclude with `⟨hrow, hc1⟩`. Set `a : Fin r` to `⟨2 * r + k - p.val, by omega⟩`. Establish `hpa : esI k r a = p` using `by apply Fin.ext; rw [esI_val]; simp [a]; omega`. Establish `ha : a.val < l.succ.val` using `by simp [a]; omega`. Establish `hc1` using `col_of_fix (hg.2 a ha).1`.

Establish `hc2` using `col_of_fix (hg.2 a ha).2`. Establish `hrow` using `row_of_fixed_col hg.1 (eI k r a) hc1`. Rewrite `hrow` using `[tau_e, hpa]`. Rewrite `hc2` using `[hpa]`. Conclude with `⟨hrow, hc2⟩`.
-/
lemma glev_out {l : Fin r} {g : Mx k r} (hg : g ∈ Glev k r l.succ) (p : Fin (2 * r + k + 1))
    (hp : ¬ (l.val < p.val ∧ p.val < 2 * r + k - l.val)) :
    (∀ q, g p q = if p = q then 1 else 0) ∧ (∀ q, g q p = if q = p then 1 else 0) := by
  have hl := l.isLt
  by_cases h1 : p.val ≤ l.val
  · let a : Fin r := ⟨p.val, by omega⟩
    have hpa : eI k r a = p := Fin.ext rfl
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (esI k r a) hc2
    rw [tau_es, hpa] at hrow
    rw [hpa] at hc1
    exact ⟨hrow, hc1⟩
  · let a : Fin r := ⟨2 * r + k - p.val, by omega⟩
    have hpa : esI k r a = p := by apply Fin.ext; rw [esI_val]; simp [a]; omega
    have ha : a.val < l.succ.val := by simp [a]; omega
    have hc1 := col_of_fix (hg.2 a ha).1
    have hc2 := col_of_fix (hg.2 a ha).2
    have hrow := row_of_fixed_col hg.1 (eI k r a) hc1
    rw [tau_e, hpa] at hrow
    rw [hpa] at hc2
    exact ⟨hrow, hc2⟩

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [bvec, Matrix.mulVec, dotProduct_single, mul_one]`. Rewrite using `[reflection_off_support _ _ p q hq1 hq2, Pi.single_apply]`.
-/
lemma reflection_fixes_basis_vector (l : Fin r) (c : ℂ) (q : Fin (2 * r + k + 1)) (hq1 : q ≠ eI k r l)
    (hq2 : q ≠ esI k r l) : w1 k r l c *ᵥ bvec q = bvec q := by
  funext p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one]
  rw [reflection_off_support _ _ p q hq1 hq2, Pi.single_apply]

/- English proof (translation)
Use `⟨uh_mul (weyl_cell_mem_unitary l c hc) hg.1, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hal : a.val < l.val` using `by simpa using ha`. Establish `ha' : a.val < l.succ.val` using `by simp; omega`. Establish `hl` using `l.isLt`. Take `⟨h1, h2⟩` from `hg.2 a ha'`.

Prove the components needed by the constructor for the conclusion. Rewrite using `[← Matrix.mulVec_mulVec, h1]`. Apply `reflection_fixes_basis_vector` to reduce the goal to its premises. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Rewrite `this` using `[eI_val, eI_val]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[eI_val, esI_val]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[← Matrix.mulVec_mulVec, h2]`. Apply `reflection_fixes_basis_vector` to reduce the goal to its premises. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact.

Rewrite `this` using `[esI_val, eI_val]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Rewrite `this` using `[esI_val, esI_val]`.

Use linear arithmetic over natural numbers and integers.
-/
lemma wg_glev (l : Fin r) (c : ℂ) (hc : c ≠ 0) {g₁ : Mx k r} (hg : g₁ ∈ Glev k r l.succ) :
    w1 k r l c * g₁ ∈ Glev k r l.castSucc := by
  refine ⟨uh_mul (weyl_cell_mem_unitary l c hc) hg.1, fun a ha => ?_⟩
  have hal : a.val < l.val := by simpa using ha
  have ha' : a.val < l.succ.val := by simp; omega
  have hl := l.isLt
  obtain ⟨h1, h2⟩ := hg.2 a ha'
  constructor
  · rw [← Matrix.mulVec_mulVec, h1]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [eI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [eI_val, esI_val] at this; omega
  · rw [← Matrix.mulVec_mulVec, h2]
    apply reflection_fixes_basis_vector
    · intro h; have := congrArg Fin.val h; rw [esI_val, eI_val] at this; omega
    · intro h; have := congrArg Fin.val h; rw [esI_val, esI_val] at this; omega

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single p]`. Distinguish the cases in `hp1 : p = eI k r l`. Substitute `hp1` using the available equality. Rewrite using `[h1, mul_zero]`. Distinguish the cases in `hp2 : p = esI k r l`.

Substitute `hp2` using the available equality. Rewrite using `[h2, mul_zero]`. Rewrite using `[reflection_off_support _ _ p p hp1 hp2, if_pos rfl, one_mul]`. Introduce `t _ ht`. Distinguish the cases in `ht1 : t = eI k r l`.

Substitute `ht1` using the available equality. Rewrite using `[h1, mul_zero]`. Distinguish the cases in `ht2 : t = esI k r l`. Substitute `ht2` using the available equality. Rewrite using `[h2, mul_zero]`.

Rewrite using `[reflection_off_support _ _ p t ht1 ht2, if_neg (Ne.symm ht), zero_mul]`. Simplify using the standard rewrite rules.
-/
lemma weyl_cell_mul_apply (l : Fin r) (c : ℂ) (A : Mx k r) (p q : Fin (2 * r + k + 1))
    (h1 : A (eI k r l) q = 0) (h2 : A (esI k r l) q = 0) : (w1 k r l c * A) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single p]
  · by_cases hp1 : p = eI k r l
    · subst hp1; rw [h1, mul_zero]
    · by_cases hp2 : p = esI k r l
      · subst hp2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p p hp1 hp2, if_pos rfl, one_mul]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, mul_zero]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, mul_zero]
      · rw [reflection_off_support _ _ p t ht1 ht2, if_neg (Ne.symm ht), zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single q]`. Distinguish the cases in `hq1 : q = eI k r l`. Substitute `hq1` using the available equality. Rewrite using `[h1, zero_mul]`. Distinguish the cases in `hq2 : q = esI k r l`.

Substitute `hq2` using the available equality. Rewrite using `[h2, zero_mul]`. Rewrite using `[reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one]`. Introduce `t _ ht`. Distinguish the cases in `ht1 : t = eI k r l`.

Substitute `ht1` using the available equality. Rewrite using `[h1, zero_mul]`. Distinguish the cases in `ht2 : t = esI k r l`. Substitute `ht2` using the available equality. Rewrite using `[h2, zero_mul]`.

Rewrite using `[reflection_off_support_row _ _ t q ht1 ht2, if_neg ht, mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma mul_weyl_cell_apply (l : Fin r) (c : ℂ) (A : Mx k r) (p q : Fin (2 * r + k + 1))
    (h1 : A p (eI k r l) = 0) (h2 : A p (esI k r l) = 0) : (A * w1 k r l c) p q = A p q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · by_cases hq1 : q = eI k r l
    · subst hq1; rw [h1, zero_mul]
    · by_cases hq2 : q = esI k r l
      · subst hq2; rw [h2, zero_mul]
      · rw [reflection_off_support _ _ q q hq1 hq2, if_pos rfl, mul_one]
  · intro t _ ht
    by_cases ht1 : t = eI k r l
    · subst ht1; rw [h1, zero_mul]
    · by_cases ht2 : t = esI k r l
      · subst ht2; rw [h2, zero_mul]
      · rw [reflection_off_support_row _ _ t q ht1 ht2, if_neg ht, mul_zero]
  · simp

end Formalism.FourierDecayAlt.Q.LeftMultiplicationRule
