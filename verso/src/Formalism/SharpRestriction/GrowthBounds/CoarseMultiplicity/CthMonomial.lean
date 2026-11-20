import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.TopOddNeEnd
import Formalism.SharpRestriction.GrowthBounds.PolBridge

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Cth

variable {K : Type} [Field K] {σ : Type}

def cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) : MvPolynomial σ K :=
  monomial (Finsupp.single v n) (1 : K) * divDer (Finsupp.single v n) F

/- English proof (translation)
Unfold `cth`. Rewrite using `[eig_one]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Finsupp.prod_single_index (by simp)]`.
-/
theorem coeff_cth (v : σ) (n : ℕ) (F : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    coeff μ (cth v n F) = coeff μ F * (((μ v).choose n : ℕ) : K) := by
  unfold cth
  rw [eig_one]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [Finsupp.prod_single_index (by simp)]

/- English proof (translation)
Use extensionality with `μ`. Simplify using `only [coeff_cth, coeff_add, add_mul]`.
-/
theorem cth_add (v : σ) (n : ℕ) (F G : MvPolynomial σ K) : cth v n (F + G) = cth v n F + cth v n G := by
  ext μ
  simp only [coeff_cth, coeff_add, add_mul]

/- English proof (translation)
Use extensionality with `μ`. Simplify using `only [coeff_cth, coeff_smul, smul_eq_mul, mul_assoc]`.
-/
theorem cth_smul (v : σ) (n : ℕ) (c : K) (F : MvPolynomial σ K) : cth v n (c • F) = c • cth v n F := by
  ext μ
  simp only [coeff_cth, coeff_smul, smul_eq_mul, mul_assoc]

def cthL (v : σ) (n : ℕ) : MvPolynomial σ K →ₗ[K] MvPolynomial σ K where
  toFun := cth v n
  map_add' := cth_add v n
  map_smul' := cth_smul v n

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cthL_apply (v : σ) (n : ℕ) (F : MvPolynomial σ K) : cthL v n F = cth v n F := rfl

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_cth, coeff_monomial, coeff_monomial]`. Use `split_ifs with h`. Rewrite using `[h]`. Rewrite using `[zero_mul]`.
-/
theorem cth_monomial (v : σ) (n : ℕ) (e : σ →₀ ℕ) (c : K) :
    cth v n (monomial e c) = monomial e (c * (((e v).choose n : ℕ) : K)) := by
  classical
  ext μ
  rw [coeff_cth, coeff_monomial, coeff_monomial]
  split_ifs with h
  · rw [h]
  · rw [zero_mul]

/- English proof (translation)
Use extensionality with `μ`. Simplify using `[coeff_cth]`.
-/
theorem cth_zero (v : σ) (F : MvPolynomial σ K) : cth v 0 F = F := by
  ext μ
  simp [coeff_cth]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `add F F' hF hF'`. Rewrite using `[add_mul, cth_add, hF, hF', ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun ab _ => by rw [cth_add, add_mul]`. Consider the case `monomial e c`.

Proceed by induction on `G using MvPolynomial.induction_on' with`. Consider the case `add G G' hG hG'`. Rewrite using `[mul_add, cth_add, hG, hG', ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun ab _ => by rw [cth_add, mul_add]`. Consider the case `monomial e' c'`.

Rewrite using `[monomial_mul, cth_monomial, Finsupp.add_apply, Nat.add_choose_eq, Nat.cast_sum, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun ab _ => ?_` and prove the remaining obligations. Rewrite using `[cth_monomial, cth_monomial, monomial_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cth_mul (v : σ) (n : ℕ) (F G : MvPolynomial σ K) :
    cth v n (F * G) = ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal n, cth v ab.1 F * cth v ab.2 G := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add F F' hF hF' =>
    rw [add_mul, cth_add, hF, hF', ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, add_mul]
  | monomial e c =>
    induction G using MvPolynomial.induction_on' with
    | add G G' hG hG' =>
      rw [mul_add, cth_add, hG, hG', ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun ab _ => by rw [cth_add, mul_add]
    | monomial e' c' =>
      rw [monomial_mul, cth_monomial, Finsupp.add_apply, Nat.add_choose_eq, Nat.cast_sum, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun ab _ => ?_
      rw [cth_monomial, cth_monomial, monomial_mul]
      congr 1
      push_cast
      ring

/- English proof (translation)
Use extensionality with `μ`. Rewrite using `[coeff_cth, coeff_zero]`. Distinguish the cases in `h : μ ∈ F.support`. Rewrite using `[hF μ h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hn)]`. Simplify using the standard rewrite rules.

Rewrite using `[notMem_support_iff.1 h, zero_mul]`.
-/
theorem cth_free (v : σ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) {n : ℕ} (hn : n ≠ 0) :
    cth v n F = 0 := by
  ext μ
  rw [coeff_cth, coeff_zero]
  by_cases h : μ ∈ F.support
  · rw [hF μ h, Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hn)]
    simp
  · rw [notMem_support_iff.1 h, zero_mul]

/- English proof (translation)
Rewrite using `[cth_mul, Finset.sum_eq_single (0, n)]`. Rewrite using `[cth_zero]`. Introduce and unpack `⟨a, b⟩ hab hne`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hab` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only [zero_add] at hab`. Conclude with `hne (by rw [hab])`. Rewrite using `[cth_free v hF ha, zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h`.
-/
theorem cth_mul_free (v : σ) (n : ℕ) {F : MvPolynomial σ K} (hF : ∀ μ ∈ F.support, μ v = 0) (G : MvPolynomial σ K) :
    cth v n (F * G) = F * cth v n G := by
  classical
  rw [cth_mul, Finset.sum_eq_single (0, n)]
  · rw [cth_zero]
  · rintro ⟨a, b⟩ hab hne
    have ha : a ≠ 0 := by
      rintro rfl
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
      simp only [zero_add] at hab
      exact hne (by rw [hab])
    rw [cth_free v hF ha, zero_mul]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp)) h

/- English proof (translation)
Proceed by induction on `j generalizing l with`. Consider the case `zero`. Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using `[cth_zero]`. Rewrite using `[pow_zero, Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_smul]`.

Use `cth_free v ?_ hl.ne'` and prove the remaining obligations. Introduce `μ hμ`. Establish `: μ = 0`. Assume the negation of the conclusion as `hne`. Rewrite `hμ` using `[mem_support_iff, coeff_one, if_neg (Ne.symm hne)]`.

Conclude with `hμ rfl`. Rewrite using `[this]`. Both sides reduce to the same expression. Consider the case `succ j ih`. Rewrite using `[pow_succ, cth_mul]`.

Break down `Nat.eq_zero_or_pos l with rfl | hl` into its components or cases. Simplify using `[cth_zero, pow_succ]`. Take `⟨l', rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hl.ne'`. Establish `hsub : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (l' + 1), ab ≠ (l' + 1, 0) → ab ≠ (l', 1) → cth v ab.1 (E ^ j) * cth v ab.2 E = 0`. Introduce and unpack `⟨a, b⟩ hab hn1 hn2`.

Rewrite `hab` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Simplify using `only at hab`. Establish `hb : 2 ≤ b`. Assume the negation of the conclusion as `hb`. Establish `: b = 0 ∨ b = 1` using `by omega`.

Break down `this with rfl | rfl` into its components or cases. Conclude with `hn1 (by simp at hab; rw [hab])`. Conclude with `hn2 (by have : a = l' := by omega`. Rewrite using `[this])`. Rewrite using `[h2 b hb, mul_zero]`.

Establish `hne : ((l' + 1, 0) : ℕ × ℕ) ≠ (l', 1)` using `by simp`. Rewrite using `[← Finset.sum_subset (s₁ := {(l' + 1, 0), (l', 1)}) (by`. Introduce `x hx`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hx`. Apply the tactic sequence `rcases hx with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal])`.

Use the proof step `(by`. Introduce `x hx hx'`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'`. Conclude with `hsub x hx hx'.1 hx'.2),`. Use the proof step `Finset.sum_pair hne]`.

Simplify using `only`. Rewrite using `[ih, ih, cth_zero, h1, Nat.choose_succ_succ' j l']`. Distinguish the cases in `hlj : l' + 1 ≤ j`. Establish `e1 : j + 1 - (l' + 1) = (j - (l' + 1)) + 1` using `by omega`. Establish `e2 : j - l' = (j - (l' + 1)) + 1` using `by omega`.

Rewrite using `[e1, e2]`. Use `push_cast`. Simplify using `only [smul_eq_C_mul, pow_succ, map_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `e0 : j.choose (l' + 1) = 0` using `Nat.choose_eq_zero_of_lt (by omega)`.

Establish `e1 : j + 1 - (l' + 1) = j - l'` using `by omega`. Rewrite using `[e0, e1]`. Simplify using `only [Nat.cast_zero, zero_smul, zero_mul, zero_add, add_zero, smul_eq_C_mul, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cth_pow (v : σ) {E m : MvPolynomial σ K} (h1 : cth v 1 E = m) (h2 : ∀ a, 2 ≤ a → cth v a E = 0) (j l : ℕ) :
    cth v l (E ^ j) = ((j.choose l : ℕ) : K) • (E ^ (j - l) * m ^ l) := by
  classical
  induction j generalizing l with
  | zero =>
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero]
    · rw [pow_zero, Nat.choose_eq_zero_of_lt hl, Nat.cast_zero, zero_smul]
      refine cth_free v ?_ hl.ne'
      intro μ hμ
      have : μ = 0 := by
        by_contra hne
        rw [mem_support_iff, coeff_one, if_neg (Ne.symm hne)] at hμ
        exact hμ rfl
      rw [this]; rfl
  | succ j ih =>
    rw [pow_succ, cth_mul]
    rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp [cth_zero, pow_succ]
    · obtain ⟨l', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
      have hsub : ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal (l' + 1), ab ≠ (l' + 1, 0) → ab ≠ (l', 1) →
          cth v ab.1 (E ^ j) * cth v ab.2 E = 0 := by
        rintro ⟨a, b⟩ hab hn1 hn2
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hab
        simp only at hab
        have hb : 2 ≤ b := by
          by_contra hb
          have : b = 0 ∨ b = 1 := by omega
          rcases this with rfl | rfl
          · exact hn1 (by simp at hab; rw [hab])
          · exact hn2 (by have : a = l' := by omega
                          rw [this])
        rw [h2 b hb, mul_zero]
      have hne : ((l' + 1, 0) : ℕ × ℕ) ≠ (l', 1) := by simp
      rw [← Finset.sum_subset (s₁ := {(l' + 1, 0), (l', 1)})
        (by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> simp [Finset.HasAntidiagonal.mem_antidiagonal])
        (by
          intro x hx hx'
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx'
          exact hsub x hx hx'.1 hx'.2),
        Finset.sum_pair hne]
      simp only
      rw [ih, ih, cth_zero, h1, Nat.choose_succ_succ' j l']
      by_cases hlj : l' + 1 ≤ j
      · have e1 : j + 1 - (l' + 1) = (j - (l' + 1)) + 1 := by omega
        have e2 : j - l' = (j - (l' + 1)) + 1 := by omega
        rw [e1, e2]
        push_cast
        simp only [smul_eq_C_mul, pow_succ, map_add]
        ring
      · have e0 : j.choose (l' + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
        have e1 : j + 1 - (l' + 1) = j - l' := by omega
        rw [e0, e1]
        simp only [Nat.cast_zero, zero_smul, zero_mul, zero_add, add_zero, smul_eq_C_mul, pow_succ]
        ring

end Cth

end Formalism.MainNotions.ColumnSystems.Pf
