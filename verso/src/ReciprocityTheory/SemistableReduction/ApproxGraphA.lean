import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.ApproximationGraph

open ComplexConjugate

def posPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then u k else 0

def negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : Fin r → ℂ := fun k => if (k : ℕ) < p then 0 else u k

def euc {r : ℕ} (u : Fin r → ℂ) : EuclideanSpace ℂ (Fin r) := WithLp.toLp 2 u

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma euc_add {r : ℕ} (u v : Fin r → ℂ) : euc (u + v) = euc u + euc v := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma euc_smul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) : euc (c • u) = c • euc u := rfl

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Simplify using `[normSq, euc]`.
-/
lemma normSq_eq_euc {r : ℕ} (u : Fin r → ℂ) : normSq u = ‖euc u‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [normSq, euc]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Unfold `posSq`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [euc, posPart, PiLp.toLp_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = ‖euc (posPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold posSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, posPart, PiLp.toLp_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Unfold `negSq`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [euc, negPart, PiLp.toLp_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = ‖euc (negPart p u)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  unfold negSq
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [euc, negPart, PiLp.toLp_apply]
  split_ifs <;> simp

/- English proof (translation)
Unfold `normSq posSq negSq`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma normSq_split (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : normSq u = posSq p u + negSq p u := by
  unfold normSq posSq negSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [posPart, negPart, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma posPart_add_negPart (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posPart p u + negPart p u = u := by
  funext k
  simp only [posPart, negPart, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [posPart, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma posPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    posPart p (u + v) = posPart p u + posPart p v := by
  funext k
  simp only [posPart, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [negPart, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma negPart_add (p : ℕ) {r : ℕ} (u v : Fin r → ℂ) :
    negPart p (u + v) = negPart p u + negPart p v := by
  funext k
  simp only [negPart, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [posPart, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma posPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    posPart p (c • u) = c • posPart p u := by
  funext k
  simp only [posPart, Pi.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [negPart, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma negPart_smul (p : ℕ) {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    negPart p (c • u) = c • negPart p u := by
  funext k
  simp only [negPart, Pi.smul_apply]
  split_ifs <;> simp

/- English proof (translation)
Simplify using `[euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]`.
-/
lemma inner_euc {r : ℕ} (x y : Fin r → ℂ) : inner ℂ (euc x) (euc y) = ∑ k, conj (x k) * y k := by
  simp [euc, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/- English proof (translation)
Rewrite using `[inner_euc, inner_euc, ← Finset.sum_sub_distrib]`. Unfold `jForm`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [sgn, posPart, negPart]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma jForm_eq (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) :
    jForm p x y = inner ℂ (euc (posPart p x)) (euc (posPart p y)) -
      inner ℂ (euc (negPart p x)) (euc (negPart p y)) := by
  rw [inner_euc, inner_euc, ← Finset.sum_sub_distrib]
  unfold jForm
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [sgn, posPart, negPart]
  split_ifs <;> simp

/- English proof (translation)
Unfold `jForm posSq negSq`. Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.conj_mul']`.

Unfold `sgn`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma jForm_self (p : ℕ) {r : ℕ} (y : Fin r → ℂ) :
    jForm p y y = ((posSq p y - negSq p y : ℝ) : ℂ) := by
  unfold jForm posSq negSq
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  unfold sgn
  split_ifs <;> simp

/- English proof (translation)
Establish `h1` using `posSq_eq p u`. Establish `h2` using `normSq_eq_euc u`. Establish `h3` using `normSq_split p u`. Apply the tactic sequence `have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity`. Establish `ha` using `norm_nonneg (euc (posPart p u))`.

Establish `hb` using `norm_nonneg (euc u)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_posPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (posPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := posSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (posPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

/- English proof (translation)
Establish `h1` using `negSq_eq p u`. Establish `h2` using `normSq_eq_euc u`. Establish `h3` using `normSq_split p u`. Apply the tactic sequence `have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity`. Establish `ha` using `norm_nonneg (euc (negPart p u))`.

Establish `hb` using `norm_nonneg (euc u)`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_negPart_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖euc (negPart p u)‖ ≤ ‖euc u‖ := by
  have h1 := negSq_eq p u
  have h2 := normSq_eq_euc u
  have h3 := normSq_split p u
  have hn : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity
  have ha := norm_nonneg (euc (negPart p u))
  have hb := norm_nonneg (euc u)
  by_contra h
  push_neg at h
  nlinarith

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma euc_zero {r : ℕ} : euc (0 : Fin r → ℂ) = 0 := by
  rfl

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_empty]`. Conclude with `euc_zero`. Introduce `a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]`.
-/
lemma euc_sum {r : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin r → ℂ) :
    euc (∑ j ∈ s, f j) = ∑ j ∈ s, euc (f j) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact euc_zero
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, euc_add, ih]

/- English proof (translation)
Establish `h'` using `congrArg WithLp.ofLp h`. Simplify `h'` using `[euc]`.
-/
lemma euc_eq_zero {r : ℕ} {w : Fin r → ℂ} (h : euc w = 0) : w = 0 := by
  have h' := congrArg WithLp.ofLp h
  simpa [euc] using h'

/- English proof (translation)
Establish `h` using `Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)`. Rewrite using `[EuclideanSpace.norm_eq]`. Simplify `h` using `[euc]`.
-/
lemma sum_norm_le_sqrt {r : ℕ} (w : Fin r → ℂ) : ∑ j, ‖w j‖ ≤ √(r : ℝ) * ‖euc w‖ := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ)) (fun j => ‖w j‖)
  rw [EuclideanSpace.norm_eq]
  simpa [euc] using h

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]`. Simplify using `[Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_smul_eq {r : ℕ} (X : Fin r → Fin r → ℂ) (w : Fin r → ℂ) (c : ℂ) :
    ∑ j, w j • X j = c • w + ∑ j, w j • (X j - c • (Pi.single j 1 : Fin r → ℂ)) := by
  funext k
  simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Pi.single_apply]
  simp [Finset.mul_sum]
  ring

/- English proof (translation)
Establish `he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ`. Introduce `j`. Distinguish the cases in `hj : (j : ℕ) < p`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Establish `h1` using `hX j hj`.

Rewrite `h1` using `[normSq_eq_euc]`. Establish `ha` using `norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use the polynomial consequences of the given equalities and inequalities.

Rewrite using `[hw j (not_lt.mp hj)]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[euc_sum]`. Simplify using `only [euc_smul]`.

Use `_ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _`. Use `_ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by`. Simplify using `only [norm_smul]`. Use `_ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j`. Use `_ = μ * ∑ j, ‖w j‖ := by`.

Rewrite using `[Finset.mul_sum]`. Simplify using `only [mul_comm]`. Use `_ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ`. Use `_ = √(r : ℝ) * μ * ‖euc w‖ := by ring`.
-/
lemma norm_err_le {r p : ℕ} {μ R : ℝ} (X : Fin r → Fin r → ℂ)
    (hX : ∀ j : Fin r, (j : ℕ) < p → normSq (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2)
    (hμ : 0 ≤ μ) (w : Fin r → ℂ) (hw : ∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) :
    ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖ ≤ √(r : ℝ) * μ * ‖euc w‖ := by
  have he : ∀ j : Fin r, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ ≤ ‖w j‖ * μ := by
    intro j
    by_cases hj : (j : ℕ) < p
    · refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h1 := hX j hj
      rw [normSq_eq_euc] at h1
      have ha := norm_nonneg (euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))
      by_contra h
      push_neg at h
      nlinarith
    · rw [hw j (not_lt.mp hj)]
      simp
  calc ‖euc (∑ j, w j • (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ)))‖
      = ‖∑ j, w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        rw [euc_sum]
        simp only [euc_smul]
    _ ≤ ∑ j, ‖w j • euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := norm_sum_le _ _
    _ = ∑ j, ‖w j‖ * ‖euc (X j - (R : ℂ) • (Pi.single j 1 : Fin r → ℂ))‖ := by
        simp only [norm_smul]
    _ ≤ ∑ j, ‖w j‖ * μ := Finset.sum_le_sum fun j _ => he j
    _ = μ * ∑ j, ‖w j‖ := by
        rw [Finset.mul_sum]
        simp only [mul_comm]
    _ ≤ μ * (√(r : ℝ) * ‖euc w‖) := mul_le_mul_of_nonneg_left (sum_norm_le_sqrt w) hμ
    _ = √(r : ℝ) * μ * ‖euc w‖ := by ring

end ReciprocityTheory.MultiplicativeHeights.ApproximationGraph
