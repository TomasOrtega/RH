import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpB
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

/- English proof (translation)
Unfold `inG Jm sg`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrFun (congrFun h i) j` as an intermediate fact. Rewrite `this` using `[Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply]`. Then use the resulting hypothesis.

Introduce `h`. Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply]`. Conclude with `h i j`.
-/
theorem inG_iff_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    inG ε X ↔ ∀ i j, star (X j i) * sg ε j + sg ε i * X i j = 0 := by
  unfold inG Jm sg
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at this
  · intro h
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    exact h i j

/- English proof (translation)
Rewrite using `[inG_iff_entry]`. Introduce `i j`. Simplify using `only [gMat, Matrix.add_apply, kMat, pmat, sg]`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Establish `h1 : ¬ j < i` using `lt_asymm h`.

Establish `h2 : i ≠ j` using `ne_of_lt h`. Distinguish the cases in `he : ε i = ε j`. Simplify using `[h, h1, h2, h2.symm, he]`. Establish `he' : ε j ≠ ε i` using `Ne.symm he`. Simplify using `[h, h1, h2, h2.symm, he, he']`.

Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢`. Apply the tactic sequence `apply Complex.ext <;> simp <;> split_ifs <;> simp`. Establish `h1 : ¬ i < j` using `lt_asymm h`. Establish `h2 : j ≠ i` using `ne_of_lt h`.

Distinguish the cases in `he : ε i = ε j`. Apply the tactic sequence `simp [h, h1, h2, h2.symm, he] split_ifs <;> ring`. Establish `he' : ε j ≠ ε i` using `Ne.symm he`. Simplify using `[h, h1, h2, h2.symm, he, he']`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>`.

Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢`.
-/
theorem gMat_inG {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  rw [inG_iff_entry]
  intro i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, sg]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢
  · apply Complex.ext <;> simp <;> split_ifs <;> simp
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
      split_ifs <;> ring
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢

def gCo (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Z a a).im, fun p => Z p.1.1 p.1.2), fun p => Z p.1.1 p.1.2)

/- English proof (translation)
Take `⟨⟨w, x⟩, z⟩` from `s`. Use `Prod.ext (Prod.ext ?_ ?_) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a`. Simplify using `[gCo, gMat, kMat, pmat]`. Use function extensionality and compare the values at `p`.

Take `⟨⟨a, b⟩, hab, he⟩` from `p`. Establish `h1 : a ≠ b` using `(ne_of_lt hab).symm`. Establish `h2 : ¬ a < b` using `lt_asymm hab`. Simplify using `[gCo, gMat, kMat, pmat, h1, hab, he, h2]`. Use function extensionality and compare the values at `p`.

Take `⟨⟨a, b⟩, hab, he⟩` from `p`. Establish `h1 : a ≠ b` using `(ne_of_lt hab).symm`. Establish `h2 : ¬ a < b` using `lt_asymm hab`. Simplify using `[gCo, gMat, kMat, pmat, h1, hab, he, h2]`.
-/
theorem gCo_gMat {ε : Fin n → Bool} (s : GCo ε) : gCo ε (gMat s) = s := by
  obtain ⟨⟨w, x⟩, z⟩ := s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gCo, gMat, kMat, pmat]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]

/- English proof (translation)
Rewrite `hZ` using `[inG_iff_entry]`. Use extensionality with `i j`. Establish `hij` using `hZ i j`. Simplify using `only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases.

Establish `h1 : ¬ j < i` using `lt_asymm h`. Establish `h2 : i ≠ j` using `ne_of_lt h`. Apply the tactic sequence `cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;> first | linear_combination hij | linear_combination -hij`. Apply the tactic sequence `apply Complex.ext <;> simp`. Use `congrArg Complex.re hij` as an intermediate fact.

Apply the tactic sequence `cases hi : ε i <;> simp [hi] at this <;> linarith`. Establish `h1 : ¬ i < j` using `lt_asymm h`. Establish `h2 : j ≠ i` using `ne_of_lt h`. Simplify using `[h, h1, h2.symm]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem gMat_gCo {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    gMat (gCo ε Z) = Z := by
  rw [inG_iff_entry] at hZ
  ext i j
  have hij := hZ i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;>
      first | linear_combination hij | linear_combination -hij
  · apply Complex.ext <;> simp
    · have := congrArg Complex.re hij
      cases hi : ε i <;> simp [hi] at this <;> linarith
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    simp [h, h1, h2.symm]
    split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HExp
