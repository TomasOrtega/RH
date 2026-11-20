import Mathlib
import Formalism.PeriodIntegrals.ExistsGaugeMeasureForEachRank
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CircleGaugeAction.DglApplyOff

noncomputable section

open Matrix Filter Topology

namespace PI.ExistsGaugeMeasureForEachRank.W

variable {r : ℕ}

def dz (r : ℕ) (z : ℂ) : Mat 0 r := diagonal (Pi.single (cI r) z)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
lemma exp_dz (z : ℂ) : NormedSpace.exp (dz r z) = dgl r (Complex.exp z) := by
  rw [dz, Matrix.exp_diagonal, dgl]
  congr 1
  funext i
  rw [Pi.coe_exp]
  by_cases h : i = cI r
  · subst h
    simp [← Complex.exp_eq_exp_ℂ]
  · simp [h]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
lemma smul_dz (t z : ℂ) : t • dz r z = dz r (t * z) := by
  rw [dz, dz, ← Matrix.diagonal_smul, ← Pi.single_smul', smul_eq_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma dz_mem_lie (s : ℝ) : dz r ((s : ℂ) * Complex.I) ∈ lieOf (UWb 0 r) := by
  intro t
  rw [smul_dz, exp_dz]
  apply dgl_mem
  rw [conj_mul_iff, Complex.norm_exp]
  simp

set_option backward.isDefEq.respectTransparency false in
open scoped Norms.Operator in
/- English proof (translation)
Equip the data with the indicated structure. Equip the data with the indicated structure. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma entry_zero {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) (i j : Fin (2 * r + 0 + 1))
    (hij : ¬ (i = cI r ∧ j = cI r)) : X i j = 0 := by
  letI : NormedRing (Mat 0 r) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mat 0 r) := Matrix.linftyOpNormedAlgebra
  have hconst : ∀ t : ℝ, (NormedSpace.exp (t • X)) i j = (1 : Mat 0 r) i j := by
    intro t
    have hm := hX t
    rw [Complex.coe_smul] at hm
    rw [eq_dgl hm, dgl_apply_off _ _ _ hij]
  let L : Mat 0 r →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have hd := (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const X (0 : ℝ)))
  have hfun : (L ∘ fun t : ℝ => NormedSpace.exp (t • X)) = fun _ => (1 : Mat 0 r) i j :=
    funext hconst
  rw [hfun] at hd
  have h0 := hd.unique (hasDerivAt_const (0 : ℝ) ((1 : Mat 0 r) i j))
  simpa [L] using h0

/- English proof (translation)
By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
lemma eq_dz_of_lie {X : Mat 0 r} (hX : X ∈ lieOf (UWb 0 r)) : X = dz r (X (cI r) (cI r)) := by
  ext i j
  by_cases h : i = cI r ∧ j = cI r
  · obtain ⟨rfl, rfl⟩ := h
    simp [dz]
  · rw [entry_zero hX i j h, dz, diagonal_apply]
    split_ifs with hij
    · subst hij
      have hi : i ≠ cI r := fun hi => h ⟨hi, hi⟩
      simp [hi]
    · rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem lieOf_iff (X : Mat 0 r) :
    X ∈ lieOf (UWb 0 r) ↔ ∃ s : ℝ, X = dz r ((s : ℂ) * Complex.I) := by
  constructor
  · intro hX
    have hX' := eq_dz_of_lie hX
    set x := X (cI r) (cI r)
    have h1 := hX 1
    rw [hX', Complex.ofReal_one, one_smul, exp_dz] at h1
    have hn := (conj_mul_iff _).1 (dgl_norm h1)
    rw [Complex.norm_exp, Real.exp_eq_one_iff] at hn
    refine ⟨x.im, hX'.trans ?_⟩
    congr 1
    apply Complex.ext <;> simp [hn]
  · rintro ⟨s, rfl⟩
    exact dz_mem_lie s

def v0 (r : ℕ) : EuclideanSpace ℝ (Fin (2 * r + 0 + 1) × Fin (2 * r + 0 + 1) × Bool) :=
  EuclideanSpace.single (cI r, cI r, true) 1

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
lemma norm_v0_eq_one : ‖v0 r‖ = 1 := by
  simp [v0]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
lemma v0_ne : v0 r ≠ 0 := by
  intro h
  have := norm_v0_eq_one (r := r)
  rw [h, norm_zero] at this
  exact zero_ne_one this

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
lemma realify_dz (s : ℝ) :
    (WithLp.equiv 2 _).symm (realifyFun (dz r ((s : ℂ) * Complex.I))) = s • v0 r := by
  ext ⟨i, j, b⟩
  simp only [WithLp.equiv_symm_apply, realifyFun, v0, dz, diagonal_apply, PiLp.smul_apply,
    EuclideanSpace.single_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i = cI r
    · subst hi
      cases b <;> simp
    · cases b <;> simp [hi]
  · cases b <;> simp [hij] <;> intro hi hj <;> exact absurd (hi.trans hj.symm) hij

/- English proof (translation)
By extensionality, compare the relevant components. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
lemma ofRealCoords_smul_centerCoord (s : ℝ) : unrealify (s • v0 r) = dz r ((s : ℂ) * Complex.I) := by
  ext i j
  apply Complex.ext
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
  · simp only [unrealify, v0, dz, diagonal_apply, PiLp.smul_apply, EuclideanSpace.single_apply,
      smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = cI r
      · subst hi
        simp
      · simp [hi]
    · simp [hij]
      intro hi hj
      exact absurd (hi.trans hj.symm) hij

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lieE_eq : lieE (UWb 0 r) = Submodule.span ℝ {v0 r} := by
  apply le_antisymm
  · rw [lieE, Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    obtain ⟨s, rfl⟩ := (lieOf_iff X).1 hX
    beta_reduce
    rw [realify_dz]
    exact Submodule.smul_mem _ s (Submodule.subset_span rfl)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    apply Submodule.subset_span
    refine ⟨dz r ((1 : ℝ) * Complex.I), dz_mem_lie 1, ?_⟩
    beta_reduce
    rw [realify_dz, one_smul]

end PI.ExistsGaugeMeasureForEachRank.W
