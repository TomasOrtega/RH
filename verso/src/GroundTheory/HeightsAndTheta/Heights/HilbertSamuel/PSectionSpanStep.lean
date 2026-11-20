import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionSpanStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepHomog
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSerreGraded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SectionSpanStep

variable {K : Type} [Fintype K] {ι : K → Type} {Ω : Type} [Field Ω]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mul_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n j : ℕ} {s t : Ω} (hs : s ∈ chartLat y a n)
    (ht : t ∈ chartLat y a j) : s * t ∈ chartLat y a (n + j) := by
  intro c hc
  have h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) =
      (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_add₀ (hc k)]
    congr 1
    push_cast
    ring
  rw [h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) =
      (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]
  exact MulMemClass.mul_mem (hs c hc) (ht c hc)

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem prod_pow_mem {y : (Σ k, ι k) → Ω} {a : K → ℤ} {q : ℕ} {w : Fin q → Ω}
    (hw : ∀ j, w j ∈ chartLat y a 1) (ν : Fin q → ℕ) (S : Finset (Fin q)) :
    ∏ j ∈ S, w j ^ ν j ∈ chartLat y a (∑ j ∈ S, ν j) := by
  have hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e := by
    intro j e
    induction e with
    | zero => intro c _; simp
    | succ e ih => rw [pow_succ]; exact mul_mem ih (hw j)
  refine Finset.induction_on S ?_ ?_
  · intro c _
    simp
  · intro j S hj ih
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact mul_mem (hpow j (ν j)) ih

end SectionSpanStep

open SectionSpanStep in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

A detailed English derivation is pending.
-/
theorem SectionSpanStep.proof (hH : SpanStepHomog.Statement) (hS : SerreGraded.Statement) :
    SectionSpanStep.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen
  obtain ⟨m, r, t, ht, hloc⟩ := hH K ι Ω y a q w hy hw hgen
  have hne : ∃ j, w j ≠ 0 := by
    by_contra h
    push Not at h
    choose c hc using hy
    obtain ⟨u, -, hu⟩ := hgen c hc
    simp [h] at hu
  obtain ⟨n₀, hn₀⟩ := hS Ω q r w (fun _ => m) t hne
  refine ⟨max n₀ m, fun n hn s hs => ?_⟩
  have hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1) :=
    hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj
  refine (AddSubgroup.closure_le _).2 ?_ hs'
  rintro x ⟨l, μ, hdeg, rfl⟩
  have hdeg : m + ∑ i, μ i = n + 1 := hdeg
  obtain ⟨j, hj⟩ : ∃ j, 0 < μ j := by
    by_contra h
    push Not at h
    have h0 : ∑ i, μ i = 0 := Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)
    omega
  set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'
  have hμ : μ = μ' + Pi.single j 1 := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp [hμ']
      omega
    · simp [hμ', hij]
  have hsum : ∑ i, μ i = ∑ i, μ' i + 1 := by
    rw [hμ]
    simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
    simp
  have hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j := by
    rw [hμ]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_eq_single j]
    · simp
    · intro i hi
      simp [hi]
  apply AddSubgroup.subset_closure
  refine ⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩
  have hmem := mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)
  have hdeg' : m + ∑ i, μ' i = n := by omega
  rwa [hdeg'] at hmem

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
