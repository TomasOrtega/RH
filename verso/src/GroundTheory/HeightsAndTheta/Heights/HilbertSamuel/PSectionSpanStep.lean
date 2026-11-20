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
Introduce `c hc`. Establish `h : ∏ k, y ⟨k, c k⟩ ^ (-(((n + j : ℕ) : ℤ) * a k)) = (∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_add₀ (hc k)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, show s * t * ((∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) = (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * (t * ∏ k, y ⟨k, c k⟩ ^ (-((j : ℤ) * a k))) by ring]`. Conclude with `MulMemClass.mul_mem (hs c hc) (ht c hc)`.
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
Establish `hpow : ∀ (j : Fin q) (e : ℕ), w j ^ e ∈ chartLat y a e`. Introduce `j e`. Proceed by induction on `e with`. Consider the case `zero => intro c _`. Simplify using the standard rewrite rules.

Consider the case `succ e ih => rw [pow_succ]`. Conclude with `mul_mem ih (hw j)`. Use `Finset.induction_on S ?_ ?_` and prove the remaining obligations. Introduce `c _`. Simplify using the standard rewrite rules.

Introduce `j S hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `mul_mem (hpow j (ν j)) ih`.
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
Introduce `K _ ι _ Ω _ y a q w hy hw hgen`. Take `⟨m, r, t, ht, hloc⟩` from `hH K ι Ω y a q w hy hw hgen`. Establish `hne : ∃ j, w j ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Use `choose c hc using hy`. Take `⟨u, -, hu⟩` from `hgen c hc`. Simplify using `[h] at hu`. Take `⟨n₀, hn₀⟩` from `hS Ω q r w (fun _ => m) t hne`. Use `⟨max n₀ m, fun n hn s hs => ?_⟩` and prove the remaining obligations.

Establish `hs' : s ∈ gradedSpan w (fun _ => m) t (n + 1)` using `hn₀ (n + 1) (by omega) s fun j hj => hloc (n + 1) s hs j hj`. Use `(AddSubgroup.closure_le _).2 ?_ hs'` and prove the remaining obligations. Introduce and unpack `x ⟨l, μ, hdeg, rfl⟩`. Establish `hdeg : m + ∑ i, μ i = n + 1` using `hdeg`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, 0 < μ j := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Establish `h0 : ∑ i, μ i = 0` using `Finset.sum_eq_zero fun i _ => Nat.le_zero.1 (h i)`. Use linear arithmetic over natural numbers and integers. Use `set μ' : Fin q → ℕ := μ - Pi.single j 1 with hμ'`.

Establish `hμ : μ = μ' + Pi.single j 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hμ']`.

Use linear arithmetic over natural numbers and integers. Simplify using `[hμ', hij]`. Establish `hsum : ∑ i, μ i = ∑ i, μ' i + 1`. Rewrite using `[hμ]`. Simplify using `only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']`.

Simplify using the standard rewrite rules. Establish `hprod : ∏ i, w i ^ μ i = (∏ i, w i ^ μ' i) * w j`. Rewrite using `[hμ]`. Simplify using `only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]`. Use `congr 1`.

Rewrite using `[Fintype.prod_eq_single j]`. Simplify using the standard rewrite rules. Introduce `i hi`. Simplify using `[hi]`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises.

Use `⟨t l * ∏ i, w i ^ μ' i, ?_, j, by rw [hprod, mul_assoc]⟩` and prove the remaining obligations. Establish `hmem` using `mul_mem (ht l) (prod_pow_mem hw μ' Finset.univ)`. Establish `hdeg' : m + ∑ i, μ' i = n` using `by omega`. Rewrite `hmem` using `[hdeg']`. Then use the resulting hypothesis.
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
