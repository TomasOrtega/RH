import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import Development.WeilBound.CoreStatements.PluriharmonicCharts.LeviDiagonalOfIsPeriodChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereDensityDiagonalLeviStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.per_point

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨by simpa using contDiffAt_const, fun w => by simp [levi]⟩`. Consider the case `insert a s ha ih`. Simplify using `only [Finset.sum_insert ha]`. Use `⟨(contDiffAt_const.mul (hf a)).add ih.1, fun w => ?_⟩` and prove the remaining obligations.

Establish `h` using `levi_add_smul (c a) ih.1 (hf a) w`. Rewrite `h` using `[ih.2]`. Simplify using `only [add_comm (c a * _)]`. Conclude with `h`.
-/
theorem levi_sum {e : ℕ} {σ : Type} (s : Finset σ) (c : σ → ℝ) (f : σ → (Fin e → ℂ) → ℝ) (z : Fin e → ℂ)
    (hf : ∀ a, ContDiffAt ℝ 2 (f a) z) :
    ContDiffAt ℝ 2 (fun y => ∑ a ∈ s, c a * f a y) z ∧
      ∀ w, levi (fun y => ∑ a ∈ s, c a * f a y) z w = ∑ a ∈ s, c a * levi (f a) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using contDiffAt_const, fun w => by simp [levi]⟩
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    refine ⟨(contDiffAt_const.mul (hf a)).add ih.1, fun w => ?_⟩
    have h := levi_add_smul (c a) ih.1 (hf a) w
    rw [ih.2] at h
    simp only [add_comm (c a * _)]
    exact h

/- English proof (translation)
Rewrite using `[← Finset.prod_subtype (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2) (by simp) (fun p => f p.1 p.2), Finset.prod_filter, Fintype.prod_prod_type]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_filter]`. Use `congr 1`. Use extensionality with `l`.

Simplify using the standard rewrite rules.
-/
theorem prod_pairs {N : ℕ} (f : Fin N → Fin N → ℝ) :
    ∏ q : Pairs N, f q.1.1 q.1.2 = ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, f i l := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin N × Fin N => p.1 < p.2) (by simp)
    (fun p => f p.1 p.2), Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext l
  simp

/- English proof (translation)
Rewrite using `[Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]`. Establish `h1 : ∀ i : Fin N, (∑ l : Fin N, if i < l then 1 else 0) = N - 1 - (i : ℕ)`. Introduce `i`. Rewrite using `[← Finset.sum_filter, ← Finset.card_eq_sum_ones]`. Rewrite using `[show Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i by ext l; simp]`.

Conclude with `Fin.card_Ioi i`. Repeatedly rewrite using `[h1]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]`. Rewrite using `[Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id, Nat.choose_two_right]`.
-/
theorem card_pairs (N : ℕ) : Fintype.card (Pairs N) = N.choose 2 := by
  classical
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  have h1 : ∀ i : Fin N, (∑ l : Fin N, if i < l then 1 else 0) = N - 1 - (i : ℕ) := by
    intro i
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    rw [show Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i by ext l; simp]
    exact Fin.card_Ioi i
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  rw [Finset.sum_range_reflect (fun i => i) N, Finset.sum_range_id, Nat.choose_two_right]

end PositivityTheory.Xgp.per_point

open PositivityTheory.Xgp.per_point in

/- English proof (translation)
Introduce `e X _ A Ψ _ _ N j hj pot x V g hP he k hx`. Take `⟨Lm, hcd, hlevi, hinj⟩` from `per_diag.levi_diagonal_of_isPeriodChart e X A Ψ N j hj pot x V g hP k hx`. Establish `hcard : Fintype.card (Ψ × Pairs N) = e`. Rewrite using `[Fintype.card_prod, card_pairs, he, antisymDegree]`. Set `eq : Fin e ≃ Ψ × Pairs N` to `(Fintype.equivFinOfCardEq hcard).symm`.

Set `M : Matrix (Fin e) (Fin e) ℂ` to `LinearMap.toMatrix' ((LinearMap.funLeft ℂ ℂ (eq : Fin e → Ψ × Pairs N)) ∘ₗ Lm)`. Establish `hM : ∀ v, M *ᵥ v = fun r => Lm v (eq r)`. Introduce `v`. Simplify using `[M, LinearMap.toMatrix'_mulVec, LinearMap.funLeft]`. Both sides reduce to the same expression.

Use `⟨(e.factorial : ℝ) * (2 / Real.pi) ^ e * (1 / 2) ^ e * ‖M.det‖ ^ 2, by positivity, ?_, ?_⟩` and prove the remaining obligations. Introduce `hI`. Establish `hinjM : Function.Injective M.mulVec`. Introduce `v w h`. Apply `hinj hI` to reduce the goal to its premises.

Use function extensionality and compare the values at `t`. Establish `h1` using `congrFun h (eq.symm t)`. Simplify `h1` using `[hM]`. Establish `hu : IsUnit M` using `Matrix.mulVec_injective_iff_isUnit.1 hinjM`. Establish `hdet : M.det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det M).1 hu).ne_zero`.

Establish `hpos : 0 < ‖M.det‖` using `norm_pos_iff.2 hdet`. Establish `hpi : 0 < Real.pi` using `Real.pi_pos`. Check the signs of the components of the expression. Introduce `c`. Set `f : Ψ × Fin N → (Fin e → ℂ) → ℝ` to `fun p => (pot p).φ x ∘ (A.chart k).symm`.

Establish `hx' : (A.chart k).symm (A.chart k x) = x` using `(A.chart k).left_inv hx`. Establish `hloc : locDens A (fun _ => sumPot c pot) k (A.chart k x) = maDens (fun _ => fun y => ∑ p ∈ Finset.univ, c p * f p y) (A.chart k x)`. Unfold `locDens`. Rewrite using `[hx']`. Both sides reduce to the same expression.

Take `⟨hC, hL⟩` from `levi_sum Finset.univ c f (A.chart k x) (fun p => hcd p)`. Set `dd : Fin e → ℝ` to `fun r => 1 / 2 * ∑ m ∈ Finset.Ico (eq r).2.1.1 (eq r).2.1.2, c ((eq r).1, m)`. Establish `hprod : ∏ r, dd r = (1 / 2) ^ e * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)`. Rewrite using `[Fintype.prod_equiv eq dd (fun t => 1 / 2 * ∑ m ∈ Finset.Ico t.2.1.1 t.2.1.2, c (t.1, m)) (fun r => rfl)]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Fintype.prod_prod_type]`.

Use `congr 1`. Use `Finset.prod_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Conclude with `prod_pairs (fun i l => ∑ m ∈ Finset.Ico i l, c (τ, m))`. Rewrite using `[hloc, GlobalTheory.T.monge_ampere_density_diagonal_levi e _ (A.chart k x) dd M hC ?_]`. Rewrite using `[hprod]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `v`. Rewrite using `[hL v, hM v]`. Establish `h2 : ∀ p, levi (f p) (A.chart k x) v = ∑ q : Pairs N, if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then 1 / 2 * ‖Lm v (p.1, q)‖ ^ 2 else 0` using `fun p => hlevi p v`. Repeatedly rewrite using `[h2]`.

Rewrite using `[Fintype.sum_equiv eq (fun r => dd r * ‖Lm v (eq r)‖ ^ 2) (fun t => 1 / 2 * (∑ m ∈ Finset.Ico t.2.1.1 t.2.1.2, c (t.1, m)) * ‖Lm v t‖ ^ 2) (fun r => rfl)]`. Rewrite using `[Fintype.sum_prod_type, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl (fun q _ => ?_)` and prove the remaining obligations. Repeatedly rewrite using `[mul_ite, mul_zero]`. Rewrite using `[← Finset.sum_filter]`. Establish `hI : Finset.univ.filter (fun m : Fin N => q.1.1 ≤ m ∧ m < q.1.2) = Finset.Ico q.1.1 q.1.2`. Use extensionality with `m`.

Simplify using `[Finset.mem_Ico]`. Rewrite using `[hI, Finset.sum_mul]`. Use `Finset.sum_congr rfl (fun m _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PositivityTheory.Xgp.t_per_point : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ), j ≤ N → ∀ (pot : Ψ × Fin N → LocPot X) (x : X) (V : Set X) (g : Ψ → X → Matrix (Fin N) (Fin N) ℂ), IsPeriodChart A j pot x V g → e = antisymDegree Ψ N → ∀ k, x ∈ (A.chart k).source → ∃ ν : ℝ, 0 ≤ ν ∧ (IsFlagImmersionAt A g x → 0 < ν) ∧ ∀ c : Ψ × Fin N → ℝ, locDens A (fun _ => sumPot c pot) k (A.chart k x) = ν * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m) := by
  intro e X _ A Ψ _ _ N j hj pot x V g hP he k hx
  obtain ⟨Lm, hcd, hlevi, hinj⟩ :=
    per_diag.levi_diagonal_of_isPeriodChart e X A Ψ N j hj pot x V g hP k hx
  have hcard : Fintype.card (Ψ × Pairs N) = e := by
    rw [Fintype.card_prod, card_pairs, he, antisymDegree]
  let eq : Fin e ≃ Ψ × Pairs N := (Fintype.equivFinOfCardEq hcard).symm
  let M : Matrix (Fin e) (Fin e) ℂ :=
    LinearMap.toMatrix' ((LinearMap.funLeft ℂ ℂ (eq : Fin e → Ψ × Pairs N)) ∘ₗ Lm)
  have hM : ∀ v, M *ᵥ v = fun r => Lm v (eq r) := by
    intro v
    simp [M, LinearMap.toMatrix'_mulVec, LinearMap.funLeft]
    rfl
  refine ⟨(e.factorial : ℝ) * (2 / Real.pi) ^ e * (1 / 2) ^ e * ‖M.det‖ ^ 2, by positivity, ?_, ?_⟩
  · intro hI
    have hinjM : Function.Injective M.mulVec := by
      intro v w h
      apply hinj hI
      funext t
      have h1 := congrFun h (eq.symm t)
      simpa [hM] using h1
    have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.1 hinjM
    have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M).1 hu).ne_zero
    have hpos : 0 < ‖M.det‖ := norm_pos_iff.2 hdet
    have hpi : 0 < Real.pi := Real.pi_pos
    positivity
  · intro c
    let f : Ψ × Fin N → (Fin e → ℂ) → ℝ := fun p => (pot p).φ x ∘ (A.chart k).symm
    have hx' : (A.chart k).symm (A.chart k x) = x := (A.chart k).left_inv hx
    have hloc : locDens A (fun _ => sumPot c pot) k (A.chart k x)
        = maDens (fun _ => fun y => ∑ p ∈ Finset.univ, c p * f p y) (A.chart k x) := by
      unfold locDens
      rw [hx']
      rfl
    obtain ⟨hC, hL⟩ := levi_sum Finset.univ c f (A.chart k x) (fun p => hcd p)
    let dd : Fin e → ℝ := fun r => 1 / 2 * ∑ m ∈ Finset.Ico (eq r).2.1.1 (eq r).2.1.2, c ((eq r).1, m)
    have hprod : ∏ r, dd r = (1 / 2) ^ e *
        ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m) := by
      rw [Fintype.prod_equiv eq dd (fun t => 1 / 2 * ∑ m ∈ Finset.Ico t.2.1.1 t.2.1.2, c (t.1, m))
        (fun r => rfl)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Fintype.prod_prod_type]
      congr 1
      refine Finset.prod_congr rfl (fun τ _ => ?_)
      exact prod_pairs (fun i l => ∑ m ∈ Finset.Ico i l, c (τ, m))
    rw [hloc, GlobalTheory.T.monge_ampere_density_diagonal_levi e _ (A.chart k x) dd M hC ?_]
    · rw [hprod]
      ring
    · intro v
      rw [hL v, hM v]
      have h2 : ∀ p, levi (f p) (A.chart k x) v = ∑ q : Pairs N,
          if q.1.1 ≤ p.2 ∧ p.2 < q.1.2 then 1 / 2 * ‖Lm v (p.1, q)‖ ^ 2 else 0 := fun p => hlevi p v
      simp_rw [h2]
      rw [Fintype.sum_equiv eq (fun r => dd r * ‖Lm v (eq r)‖ ^ 2)
        (fun t => 1 / 2 * (∑ m ∈ Finset.Ico t.2.1.1 t.2.1.2, c (t.1, m)) * ‖Lm v t‖ ^ 2) (fun r => rfl)]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun τ _ => ?_)
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      simp_rw [mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      have hI : Finset.univ.filter (fun m : Fin N => q.1.1 ≤ m ∧ m < q.1.2) = Finset.Ico q.1.1 q.1.2 := by
        ext m
        simp [Finset.mem_Ico]
      rw [hI, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      ring
