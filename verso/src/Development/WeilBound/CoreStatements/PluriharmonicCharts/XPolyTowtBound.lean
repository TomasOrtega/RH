import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights

namespace PositivityTheory.Xgp.poly_towt_bound

/- English proof (translation)
The claim follows from `|coeff m P| ≤ ∑ d ∈ P.support, |coeff d P| := by by_cases h : m ∈ P.support · exact Finset.single_le_sum (f := fun d => |coeff d P|) (fun _ _ => abs_nonneg _) h · rw [notMem_support_iff.mp h, abs_zero] exact Finset.sum_nonneg fun _ _ => abs_nonneg _`.
-/
theorem abs_coeff_le {σ : Type} (P : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    |coeff m P| ≤ ∑ d ∈ P.support, |coeff d P| := by
  by_cases h : m ∈ P.support
  · exact Finset.single_le_sum (f := fun d => |coeff d P|) (fun _ _ => abs_nonneg _) h
  · rw [notMem_support_iff.mp h, abs_zero]
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _

/- English proof (translation)
Set `S : Finset (σ →₀ ℕ)` to `(Finsupp.finite_of_degree_le (σ := σ) n).toFinset`. Set `B : (σ →₀ ℕ) → ℝ` to `fun d => ∑ e ∈ (aeval f (monomial d (1 : ℝ))).support, |coeff e (aeval f (monomial d (1 : ℝ)))|`. Establish `hB : ∀ d, 0 ≤ B d` using `fun d => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `⟨∑ d ∈ S, B d, Finset.sum_nonneg fun d _ => hB d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩` and prove the remaining obligations. Simplify using `using hQ.aeval f hf`.

Establish `hM0 : 0 ≤ M` using `(abs_nonneg _).trans (hM 0)`. Establish `hsub : Q.support ⊆ S`. Introduce `d hd`. Simplify using `only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Assume the negation of the conclusion as `hne`.

Conclude with `(mem_support_iff.mp hd) (hQ.coeff_eq_zero (by omega))`. Establish `e : coeff m (aeval f Q) = ∑ d ∈ Q.support, coeff d Q * coeff m (aeval f (monomial d (1 : ℝ)))` using `by conv_lhs => rw [Q.as_sum]`. Rewrite using `[map_sum, coeff_sum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[← coeff_C_mul]`.

Use `congr 1`. Establish `: monomial d (coeff d Q) = C (coeff d Q) * monomial d (1 : ℝ)`. Rewrite using `[C_mul_monomial, mul_one]`. Rewrite using `[this, map_mul, aeval_C]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun d _ => ?_` and prove the remaining obligations. Rewrite using `[abs_mul, mul_comm]`. Conclude with `mul_le_mul (abs_coeff_le _ m) (hM d) (abs_nonneg _) (hB d)`.

Use `_ ≤ ∑ d ∈ S, B d * M := Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0`. Use `_ = _ := by rw [Finset.sum_mul]`.
-/
theorem gen {σ : Type} [Fintype σ] (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsHomogeneous 1) (n : ℕ) :
    ∃ Cst : ℝ, 0 ≤ Cst ∧ ∀ (Q : MvPolynomial σ ℝ) (M : ℝ), Q.IsHomogeneous n →
      (aeval f Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (aeval f Q)| ≤ Cst * M) := by
  classical
  let S : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) n).toFinset
  let B : (σ →₀ ℕ) → ℝ := fun d =>
    ∑ e ∈ (aeval f (monomial d (1 : ℝ))).support, |coeff e (aeval f (monomial d (1 : ℝ)))|
  have hB : ∀ d, 0 ≤ B d := fun d => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨∑ d ∈ S, B d, Finset.sum_nonneg fun d _ => hB d, fun Q M hQ => ⟨?_, fun hM m => ?_⟩⟩
  · simpa using hQ.aeval f hf
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hsub : Q.support ⊆ S := by
      intro d hd
      simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      by_contra hne
      exact (mem_support_iff.mp hd) (hQ.coeff_eq_zero (by omega))
    have e : coeff m (aeval f Q) = ∑ d ∈ Q.support, coeff d Q * coeff m (aeval f (monomial d (1 : ℝ))) := by
      conv_lhs => rw [Q.as_sum]
      rw [map_sum, coeff_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [← coeff_C_mul]
      congr 1
      have : monomial d (coeff d Q) = C (coeff d Q) * monomial d (1 : ℝ) := by
        rw [C_mul_monomial, mul_one]
      rw [this, map_mul, aeval_C]
      rfl
    rw [e]
    calc _ ≤ ∑ d ∈ Q.support, |coeff d Q * coeff m (aeval f (monomial d (1 : ℝ)))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Q.support, B d * M := by
          refine Finset.sum_le_sum fun d _ => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul (abs_coeff_le _ m) (hM d) (abs_nonneg _) (hB d)
      _ ≤ ∑ d ∈ S, B d * M :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun d _ _ => mul_nonneg (hB d) hM0
      _ = _ := by rw [Finset.sum_mul]

/- English proof (translation)
Unfold `gapX`. Use `(isHomogeneous_X ℝ p).sub ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `isHomogeneous_X ℝ _`. Conclude with `isHomogeneous_zero _ _ _`.
-/
theorem gapX_hom {Ψ : Type} {N : ℕ} (p : Ψ × Fin N) : (gapX p).IsHomogeneous 1 := by
  unfold gapX
  refine (isHomogeneous_X ℝ p).sub ?_
  split_ifs
  · exact isHomogeneous_X ℝ _
  · exact isHomogeneous_zero _ _ _

end PositivityTheory.Xgp.poly_towt_bound

/- English proof (translation)
Introduce `Ψ _ N n`. Take `⟨C1, h1, H1⟩` from `PositivityTheory.Xgp.poly_towt_bound.gen (gapX (Ψ := Ψ) (N := N)) PositivityTheory.Xgp.poly_towt_bound.gapX_hom n`. Take `⟨C2, h2, H2⟩` from `PositivityTheory.Xgp.poly_towt_bound.gen (fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)) (by`. Introduce and unpack `(_ | p)`. Conclude with `isHomogeneous_X ℝ _`.

Conclude with `(PositivityTheory.Xgp.poly_towt_bound.gapX_hom p).rename_isHomogeneous) n`. Use `⟨C1 + C2, fun Q M hQ => ⟨(H1 Q M hQ).1, fun hM m => ?_⟩, fun Q M hQ => ⟨(H2 Q M hQ).1, fun hM m => ?_⟩⟩` and prove the remaining obligations. Establish `hM0 : 0 ≤ M` using `(abs_nonneg _).trans (hM 0)`. Use `(H1 Q M hQ).2 hM m` as an intermediate fact. Establish `h3` using `mul_nonneg h2 hM0`.

Unfold `toWt`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hM0 : 0 ≤ M` using `(abs_nonneg _).trans (hM 0)`. Use `(H2 Q M hQ).2 hM m` as an intermediate fact. Establish `h3` using `mul_nonneg h1 hM0`.

Unfold `toWtS`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PositivityTheory.Xgp.t_poly_towt_bound : ∀ (Ψ : Type) [Fintype Ψ] (N n : ℕ), ∃ Cst : ℝ, (∀ (Q : MvPolynomial (Ψ × Fin N) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWt Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWt Q)| ≤ Cst * M)) ∧ ∀ (Q : MvPolynomial (Option (Ψ × Fin N)) ℝ) (M : ℝ), Q.IsHomogeneous n → (toWtS Q).IsHomogeneous n ∧ ((∀ m, |coeff m Q| ≤ M) → ∀ m, |coeff m (toWtS Q)| ≤ Cst * M) := by
  intro Ψ _ N n
  obtain ⟨C1, h1, H1⟩ := PositivityTheory.Xgp.poly_towt_bound.gen (gapX (Ψ := Ψ) (N := N))
    PositivityTheory.Xgp.poly_towt_bound.gapX_hom n
  obtain ⟨C2, h2, H2⟩ := PositivityTheory.Xgp.poly_towt_bound.gen
    (fun o : Option (Ψ × Fin N) => o.elim (X none) fun p => rename some (gapX p)) (by
      rintro (_ | p)
      · exact isHomogeneous_X ℝ _
      · exact (PositivityTheory.Xgp.poly_towt_bound.gapX_hom p).rename_isHomogeneous) n
  refine ⟨C1 + C2, fun Q M hQ => ⟨(H1 Q M hQ).1, fun hM m => ?_⟩,
    fun Q M hQ => ⟨(H2 Q M hQ).1, fun hM m => ?_⟩⟩
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H1 Q M hQ).2 hM m
    have h3 := mul_nonneg h2 hM0
    unfold toWt
    linarith
  · have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have := (H2 Q M hQ).2 hM m
    have h3 := mul_nonneg h1 hM0
    unfold toWtS
    linarith
