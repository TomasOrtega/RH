import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KappaSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreFubini
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SphereMeasureStereographicIntegralStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.XiPotentialHessianDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EvalW
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
open GlobalTheory.CompanionTheory.Ar.PB.FibN ReciprocityTheory.ChartRestriction.G.AI GroundTheory.Heights₂.Heights.Inter

namespace GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd

/- English proof (translation)
Establish `h : ⁅(pderiv a : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)), (pderiv b : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `i`. Establish `hc : ∀ c : σ, pderiv (R` using `ℝ) c (X i) = if i = c then 1 else 0 := fun c => by`. Rewrite using `[pderiv_X, Pi.single_apply]`.

Simplify using `only [Derivation.commutator_apply, hc, Derivation.coe_zero, Pi.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `congrArg (fun D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) => D P) h`. Simplify `h2` using `[Derivation.commutator_apply, sub_eq_zero]`.
-/
theorem pderiv_comm {σ : Type*} (a b : σ) (P : MvPolynomial σ ℝ) :
    pderiv a (pderiv b P) = pderiv b (pderiv a P) := by
  have h : ⁅(pderiv a : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ)),
      (pderiv b : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    classical
    have hc : ∀ c : σ, pderiv (R := ℝ) c (X i) = if i = c then 1 else 0 := fun c => by
      rw [pderiv_X, Pi.single_apply]
    simp only [Derivation.commutator_apply, hc, Derivation.coe_zero, Pi.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℝ (MvPolynomial σ ℝ) (MvPolynomial σ ℝ) => D P) h
  simpa [Derivation.commutator_apply, sub_eq_zero] using h2

/- English proof (translation)
Establish `h0 : pderiv (some j) ((X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) = 0`. Simplify using `[Derivation.leibniz_pow, pderiv_X, Pi.single_apply]`. Rewrite using `[Derivation.leibniz, h0, pderiv_rename (Option.some_injective _)]`. Simplify using `[mul_comm]`.
-/
theorem pderiv_some_rename_mul (j : Fin 2) (P : MvPolynomial (Fin 2) ℝ) (m : ℕ) :
    pderiv (some j) (rename some P * (X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) =
      rename some (pderiv j P) * X none ^ m := by
  have h0 : pderiv (some j) ((X none : MvPolynomial (Option (Fin 2)) ℝ) ^ m) = 0 := by
    simp [Derivation.leibniz_pow, pderiv_X, Pi.single_apply]
  rw [Derivation.leibniz, h0, pderiv_rename (Option.some_injective _)]
  simp [mul_comm]

/- English proof (translation)
Establish `h : ((evalW n₀ n₁).comp (rename some) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] _) = (rename some).comp (aeval ![lin3 n₀, lin3 n₁])`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`. Apply the tactic sequence `fin_cases j <;> simp [evalW, lin4]`. Conclude with `DFunLike.congr_fun h P`.
-/
theorem evalW_rename (n₀ n₁ : Fin 3 → ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    evalW n₀ n₁ (rename some P) = rename some (aeval ![lin3 n₀, lin3 n₁] P) := by
  have h : ((evalW n₀ n₁).comp (rename some) : MvPolynomial (Fin 2) ℝ →ₐ[ℝ] _) =
      (rename some).comp (aeval ![lin3 n₀, lin3 n₁]) := by
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j <;> simp [evalW, lin4]
  exact DFunLike.congr_fun h P

/- English proof (translation)
Rewrite using `[Fin.prod_univ_eq_prod_range (fun r : ℕ => rowW (if r < 2 * k then DiagonalFibreFubini.wordCoef i r else 0) (if r < 2 * k then 0 else 1)) (d + 2)]`. Take `⟨m, hm⟩ : ∃ m, d + 2 = 2 * k + m` from `⟨d + 2 - 2 * k, by omega⟩`. Rewrite using `[hm, Finset.prod_range_add, show 2 * k + m - 2 * k = m by omega]`. Use `congr 1`. Rewrite using `[wwLinProd, map_prod]`.

Use `Finset.prod_congr rfl fun n hn => ?_` and prove the remaining obligations. Establish `hn' : n < 2 * k` using `Finset.mem_range.mp hn`. Simplify using `[rowW, hn']`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => (X none : MvPolynomial (Option (Fin 2)) ℝ))]`. Simplify using the standard rewrite rules.

Introduce `x _`. Simplify using `[rowW]`.
-/
theorem prod_rows_word (d k i : ℕ) (hk : 2 * k ≤ d + 2) :
    (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)) =
    rename some (wwLinProd k (DiagonalFibreFubini.wordCoef i)) * X none ^ (d + 2 - 2 * k) := by
  rw [Fin.prod_univ_eq_prod_range (fun r : ℕ =>
    rowW (if r < 2 * k then DiagonalFibreFubini.wordCoef i r else 0) (if r < 2 * k then 0 else 1)) (d + 2)]
  obtain ⟨m, hm⟩ : ∃ m, d + 2 = 2 * k + m := ⟨d + 2 - 2 * k, by omega⟩
  rw [hm, Finset.prod_range_add, show 2 * k + m - 2 * k = m by omega]
  congr 1
  · rw [wwLinProd, map_prod]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hn' : n < 2 * k := Finset.mem_range.mp hn
    simp [rowW, hn']
  · rw [Finset.prod_congr rfl (g := fun _ => (X none : MvPolynomial (Option (Fin 2)) ℝ))]
    · simp
    · intro x _
      simp [rowW]

/- English proof (translation)
Introduce `d k i _ hk n₀ n₁`. Rewrite using `[prod_rows_word d k i hk, pderiv_some_rename_mul, pderiv_some_rename_mul, map_mul, evalW_rename, pderiv_comm 1 0, map_pow]`. Use `congr 1`. Simplify using `[evalW]`.
-/
theorem evalW_pderiv_prod_rows_word : ∀ (d k i : ℕ), i < k → 2 * k ≤ d + 2 → ∀ n₀ n₁ : Fin 3 → ℝ,
    evalW n₀ n₁ (pderiv (some 1) (pderiv (some 0) (∏ r : Fin (d + 2),
      rowW (if (r : ℕ) < 2 * k then DiagonalFibreFubini.wordCoef i r else 0)
        (if (r : ℕ) < 2 * k then 0 else 1)))) =
    rename some (aeval ![lin3 n₀, lin3 n₁]
      (pderiv 0 (pderiv 1 (wwLinProd k (DiagonalFibreFubini.wordCoef i))))) * X none ^ (d + 2 - 2 * k) := by
  intro d k i _ hk n₀ n₁
  rw [prod_rows_word d k i hk, pderiv_some_rename_mul, pderiv_some_rename_mul, map_mul, evalW_rename,
    pderiv_comm 1 0, map_pow]
  congr 1
  simp [evalW]

end GlobalTheory.CompanionTheory.Ar.PB.FibN.WordProd
