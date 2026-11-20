import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.TsgPolyVolPolyCoeffEven
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.tsg_smul

/- English proof (translation)
Set `S : Ψ × Fin N → MvPolynomial (Ψ × Fin N) ℝ` to `fun p => ∑ k ∈ Finset.Ici p.2, X (p.1, k)`. Establish `key : ∀ p, aeval S (gapX p) = X p`. Introduce `p`. Take `⟨a, i⟩` from `p`. Establish `h1 : Finset.Ici i = insert i (Finset.Ioi i)` using `(Finset.Ioi_insert i).symm`.

Simplify using `only [gapX]`. Use `split_ifs with h`. Establish `h2 : Finset.Ioi i = Finset.Ici (⟨i.1 + 1, h⟩ : Fin N)`. Use extensionality with `k`. Simplify using `only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_mk]`.

Use linear arithmetic over natural numbers and integers. Establish `hn : i ∉ Finset.Ici (⟨i.1 + 1, h⟩ : Fin N)`. Simplify using `only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_mk]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [S, map_sub, aeval_X, h1, h2]`.

Rewrite using `[Finset.sum_insert hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Finset.Ioi i = ∅`. Use extensionality with `k`. Prove the components needed by the constructor for the conclusion.

Introduce `hk`. Rewrite `hk` using `[Finset.mem_Ioi, Fin.lt_iff_val_lt_val]`. Use `k.isLt` as an intermediate fact. It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers.

Introduce `hk`. Simplify using `at hk`. Simplify using `only [S, map_sub, map_zero, aeval_X, h1, h2, sub_zero]`. Simplify using the standard rewrite rules. Establish `hcomp : (aeval S).comp (toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] _) = AlgHom.id ℝ _`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `p`. Rewrite using `[AlgHom.comp_apply, AlgHom.id_apply]`. Use `show aeval S (aeval gapX (X p)) = X p`. Rewrite using `[aeval_X, key]`.

Establish `e : ∀ q, aeval S (toWt q) = q` using `fun q => by`. Simplify using `using AlgHom.congr_fun hcomp q`. Introduce `f g hfg`. Rewrite using `[← e f, ← e g, hfg]`.
-/
theorem toWt_inj (Ψ : Type) (N : ℕ) :
    Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  classical
  let S : Ψ × Fin N → MvPolynomial (Ψ × Fin N) ℝ := fun p => ∑ k ∈ Finset.Ici p.2, X (p.1, k)
  have key : ∀ p, aeval S (gapX p) = X p := by
    intro p
    obtain ⟨a, i⟩ := p
    have h1 : Finset.Ici i = insert i (Finset.Ioi i) := (Finset.Ioi_insert i).symm
    simp only [gapX]
    split_ifs with h
    · have h2 : Finset.Ioi i = Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        ext k
        simp only [Finset.mem_Ioi, Finset.mem_Ici, Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      have hn : i ∉ Finset.Ici (⟨i.1 + 1, h⟩ : Fin N) := by
        simp only [Finset.mem_Ici, Fin.le_iff_val_le_val, Fin.val_mk]
        omega
      simp only [S, map_sub, aeval_X, h1, h2]
      rw [Finset.sum_insert hn]
      ring
    · have h2 : Finset.Ioi i = ∅ := by
        ext k
        constructor
        · intro hk
          rw [Finset.mem_Ioi, Fin.lt_iff_val_lt_val] at hk
          have := k.isLt
          exfalso
          omega
        · intro hk
          simp at hk
      simp only [S, map_sub, map_zero, aeval_X, h1, h2, sub_zero]
      simp
  have hcomp : (aeval S).comp (toWt : MvPolynomial (Ψ × Fin N) ℝ →ₐ[ℝ] _) = AlgHom.id ℝ _ := by
    apply MvPolynomial.algHom_ext
    intro p
    rw [AlgHom.comp_apply, AlgHom.id_apply]
    show aeval S (aeval gapX (X p)) = X p
    rw [aeval_X, key]
  have e : ∀ q, aeval S (toWt q) = q := fun q => by
    simpa using AlgHom.congr_fun hcomp q
  intro f g hfg
  rw [← e f, ← e g, hfg]

end PositivityTheory.Xgp.tsg_smul

/- English proof (translation)
Use `⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩` and prove the remaining obligations. Introduce `D κ v Q`. Distinguish the cases in `hv : v = 0`. Substitute `hv` using the available equality. Simplify using `[tsgPoly]`.

Simplify using `only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `only [Polynomial.C_mul]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. Introduce `σ c e v Q`. Simplify using `[linePoly, Polynomial.algebraMap_eq]`.
-/
theorem PositivityTheory.Xgp.t_tsg_smul : (∀ (D : ℕ) (κ : ℕ → ℝ) (v : ℝ) (Q : Polynomial ℝ), tsgPoly D κ (Polynomial.C v * Q) = Polynomial.C v * tsgPoly D κ Q) ∧ (∀ (σ : Type) (c : σ → ℝ) (e : σ → ℤ) (v : ℝ) (Q : MvPolynomial σ ℝ), linePoly c e (C v * Q) = Polynomial.C v * linePoly c e Q) ∧ ∀ (Ψ : Type) (N : ℕ), Function.Injective (toWt : MvPolynomial (Ψ × Fin N) ℝ → MvPolynomial (Ψ × Fin N) ℝ) := by
  refine ⟨?_, ?_, fun Ψ N => PositivityTheory.Xgp.tsg_smul.toWt_inj Ψ N⟩
  · intro D κ v Q
    by_cases hv : v = 0
    · subst hv
      simp [tsgPoly]
    · simp only [tsgPoly, Polynomial.natDegree_C_mul hv, Polynomial.coeff_C_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs
      · simp only [Polynomial.C_mul]
        ring
      · simp
  · intro σ c e v Q
    simp [linePoly, Polynomial.algebraMap_eq]
