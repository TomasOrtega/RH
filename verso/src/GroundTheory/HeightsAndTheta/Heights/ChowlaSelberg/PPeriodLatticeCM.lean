import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.StatementsMean
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.PeriodLatticeIdeal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic Module
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

/- English proof (translation)
Introduce `s`. Use `S.isTotallyComplex` as an intermediate fact. Establish `hK : finrank ℚ K = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two ℚ K`. Take `⟨I, c, hc, h⟩` from `CMFamily.exists_periodLattice_eq S F s`. Set `P` to `idealPeriodPair (F.restrict s) hK I`.

Set `L' : PeriodPair` to `{ ω₁ := c * P.ω₁ ω₂ := c * P.ω₂ indep := by`. Use `P.indep` as an intermediate fact. Rewrite `this`, the goal using `[LinearIndependent.pair_iff]`. Introduce `a b hab`. Apply `this a b` to reduce the goal to its premises.

Establish `hab' : c * (a • P.ω₁ + b • P.ω₂) = 0`. Rewrite using `[← hab]`. Simplify using `only [Complex.real_smul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 hab').resolve_left hc }`.

Establish `hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice`. Use extensionality with `z`. Simplify using `only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`.

Conclude with `⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩`. Introduce and unpack `⟨w, ⟨m, n, rfl⟩, rfl⟩`. Conclude with `⟨m, n, by ring⟩`. Use `⟨L', ?_, ?_⟩` and prove the remaining obligations. Apply `SetLike.coe_injective` to reduce the goal to its premises.

Rewrite using `[hlat, h, lattice_idealPeriodPair]`. Rewrite using `[latticeEnd_eq_of_homothetic hc hlat]`. Conclude with `latticeEnd_idealPeriodPair (F.restrict s) hK I`.
-/
theorem PeriodLatticeCM.proof (S : PrimeDiscriminant K) (F : CMFamily K) :
    PeriodLatticeCM.Statement S F := by
  intro s
  have := S.isTotallyComplex
  have hK : finrank ℚ K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two ℚ K
  obtain ⟨I, c, hc, h⟩ := CMFamily.exists_periodLattice_eq S F s
  let P := idealPeriodPair (F.restrict s) hK I
  let L' : PeriodPair :=
    { ω₁ := c * P.ω₁
      ω₂ := c * P.ω₂
      indep := by
        have := P.indep
        rw [LinearIndependent.pair_iff] at this ⊢
        intro a b hab
        apply this a b
        have hab' : c * (a • P.ω₁ + b • P.ω₂) = 0 := by
          rw [← hab]; simp only [Complex.real_smul]; ring
        exact (mul_eq_zero.1 hab').resolve_left hc }
  have hlat : (L'.lattice : Set ℂ) = (c * ·) '' P.lattice := by
    ext z
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, Set.mem_image, L']
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m * P.ω₁ + n * P.ω₂, ⟨m, n, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨m, n, rfl⟩, rfl⟩
      exact ⟨m, n, by ring⟩
  refine ⟨L', ?_, ?_⟩
  · apply SetLike.coe_injective
    rw [hlat, h, lattice_idealPeriodPair]
  · rw [latticeEnd_eq_of_homothetic hc hlat]
    exact latticeEnd_idealPeriodPair (F.restrict s) hK I

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
