import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.CompHt

/- English proof (translation)
Establish `e1` using `finrank_quotPiece_add (coneIdeal K y) n`. Establish `e2` using `GradedHilbert.finrank_map_add_finrank_inf_ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)`. Establish `e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _) = homogeneousSubmodule (Fin N) K n ⊓ LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap`. Use extensionality with `g`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule, LinearMap.mem_ker, AlgHom.toLinearMap_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩`.

Rewrite `e1` using `[e3]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_quotPiece_coneIdeal_eq_finrank_map {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) (n : ℕ) :
    Module.finrank K (quotPiece (coneIdeal K y) n) =
      Module.finrank K ((homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap) := by
  have e1 := finrank_quotPiece_add (coneIdeal K y) n
  have e2 := GradedHilbert.finrank_map_add_finrank_inf_ker
    (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap (homogeneousSubmodule (Fin N) K n)
  have e3 : ((coneIdeal K y).restrictScalars K ⊓ homogeneousSubmodule (Fin N) K n : Submodule K _)
      = homogeneousSubmodule (Fin N) K n ⊓
        LinearMap.ker (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
    ext g
    simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_homogeneousSubmodule,
      LinearMap.mem_ker, AlgHom.toLinearMap_apply]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (mem_coneIdeal_of_isHomogeneous y h2).1 h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(mem_coneIdeal_of_isHomogeneous y h1).2 h2, h1⟩
  rw [e3] at e1
  omega

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent g, map_sum]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n`. Use `Finset.mem_range.1 hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Use `⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩` and prove the remaining obligations. Use `(homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))` as an intermediate fact. Rewrite `this` using `[one_mul, Nat.add_sub_cancel' hi']`. Conclude with `this`.
-/
theorem aeval_mem_map_homogeneousSubmodule {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    {N : ℕ} (y : Fin N → Ω) {j : Fin N} (hj : y j = 1) (g : MvPolynomial (Fin N) K) {n : ℕ}
    (hn : g.totalDegree ≤ n) :
    aeval y g ∈ (homogeneousSubmodule (Fin N) K n).map
        (aeval y : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← sum_homogeneousComponent g, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  have hi' : i ≤ n := by
    have := Finset.mem_range.1 hi
    omega
  refine ⟨homogeneousComponent i g * X j ^ (n - i), ?_, by simp [hj]⟩
  have := (homogeneousComponent_isHomogeneous i g).mul ((isHomogeneous_X K j).pow (n - i))
  rw [one_mul, Nat.add_sub_cancel' hi'] at this
  exact this

/- English proof (translation)
Establish `halg : ∀ x ∈ Set.range y, IsAlgebraic K x` using `fun x _ => Algebra.IsAlgebraic.isAlgebraic x`. Use `haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) := IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral`. Use `set S : Submodule K (AlgebraicClosure K) := Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS`. Establish `hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x`. Introduce `x`.

Rewrite using `[hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule, Algebra.adjoin_range_eq_range_aeval]`. Both sides reduce to the same expression. Establish `hfin : Module.Finite K S` using `‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›`. Take `⟨s, hs⟩` from `Module.Finite.iff_fg.1 hfin`. Establish `hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap`.

Rewrite using `[eventually_all_finset]`. Introduce `x hx`. Take `⟨g, rfl⟩` from `(hmem x).1 (hs ▸ Submodule.subset_span hx)`. Use `filter_upwards [eventually_ge_atTop g.totalDegree] with n hn`. Conclude with `aeval_mem_map_homogeneousSubmodule y hj g hn`.

Apply `polynomial_eq_of_eventually_eval_nat` to reduce the goal to its premises. Use `filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev] with n h1 h2`. Establish `hW : (homogeneousSubmodule (Fin N) K n).map (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, -, rfl⟩`.

Conclude with `(hmem _).2 ⟨g, rfl⟩`. Rewrite using `[← hs, Submodule.span_le]`. Conclude with `fun x hx => h2 x hx`. Rewrite using `[← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]`. Both sides reduce to the same expression.
-/
theorem idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin (K : Type) [Field K] (N : ℕ)
    (y : Fin N → AlgebraicClosure K) (j : Fin N) (hj : y j = 1) :
    GlobalTheory.idealHilbertPoly (coneIdeal K y) =
      Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  have halg : ∀ x ∈ Set.range y, IsAlgebraic K x := fun x _ => Algebra.IsAlgebraic.isAlgebraic x
  haveI : FiniteDimensional K (IntermediateField.adjoin K (Set.range y)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (halg x hx).isIntegral
  set S : Submodule K (AlgebraicClosure K) :=
    Subalgebra.toSubmodule (IntermediateField.adjoin K (Set.range y)).toSubalgebra with hS
  have hmem : ∀ x, x ∈ S ↔ ∃ g : MvPolynomial (Fin N) K, aeval y g = x := by
    intro x
    rw [hS, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Subalgebra.mem_toSubmodule,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  have hfin : Module.Finite K S := ‹FiniteDimensional K (IntermediateField.adjoin K (Set.range y))›
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hev : ∀ᶠ n : ℕ in atTop, ∀ x ∈ s, x ∈ (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap := by
    rw [eventually_all_finset]
    intro x hx
    obtain ⟨g, rfl⟩ := (hmem x).1 (hs ▸ Submodule.subset_span hx)
    filter_upwards [eventually_ge_atTop g.totalDegree] with n hn
    exact aeval_mem_map_homogeneousSubmodule y hj g hn
  apply polynomial_eq_of_eventually_eval_nat
  filter_upwards [eventually_finrank_quotPiece (isHomogeneous_coneIdeal (K := K) y), hev]
    with n h1 h2
  have hW : (homogeneousSubmodule (Fin N) K n).map
      (aeval y : MvPolynomial (Fin N) K →ₐ[K] AlgebraicClosure K).toLinearMap = S := by
    apply le_antisymm
    · rintro _ ⟨g, -, rfl⟩
      exact (hmem _).2 ⟨g, rfl⟩
    · rw [← hs, Submodule.span_le]
      exact fun x hx => h2 x hx
  rw [← h1, finrank_quotPiece_coneIdeal_eq_finrank_map, hW, Polynomial.eval_C]
  rfl

end GlobalTheory.CompHt
