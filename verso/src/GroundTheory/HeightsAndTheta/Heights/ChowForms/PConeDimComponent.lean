import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Introduce `F _ n e I W u hI hdim hu hW`. Take `⟨hmin, hrel⟩` from `hW`. Establish `hWprime : W.IsPrime` using `hmin.1.1`. Establish `hJ : IsHomogIdeal (I ⊔ Ideal.span {linForm u})` using `isHomogIdeal_sup_span_linForm hI.isHomog u`. Establish `hproj : IsProjPrime W` using `by classical`.

Establish `hJh` using `(isHomogIdeal_iff _).mp hJ`. Use `⟨hWprime, (isHomogIdeal_iff W).mpr ?_, hrel⟩` and prove the remaining obligations. Use `set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal`. Establish `hcore_prime : core.IsPrime` using `hWprime.homogeneousCore`. Establish `hJcore : I ⊔ Ideal.span {linForm u} ≤ core`.

Rewrite using `[← hJh.toIdeal_homogeneousCore_eq_self]`. Conclude with `Ideal.homogeneousCore_mono _ hmin.1.2`. Establish `hle : core ≤ W` using `Ideal.toIdeal_homogeneousCore_le _ _`. Establish `heq : core = W` using `le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)`. Rewrite using `[Ideal.IsHomogeneous.iff_eq]`.

Conclude with `heq`. Use `⟨hproj, ?_⟩` and prove the remaining obligations. Establish `hIprime : I.IsPrime` using `hI.isPrime`. Establish `hIW : I ≤ W` using `le_sup_left.trans hmin.1.2`. Establish `huW : linForm u ∈ W` using `(le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)`.

Use `set B := MvPolynomial (Fin n) F ⧸ I`. Establish `_ : Algebra.FiniteType F B` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ_surjective F I)`. Use `set W' : Ideal B := W.map (Ideal.Quotient.mk I)`. Establish `hW'prime : W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])`. Establish `hW'ne : W' ≠ ⊥`.

Introduce `h`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Establish `: Ideal.Quotient.mk I (linForm u) ∈ W'` using `Ideal.mem_map_of_mem _ huW`. Rewrite `this` using `[h, Ideal.mem_bot]`.

Conclude with `this`. Establish `hht : W'.height ≤ 1` using `Ideal.map_height_le_one_of_mem_minimalPrimes hmin`. Establish `hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W)` using `ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)`. Establish `hform` using `GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'`. Establish `hdrop` using `GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne`.

Rewrite `hform`, `hdrop` using `[hquot]`. Express the relevant statement in the definitionally equal form `ringKrullDim B = _ at hdim`. Rewrite `hform`, `hdrop` using `[hdim]`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = y := by`. Consider the cases of `h : ringKrullDim (MvPolynomial (Fin n) F ⧸ W) with`.

Consider the case `bot`. Use `ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ W)` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `absurd this (by simp)`. Consider the case `coe y => exact ⟨y, rfl⟩`.

Rewrite `hform`, `hdrop`, the goal using `[hy]`. Establish `h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hdrop`. Establish `h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞)` using `by exact_mod_cast hform`. Establish `hyle : y ≤ e`. Establish `: y + 1 ≤ (e : ℕ∞) + 1` using `by exact_mod_cast h1`.

Conclude with `(ENat.add_le_add_iff_right ENat.one_ne_top).mp this`. Take `⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y` from `ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top e) hyle)`. Establish `h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m` using `by rw [← h2]; gcongr`. Establish `h4 : e + 1 ≤ 1 + m` using `by exact_mod_cast h3`. Establish `h5 : m ≤ e` using `by exact_mod_cast hyle`.

Establish `: m = e` using `by omega`. Substitute `this` using the available equality. Both sides reduce to the same expression.
-/
theorem ConeDimComponent.proof_closed : ConeDimComponent.Statement := by
  intro F _ n e I W u hI hdim hu hW
  obtain ⟨hmin, hrel⟩ := hW
  have hWprime : W.IsPrime := hmin.1.1

  have hJ : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := isHomogIdeal_sup_span_linForm hI.isHomog u
  have hproj : IsProjPrime W := by
    classical
    have hJh := (isHomogIdeal_iff _).mp hJ
    refine ⟨hWprime, (isHomogIdeal_iff W).mpr ?_, hrel⟩
    set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal
    have hcore_prime : core.IsPrime := hWprime.homogeneousCore
    have hJcore : I ⊔ Ideal.span {linForm u} ≤ core := by
      rw [← hJh.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hmin.1.2
    have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
    have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  refine ⟨hproj, ?_⟩

  have hIprime : I.IsPrime := hI.isPrime
  have hIW : I ≤ W := le_sup_left.trans hmin.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ I
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I)
      (Ideal.Quotient.mkₐ_surjective F I)
  set W' : Ideal B := W.map (Ideal.Quotient.mk I)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk I (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl

/- English proof (translation)
The claim follows from `ConeDimComponent.proof_closed`.
-/
theorem ConeDimComponent.proof (_h₁ : MinimalPrimeHomog.Statement) : ConeDimComponent.Statement :=
  ConeDimComponent.proof_closed

end

end GroundTheory.Heights₂.Heights
