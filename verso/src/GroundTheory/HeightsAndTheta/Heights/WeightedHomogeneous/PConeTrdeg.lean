import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.StatementsConeTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `conv_lhs => rw [g.as_sum]`. Use `conv_rhs => rw [g.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm ↦ ?_` and prove the remaining obligations. Simplify using `only [Geo.mConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]`. Rewrite using `[mul_assoc]`. Use `congr 2`. Rewrite using `[Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← hg m hm k, ← Finset.prod_pow_eq_pow_sum]`.
-/
theorem ConeTrdeg.mConeMap_of_isMultiHomog (y : (Σ k, ι k) → Ω) {g : Geo.MRing ι} {d : K → ℕ}
    (hg : Geo.IsMultiHomog g d) :
    Geo.mConeMap y g = MvPolynomial.C (aeval y g) * ∏ k, X k ^ d k := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  simp only [Geo.mConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, map_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
  rw [mul_assoc]
  congr 2
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← hg m hm k, ← Finset.prod_pow_eq_pow_sum]

/- English proof (translation)
Introduce `K _ ι _ Ω _ y hbir hnz hhor`. Establish `hinjΩ : Function.Injective (algebraMap ℤ Ω)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `n hn`. Establish `hmem : (MvPolynomial.C n : Geo.MRing ι) ∈ Geo.mCoordIdeal y`.

Rewrite using `[Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply, hn, map_zero]`. Establish `h2 : n ∈ (Geo.mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* Geo.MRing ι)` using `hmem`. Simplify using `only [Geo.IsHorizontal] at hhor`. Rewrite `h2` using `[hhor]`. Conclude with `(Ideal.mem_bot).1 h2`.

Establish `: FaithfulSMul ℤ Ω` using `(faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr hinjΩ`. Establish `: FaithfulSMul Ω (MvPolynomial K Ω)` using `(faithfulSMul_iff_algebraMap_injective Ω (MvPolynomial K Ω)).mpr (MvPolynomial.C_injective K Ω)`. Establish `hB : Algebra.trdeg ℤ (MvPolynomial K Ω) = Algebra.trdeg ℤ Ω + Fintype.card K`. Rewrite using `[← trdeg_add_eq ℤ Ω (A := MvPolynomial K Ω), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype]`. Establish `hZB : Function.Injective (algebraMap ℤ (MvPolynomial K Ω))`.

Rewrite using `[IsScalarTower.algebraMap_eq ℤ Ω (MvPolynomial K Ω), RingHom.coe_comp]`. Conclude with `(MvPolynomial.C_injective K Ω).comp hinjΩ`. Set `S` to `(Geo.mConeMap y).range`. Establish `hA : Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ S` using `(Ideal.quotientKerEquivRange (Geo.mConeMap y)).trdeg_eq`. Establish `: FaithfulSMul ℤ S` using `(faithfulSMul_iff_algebraMap_injective ℤ S).mpr (Function.Injective.of_comp (f := algebraMap S (MvPolynomial K Ω)) (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]))`.

Establish `: FaithfulSMul S (MvPolynomial K Ω)` using `(faithfulSMul_iff_algebraMap_injective S (MvPolynomial K Ω)).mpr Subtype.val_injective`. Establish `halgC : ∀ a : Ω, IsAlgebraic S (MvPolynomial.C a : MvPolynomial K Ω)`. Introduce `a`. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hbir a`. Establish `hgS : Geo.mConeMap y g ∈ S` using `AlgHom.mem_range_self _ _`.

Establish `hhS : Geo.mConeMap y h ∈ S` using `AlgHom.mem_range_self _ _`. Establish `hne : Geo.mConeMap y h ≠ 0`. Rewrite using `[ConeTrdeg.mConeMap_of_isMultiHomog y hh]`. Conclude with `mul_ne_zero (MvPolynomial.C_ne_zero.2 hh0) (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))`. Use `IsAlgebraic.of_mul (y := Geo.mConeMap y h) (mem_nonZeroDivisors_of_ne_zero hne) (isAlgebraic_algebraMap (⟨_, hhS⟩ : S)) ?_` and prove the remaining obligations.

Establish `hmul : Geo.mConeMap y h * MvPolynomial.C a = Geo.mConeMap y g`. Rewrite using `[ConeTrdeg.mConeMap_of_isMultiHomog y hh, ConeTrdeg.mConeMap_of_isMultiHomog y hg, hgh, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hmul]`. Conclude with `isAlgebraic_algebraMap (⟨_, hgS⟩ : S)`.

Use `choose c hc using hnz`. Establish `halgX : ∀ k, IsAlgebraic S (X k : MvPolynomial K Ω)`. Introduce `k`. Establish `hS : Geo.mConeMap y (X ⟨k, c k⟩) ∈ S` using `AlgHom.mem_range_self _ _`. Use `IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨k, c k⟩)) (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.C_ne_zero.2 (hc k))) (halgC _) ?_` and prove the remaining obligations.

Establish `hmul : (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) = Geo.mConeMap y (X ⟨k, c k⟩)`. Simplify using `[Geo.mConeMap]`. Rewrite using `[hmul]`. Conclude with `isAlgebraic_algebraMap (⟨_, hS⟩ : S)`. Establish `: Algebra.IsAlgebraic S (MvPolynomial K Ω)` using `⟨fun p ↦ by`.

Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => exact halgC a`. Consider the case `add p q hp hq => exact hp.add hq`. Consider the case `mul_X p k hp => exact hp.mul (halgX k)⟩`. Establish `hSB` using `trdeg_add_eq ℤ S (A := MvPolynomial K Ω)`.

Rewrite `hSB` using `[trdeg_eq_zero (R := S) (A := MvPolynomial K Ω), add_zero]`. Rewrite using `[hA, hSB, hB]`.
-/
theorem ConeTrdeg.proof : ConeTrdeg.Statement := by
  intro K _ ι _ Ω _ y hbir hnz hhor
  classical

  have hinjΩ : Function.Injective (algebraMap ℤ Ω) := by
    rw [injective_iff_map_eq_zero]
    intro n hn
    have hmem : (MvPolynomial.C n : Geo.MRing ι) ∈ Geo.mCoordIdeal y := by
      rw [Geo.mCoordIdeal, RingHom.mem_ker, Geo.mConeMap, MvPolynomial.aeval_C,
        MvPolynomial.algebraMap_apply, hn, map_zero]
    have h2 : n ∈ (Geo.mCoordIdeal y).comap (MvPolynomial.C : ℤ →+* Geo.MRing ι) := hmem
    simp only [Geo.IsHorizontal] at hhor
    rw [hhor] at h2
    exact (Ideal.mem_bot).1 h2
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr hinjΩ
  have : FaithfulSMul Ω (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective Ω (MvPolynomial K Ω)).mpr (MvPolynomial.C_injective K Ω)
  have hB : Algebra.trdeg ℤ (MvPolynomial K Ω) = Algebra.trdeg ℤ Ω + Fintype.card K := by
    rw [← trdeg_add_eq ℤ Ω (A := MvPolynomial K Ω), MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id,
      Cardinal.mk_fintype]
  have hZB : Function.Injective (algebraMap ℤ (MvPolynomial K Ω)) := by
    rw [IsScalarTower.algebraMap_eq ℤ Ω (MvPolynomial K Ω), RingHom.coe_comp]
    exact (MvPolynomial.C_injective K Ω).comp hinjΩ
  let S := (Geo.mConeMap y).range
  have hA : Algebra.trdeg ℤ (Geo.MRing ι ⧸ Geo.mCoordIdeal y) = Algebra.trdeg ℤ S :=
    (Ideal.quotientKerEquivRange (Geo.mConeMap y)).trdeg_eq
  have : FaithfulSMul ℤ S := (faithfulSMul_iff_algebraMap_injective ℤ S).mpr
    (Function.Injective.of_comp (f := algebraMap S (MvPolynomial K Ω))
      (by rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]))
  have : FaithfulSMul S (MvPolynomial K Ω) :=
    (faithfulSMul_iff_algebraMap_injective S (MvPolynomial K Ω)).mpr Subtype.val_injective

  have halgC : ∀ a : Ω, IsAlgebraic S (MvPolynomial.C a : MvPolynomial K Ω) := by
    intro a
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir a
    have hgS : Geo.mConeMap y g ∈ S := AlgHom.mem_range_self _ _
    have hhS : Geo.mConeMap y h ∈ S := AlgHom.mem_range_self _ _
    have hne : Geo.mConeMap y h ≠ 0 := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh]
      exact mul_ne_zero (MvPolynomial.C_ne_zero.2 hh0)
        (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
    refine IsAlgebraic.of_mul (y := Geo.mConeMap y h) (mem_nonZeroDivisors_of_ne_zero hne)
      (isAlgebraic_algebraMap (⟨_, hhS⟩ : S)) ?_
    have hmul : Geo.mConeMap y h * MvPolynomial.C a = Geo.mConeMap y g := by
      rw [ConeTrdeg.mConeMap_of_isMultiHomog y hh, ConeTrdeg.mConeMap_of_isMultiHomog y hg, hgh, map_mul]
      ring
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hgS⟩ : S)

  choose c hc using hnz
  have halgX : ∀ k, IsAlgebraic S (X k : MvPolynomial K Ω) := by
    intro k
    have hS : Geo.mConeMap y (X ⟨k, c k⟩) ∈ S := AlgHom.mem_range_self _ _
    refine IsAlgebraic.of_mul (y := MvPolynomial.C (y ⟨k, c k⟩))
      (mem_nonZeroDivisors_of_ne_zero (MvPolynomial.C_ne_zero.2 (hc k))) (halgC _) ?_
    have hmul : (MvPolynomial.C (y ⟨k, c k⟩) * X k : MvPolynomial K Ω) = Geo.mConeMap y (X ⟨k, c k⟩) := by
      simp [Geo.mConeMap]
    rw [hmul]
    exact isAlgebraic_algebraMap (⟨_, hS⟩ : S)
  have : Algebra.IsAlgebraic S (MvPolynomial K Ω) := ⟨fun p ↦ by
    induction p using MvPolynomial.induction_on with
    | C a => exact halgC a
    | add p q hp hq => exact hp.add hq
    | mul_X p k hp => exact hp.mul (halgX k)⟩
  have hSB := trdeg_add_eq ℤ S (A := MvPolynomial K Ω)
  rw [trdeg_eq_zero (R := S) (A := MvPolynomial K Ω), add_zero] at hSB
  rw [hA, hSB, hB]

end

end GroundTheory.Heights₂.Heights
