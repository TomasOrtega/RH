import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TieArith

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar ReciprocityTheory.ChartRestriction.G.AI.I4

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Establish `h1` using `mConeMap_eq_scale y c hc g`. Rewrite `h1` using `[ConeTrdeg.mConeMap_of_isMultiHomog y hg, ConeTrdeg.mConeMap_of_isMultiHomog (ratioPt y c) hg]`. Establish `h2 : scaleT (fun k ↦ y ⟨k, c k⟩) (MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g) * ∏ k, MvPolynomial.X k ^ d k) = MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k) * ∏ k, MvPolynomial.X k ^ d k`. Simplify using `only [scaleT, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, mul_pow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[h2]`. Establish `h3 : (∏ k, MvPolynomial.X k ^ d k : MvPolynomial K Ω) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k)`. Conclude with `MvPolynomial.C_injective _ _ (mul_right_cancel₀ h3 h1)`.
-/
theorem aeval_eq_ratioPt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    MvPolynomial.aeval y g = MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have h1 := mConeMap_eq_scale y c hc g
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hg, ConeTrdeg.mConeMap_of_isMultiHomog (ratioPt y c) hg] at h1
  have h2 : scaleT (fun k ↦ y ⟨k, c k⟩)
      (MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g) * ∏ k, MvPolynomial.X k ^ d k) =
      MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k) *
        ∏ k, MvPolynomial.X k ^ d k := by
    simp only [scaleT, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, mul_pow, Finset.prod_mul_distrib]
    ring
  rw [h2] at h1
  have h3 : (∏ k, MvPolynomial.X k ^ d k : MvPolynomial K Ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ h3 h1)

/- English proof (translation)
Introduce `s`. Take `⟨d, g, h, hg, hh, n, e⟩` from `rep_of_mem y c hc (x := s) (by rw [htop]; trivial)`. Establish `hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)`. Use `⟨d, g, h, hg, hh, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[aeval_eq_ratioPt y c hc hh]`.

Conclude with `mul_ne_zero n hU`. Rewrite using `[aeval_eq_ratioPt y c hc hg, aeval_eq_ratioPt y c hc hh, e, _root_.mul_assoc]`.
-/
theorem birational_of_ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) : Birational y := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc (x := s) (by rw [htop]; trivial)
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · rw [aeval_eq_ratioPt y c hc hh]
    exact mul_ne_zero n hU
  · rw [aeval_eq_ratioPt y c hc hg, aeval_eq_ratioPt y c hc hh, e, _root_.mul_assoc]

/- English proof (translation)
Use `⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩` and prove the remaining obligations. Establish `hb : blockFnField y = ⊤` using `by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]`. Establish `htr : Algebra.trdeg ℤ (blockFnField y) = d`. Rewrite using `[hb, ← hd]`. Conclude with `(IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq`.

Rewrite using `[Cmp.ringKrullDim_coord y c hc, htr]`. Establish `h4 : (((d : Cardinal) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) = ((d + 1 + Fintype.card K : ℕ) : ℕ∞)`. Rewrite using `[map_add, Cardinal.toENat_nat, Cardinal.toENat_nat]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Both sides reduce to the same expression.
-/
theorem isArithVar_of_ratioField_eq_top [Nonempty K] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hd : Algebra.trdeg ℤ Ω = d) : IsArithVar (mCoordIdeal y) (d + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = d := by
    rw [hb, ← hd]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr]
  have h4 : (((d : Cardinal) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    rw [map_add, Cardinal.toENat_nat, Cardinal.toENat_nat]
    push_cast
    ring
  rw [h4]
  rfl

end Forms

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

def genCpt : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `h.bij.2 a`. Use `⟨s, ?_⟩` and prove the remaining obligations. Establish `e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _` using `TopCat.Presheaf.stalkSpecializes_refl _ _`. Use `show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ).hom s = a`. Rewrite using `[e]`.

Conclude with `hs`.
-/
theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom s = a
  rw [e]
  exact hs

variable {K : Type} [Fintype K] {J : K → Type} [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)

/- English proof (translation)
Establish `hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ (ratioField y c).toSubalgebra.restrictScalars ℤ`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Use `show _ ∈ ratioField y c`. Simplify using `only [← Finset.prod_div_distrib]`.

Conclude with `prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, j k⟩, rfl⟩`. Conclude with `hle ha`.
-/
theorem adjoin_le_ratioField {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) : a ∈ ratioField y c := by
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ (ratioField y c).toSubalgebra.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show _ ∈ ratioField y c
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, j k⟩, rfl⟩
  exact hle ha

end Chart

end GlobalTheory.CompanionTheory.Ar.TieArith

namespace GlobalTheory.CompanionTheory.Ar

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar TieArith in

/- English proof (translation)
Take `⟨c, hchart⟩` from `h.cover (genCpt ξ)`. Establish `hc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k ↦ (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)`. Establish `htop : ratioField y c = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `a _`.

Take `⟨s, hs, hu, hsa⟩` from `(GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ h c (genCpt ξ) hchart a).mp (mem_regAt_genCpt ξ h.gen a)`. Establish `h1` using `adjoin_le_ratioField y c hs`. Establish `h2` using `adjoin_le_ratioField y c hsa`. Establish `h3` using `div_mem h2 h1`. Rewrite `h3` using `[mul_div_cancel_left₀ _ hu.1]`. Then use the resulting hypothesis.

Conclude with `⟨birational_of_ratioField_eq_top y c hc htop, isArithVar_of_ratioField_eq_top y c hc htop d hd⟩`.
-/
theorem coordTie_birational_isArithVar (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ)
    (h : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hd : Algebra.trdeg ℤ Ω = d) : Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨c, hchart⟩ := h.cover (genCpt ξ)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦
    (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)
  have htop : ratioField y c = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ h c (genCpt ξ) hchart a).mp
      (mem_regAt_genCpt ξ h.gen a)
    have h1 := adjoin_le_ratioField y c hs
    have h2 := adjoin_le_ratioField y c hsa
    have h3 := div_mem h2 h1
    rwa [mul_div_cancel_left₀ _ hu.1] at h3
  exact ⟨birational_of_ratioField_eq_top y c hc htop,
    isArithVar_of_ratioField_eq_top y c hc htop d hd⟩

end GlobalTheory.CompanionTheory.Ar
