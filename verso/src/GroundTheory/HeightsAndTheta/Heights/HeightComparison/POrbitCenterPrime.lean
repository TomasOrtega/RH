import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterPrime
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
Introduce `ι _ _ n x hx v`. Set `_ : LinearOrder ι` to `LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective`. Set `w : Coord n → Lex (ι → ℕ)` to `fun c ↦ toLex (coordDeg n c)`. Set `_ : DecidableEq (Lex (ι → ℕ))` to `LinearOrder.toDecidableEq`. Establish `_ : GradedRing (weightedHomogeneousSubmodule ℤ w)` using `MvPolynomial.weightedGradedAlgebra ℤ w`.

Establish `hw : ∀ (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ), IsWeightedHomogeneous w F (toLex d) ↔ IsWeightedHomogeneous (coordDeg n) F d` using `fun _ _ ↦ Iff.rfl`. Use `set M : (ι → ℕ) → ℝ := fun d ↦ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k with hM`. Establish `hM0 : ∀ d, 0 ≤ M d` using `fun d ↦ Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _`. Establish `hMadd : ∀ d e, M (d + e) = M d * M e` using `fun d e ↦ by`. Simplify using `only [hM, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Establish `hform : ∀ F, SetLike.IsHomogeneousElem (weightedHomogeneousSubmodule ℤ w) F → ∃ d, Geo.IsMultiHomog (ι` using `blockIdx n) F d := by`. Introduce and unpack `F ⟨i, hi⟩`. Conclude with `⟨ofLex i, (geoMultiHomog_iff _ _).mpr ((hw F (ofLex i)).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hi))⟩`. Use `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem (𝒜 := weightedHomogeneousSubmodule ℤ w) ?_ ?_ ?_` and prove the remaining obligations. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations.

Introduce and unpack `F ⟨d, hd, -⟩`. Conclude with `⟨toLex d, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((hw F d).mpr ((geoMultiHomog_iff _ _).mp hd))⟩`. Rewrite using `[Ne, Ideal.eq_top_iff_one]`. Introduce `h`. Establish `h1 : Geo.IsMultiHomog (ι` using `blockIdx n) (1 : MvPolynomial (Coord n) ℤ) 0 := (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_one ℤ _)`.

Use `(hIff ι n x hx v 1 0 h1).mp h` as an intermediate fact. Simplify using `[evalCone] at this`. Introduce `F G hF hG hFG`. Take `⟨d, hd⟩` from `hform F hF`. Take `⟨e, he⟩` from `hform G hG`.

Establish `hde : Geo.IsMultiHomog (ι` using `blockIdx n) (F * G) (d + e) := (geoMultiHomog_iff _ _).mpr (((geoMultiHomog_iff _ _).mp hd).mul ((geoMultiHomog_iff _ _).mp he))`. Establish `hlt` using `(hIff ι n x hx v _ _ hde).mp hFG`. Use `by_contra! hno`. Establish `h1` using `not_lt.mp (mt (hIff ι n x hx v F d hd).mpr hno.1)`. Establish `h2` using `not_lt.mp (mt (hIff ι n x hx v G e he).mpr hno.2)`.

Rewrite `hlt` using `[evalCone, eval₂_mul, map_mul, ← evalCone, ← evalCone]`. Use `mul_le_mul h1 h2 (hM0 e) (apply_nonneg v _)` as an intermediate fact. Rewrite `this` using `[← hMadd]`. Conclude with `absurd hlt (not_lt.mpr this)`.
-/
theorem OrbitCenterPrime.proof (hIff : OrbitCenterMemIff.Statement) :
    OrbitCenterPrime.Statement := by
  intro ι _ _ n x hx v
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  let w : Coord n → Lex (ι → ℕ) := fun c ↦ toLex (coordDeg n c)
  let _ : DecidableEq (Lex (ι → ℕ)) := LinearOrder.toDecidableEq
  have _ : GradedRing (weightedHomogeneousSubmodule ℤ w) := MvPolynomial.weightedGradedAlgebra ℤ w
  have hw : ∀ (F : MvPolynomial (Coord n) ℤ) (d : ι → ℕ),
      IsWeightedHomogeneous w F (toLex d) ↔ IsWeightedHomogeneous (coordDeg n) F d :=
    fun _ _ ↦ Iff.rfl
  set M : (ι → ℕ) → ℝ := fun d ↦ ∏ k, (⨆ i, v (coordVec x k i)) ^ d k with hM
  have hM0 : ∀ d, 0 ≤ M d := fun d ↦
    Finset.prod_nonneg fun k _ ↦ pow_nonneg (Real.iSup_nonneg fun i ↦ apply_nonneg v _) _
  have hMadd : ∀ d e, M (d + e) = M d * M e := fun d e ↦ by
    simp only [hM, Pi.add_apply, pow_add, Finset.prod_mul_distrib]

  have hform : ∀ F, SetLike.IsHomogeneousElem (weightedHomogeneousSubmodule ℤ w) F →
      ∃ d, Geo.IsMultiHomog (ι := blockIdx n) F d := by
    rintro F ⟨i, hi⟩
    exact ⟨ofLex i, (geoMultiHomog_iff _ _).mpr
      ((hw F (ofLex i)).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hi))⟩
  refine Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem
    (𝒜 := weightedHomogeneousSubmodule ℤ w) ?_ ?_ ?_
  · refine Ideal.homogeneous_span _ _ ?_
    rintro F ⟨d, hd, -⟩
    exact ⟨toLex d, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
      ((hw F d).mpr ((geoMultiHomog_iff _ _).mp hd))⟩
  · rw [Ne, Ideal.eq_top_iff_one]
    intro h
    have h1 : Geo.IsMultiHomog (ι := blockIdx n) (1 : MvPolynomial (Coord n) ℤ) 0 :=
      (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_one ℤ _)
    have := (hIff ι n x hx v 1 0 h1).mp h
    simp [evalCone] at this
  · intro F G hF hG hFG
    obtain ⟨d, hd⟩ := hform F hF
    obtain ⟨e, he⟩ := hform G hG
    have hde : Geo.IsMultiHomog (ι := blockIdx n) (F * G) (d + e) :=
      (geoMultiHomog_iff _ _).mpr
        (((geoMultiHomog_iff _ _).mp hd).mul ((geoMultiHomog_iff _ _).mp he))
    have hlt := (hIff ι n x hx v _ _ hde).mp hFG
    by_contra! hno
    have h1 := not_lt.mp (mt (hIff ι n x hx v F d hd).mpr hno.1)
    have h2 := not_lt.mp (mt (hIff ι n x hx v G e he).mpr hno.2)
    rw [evalCone, eval₂_mul, map_mul, ← evalCone, ← evalCone] at hlt
    have := mul_le_mul h1 h2 (hM0 e) (apply_nonneg v _)
    rw [← hMadd] at this
    exact absurd hlt (not_lt.mpr this)

end GroundTheory.Heights₂.Heights
