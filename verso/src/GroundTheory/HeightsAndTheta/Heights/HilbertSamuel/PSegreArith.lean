import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SegreArithmetic

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {Ω : Type} [Field Ω]

omit [DecidableEq K] in

/- English proof (translation)
Simplify using `only [segreCoords, Finset.prod_div_distrib]`.
-/
theorem segreCoords_div (y : (Σ k, ι k) → Ω) (f c : (k : K) → ι k) :
    segreCoords y ⟨(), f⟩ / segreCoords y ⟨(), c⟩ = ∏ k, y ⟨k, f k⟩ / y ⟨k, c k⟩ := by
  simp only [segreCoords, Finset.prod_div_distrib]

/- English proof (translation)
Rewrite using `[segreCoords_div, Finset.prod_eq_single k]`. Rewrite using `[Function.update_self]`. Introduce `j _ hj`. Rewrite using `[Function.update_of_ne hj]`. Conclude with `div_self (hc j)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem ratio_eq_segre (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (k : K) (i : ι k) :
    y ⟨k, i⟩ / y ⟨k, c k⟩ =
      segreCoords y ⟨(), Function.update c k i⟩ / segreCoords y ⟨(), c⟩ := by
  rw [segreCoords_div, Finset.prod_eq_single k]
  · rw [Function.update_self]
  · intro j _ hj
    rw [Function.update_of_ne hj]
    exact div_self (hc j)
  · intro h
    exact absurd (Finset.mem_univ k) h

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Use `charZero_of_injective_algebraMap (R := ℤ) (A := Ω) ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `n hn`. Establish `hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)`. Rewrite using `[Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes, MvPolynomial.algebraMap_apply, C_eq_zero]`.

Conclude with `hn`. Rewrite `hmem` using `[show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h]`. Conclude with `(Ideal.mem_bot).mp hmem`.
-/
theorem charZero_of_horizontal (y : (Σ k, ι k) → Ω)
    (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_injective_algebraMap (R := ℤ) (A := Ω) ?_
  rw [injective_iff_map_eq_zero]
  intro n hn
  have hmem : n ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes,
      MvPolynomial.algebraMap_apply, C_eq_zero]
    exact hn
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from h] at hmem
  exact (Ideal.mem_bot).mp hmem

end SegreArithmetic

open SegreArithmetic BlockImageArithmetic in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ y D hY`. Take `⟨hK, ⟨_, _, hrel⟩, hhor, hdim⟩` from `hY`. Establish `: CharZero Ω` using `charZero_of_horizontal y hhor`. Establish `hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0`. Introduce `k`.

Take `⟨i, hi⟩` from `hrel k`. Use `⟨i, fun h0 ↦ hi ?_⟩` and prove the remaining obligations. Use `show mConeMap y (X ⟨k, i⟩) = 0`. Simplify using `[mConeMap, h0]`. Use `choose c hc using hnz`.

Use `set x := segreCoords y with hx`. Set `c' : ∀ u, GlobalTheory ((k : K) → ι k) u` to `fun _ ↦ c`. Establish `hx0 : x ⟨(), c⟩ ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k`. Establish `hc' : ∀ u, x ⟨u, c' u⟩ ≠ 0` using `fun _ ↦ hx0`. Use `set Fy := CoordinateConeArithVar.ratioField y c with hFy`.

Use `set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory ((k : K) → ι k)) x c' with hFx`. Establish `hLx : Fx ≤ Fy`. Rewrite using `[hFx, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨u, f⟩, rfl⟩`. Use `show x ⟨u, f⟩ / x ⟨u, c⟩ ∈ Fy`.

Rewrite using `[hx, segreCoords_div]`. Conclude with `prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, f k⟩, rfl⟩`. Establish `hLy : Fy ≤ Fx`. Rewrite using `[hFy, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`.

Use `show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx`. Rewrite using `[ratio_eq_segre y c hc k i]`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨(), Function.update c k i⟩, rfl⟩`. Establish `hLeq : Fy = Fx` using `le_antisymm hLy hLx`. Establish `hdy` using `ringKrullDim_eq y c hc`.

Rewrite `hdy` using `[hdim]`. Rewrite using `[coordIdeal_eq_mCoordIdeal]`. Use `⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x, CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩` and prove the remaining obligations. Rewrite using `[ringKrullDim_eq x c' hc']`. Rewrite `hdy` using `[← hFy, hLeq]`.

Generalize the expression as in `(Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢`. Establish `h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1` using `by exact_mod_cast hdy`. Proceed by induction on `t using ENat.recTopCoe with`. Consider the case `top => simp at h1`. Consider the case `coe t`.

Establish `h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1` using `by exact_mod_cast h1`. Establish `h3 : t = D` using `by omega`. Substitute `h3` using the available equality. Rewrite using `[Fintype.card_unit]`. Use `norm_cast`.
-/
theorem SegreArith.proof : SegreArith.Statement := by
  intro K _ _ ι _ Ω _ y D hY
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, hhor, hdim⟩ := hY
  have : CharZero Ω := charZero_of_horizontal y hhor
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  set x := segreCoords y with hx
  let c' : ∀ u, GlobalTheory ((k : K) → ι k) u := fun _ ↦ c
  have hx0 : x ⟨(), c⟩ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ ↦ hc k
  have hc' : ∀ u, x ⟨u, c' u⟩ ≠ 0 := fun _ ↦ hx0
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory ((k : K) → ι k)) x c' with hFx
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨u, f⟩, rfl⟩
    show x ⟨u, f⟩ / x ⟨u, c⟩ ∈ Fy
    rw [hx, segreCoords_div]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, f k⟩, rfl⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    rw [ratio_eq_segre y c hc k i]
    exact IntermediateField.subset_adjoin _ _ ⟨⟨(), Function.update c k i⟩, rfl⟩
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
