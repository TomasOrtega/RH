import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G

namespace OrbitCenterMemIff

variable {ι : Type} [DecidableEq ι] {n : ι → ℕ}

open Classical in

/- English proof (translation)
Use extensionality with `m`. Distinguish the cases in `hj : j ∈ m.support`. Establish `hw : Finsupp.weight (coordDeg n) m = Finsupp.weight (coordDeg n) (m - Finsupp.single j 1) + coordDeg n j` using `by conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)))]`. Rewrite using `[map_add, Finsupp.weight_single, one_smul]`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_X_mul', if_pos hj]`.

Distinguish the cases in `h2 : coordDeg n j ≤ e`. Rewrite using `[if_pos h2, coeff_X_mul', if_pos hj, coeff_weightedHomogeneousComponent]`. Distinguish the cases in `h1 : Finsupp.weight (coordDeg n) m = e`. Rewrite using `[if_pos h1, if_pos (by rw [← h1, hw, add_tsub_cancel_right])]`. Rewrite using `[if_neg h1, if_neg]`.

Introduce `h3`. Conclude with `h1 (by rw [hw, h3, tsub_add_cancel_of_le h2])`. Rewrite using `[if_neg h2, coeff_zero, if_neg]`. Introduce `h1`. Apply `h2` to reduce the goal to its premises.

Rewrite using `[← h1, hw]`. Conclude with `le_add_self`. Rewrite using `[coeff_weightedHomogeneousComponent, coeff_X_mul', if_neg hj, ite_self]`. Distinguish the cases in `h2 : coordDeg n j ≤ e`. Rewrite using `[if_pos h2, coeff_X_mul', if_neg hj]`.

Rewrite using `[if_neg h2, coeff_zero]`.
-/
theorem weightedHomogeneousComponent_X_mul (j : Coord n) (G : MvPolynomial (Coord n) ℤ)
    (e : ι → ℕ) :
    weightedHomogeneousComponent (coordDeg n) e (X j * G) =
      if coordDeg n j ≤ e then X j * weightedHomogeneousComponent (coordDeg n) (e - coordDeg n j) G
      else 0 := by
  classical
  ext m
  by_cases hj : j ∈ m.support
  · have hw : Finsupp.weight (coordDeg n) m =
        Finsupp.weight (coordDeg n) (m - Finsupp.single j 1) + coordDeg n j := by
      conv_lhs => rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr
        (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)))]
      rw [map_add, Finsupp.weight_single, one_smul]
    rw [coeff_weightedHomogeneousComponent, coeff_X_mul', if_pos hj]
    by_cases h2 : coordDeg n j ≤ e
    · rw [if_pos h2, coeff_X_mul', if_pos hj, coeff_weightedHomogeneousComponent]
      by_cases h1 : Finsupp.weight (coordDeg n) m = e
      · rw [if_pos h1, if_pos (by rw [← h1, hw, add_tsub_cancel_right])]
      · rw [if_neg h1, if_neg]
        intro h3
        exact h1 (by rw [hw, h3, tsub_add_cancel_of_le h2])
    · rw [if_neg h2, coeff_zero, if_neg]
      intro h1
      apply h2
      rw [← h1, hw]
      exact le_add_self
  · rw [coeff_weightedHomogeneousComponent, coeff_X_mul', if_neg hj, ite_self]
    by_cases h2 : coordDeg n j ≤ e
    · rw [if_pos h2, coeff_X_mul', if_neg hj]
    · rw [if_neg h2, coeff_zero]

end OrbitCenterMemIff

open OrbitCenterMemIff in

/- English proof (translation)
Introduce `ι _ _ n x hx v F d hF`. Use `set M : ι → ℝ := fun k ↦ ⨆ i, v (coordVec x k i) with hMdef`. Establish `hMle : ∀ k i, v (coordVec x k i) ≤ M k` using `fun k i ↦ le_ciSup (Set.finite_range fun i ↦ v (coordVec x k i)).bddAbove i`. Establish `hM0 : ∀ k, 0 < M k`. Introduce `k`.

Take `⟨i, hi⟩` from `Function.ne_iff.mp (hx k)`. Conclude with `(FinitePlace.pos_iff.mpr fun h ↦ hi (congrArg Subtype.val h)).trans_le (hMle k i)`. Establish `hP0 : ∀ e : ι → ℕ, 0 < ∏ k, M k ^ e k` using `fun e ↦ Finset.prod_pos fun k _ ↦ pow_pos (hM0 k) _`. Set `P : MvPolynomial (Coord n) ℤ → Prop` to `fun G ↦ ∀ e : ι → ℕ, v (evalCone (coordVec x) (weightedHomogeneousComponent (coordDeg n) e G)) < ∏ k, M k ^ e k`. Establish `hadd : ∀ G H, P G → P H → P (G + H)` using `fun G H hG hH e ↦ by`.

Rewrite using `[map_add, evalCone, eval₂_add]`. Conclude with `(FinitePlace.add_le v _ _).trans_lt (max_lt (hG e) (hH e))`. Establish `hC : ∀ (m : ℤ) G, P G → P (C m * G)` using `fun m G hG e ↦ by`. Rewrite using `[weightedHomogeneousComponent_C_mul, evalCone, eval₂_mul, eval₂_C, map_mul]`. Establish `hm : v (Int.castRingHom (coordField x) m) ≤ 1` using `IsNonarchimedean.apply_intCast_le_one (FinitePlace.add_le v)`.

Conclude with `(mul_le_of_le_one_left (by positivity) hm).trans_lt (hG e)`. Establish `hX : ∀ j G, P G → P (X j * G)` using `fun j G hG e ↦ by`. Rewrite using `[weightedHomogeneousComponent_X_mul]`. Use `split_ifs with h`. Establish `hsplit : ∏ k, M k ^ e k = M j.1 * ∏ k, M k ^ (e - coordDeg n j) k`.

Establish `h1 : ∏ k, M k ^ e k = (∏ k, M k ^ coordDeg n j k) * ∏ k, M k ^ (e - coordDeg n j) k`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← pow_add, Pi.sub_apply, Nat.add_sub_cancel' (h k)]`. Rewrite using `[h1]`.

Use `congr 1`. Simplify using `[coordDeg, Pi.single_apply, pow_ite]`. Rewrite using `[hsplit, evalCone, eval₂_mul, eval₂_X, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[evalCone, eval₂_zero, map_zero]`.

Conclude with `hP0 e`. Establish `hmul : ∀ a G, P G → P (a * G)`. Introduce `a`. Proceed by induction on `a using MvPolynomial.induction_on with`. Consider the case `C m => exact hC m`.

Consider the case `add p q hp hq => exact fun G hG ↦ by rw [add_mul]; exact hadd _ _ (hp G hG) (hq G hG)`. Consider the case `mul_X p j hp => exact fun G hG ↦ by rw [mul_assoc]; exact hp _ (hX j G hG)`. Establish `hsmall : ∀ G ∈ orbitCenter x v, P G`. Introduce `G hG`. Use `Submodule.span_induction (p := fun G _ ↦ P G) ?_ ?_ ?_ ?_ hG` and prove the remaining obligations.

Introduce and unpack `F₀ ⟨d₀, hd₀, hlt⟩ e`. Establish `hh` using `(geoMultiHomog_iff F₀ d₀).mp hd₀`. Distinguish the cases in `he : e = d₀`. Substitute `he` using the available equality. Rewrite using `[hh.weightedHomogeneousComponent_same]` and apply the resulting hypothesis.

Rewrite using `[hh.weightedHomogeneousComponent_ne e he, evalCone, eval₂_zero, map_zero]`. Conclude with `hP0 e`. Introduce `e`. Rewrite using `[map_zero, evalCone, eval₂_zero, map_zero]`. Conclude with `hP0 e`.

Conclude with `fun G H _ _ hG hH ↦ hadd G H hG hH`. Conclude with `fun a G _ hG ↦ hmul a G hG`. Prove the components needed by the constructor for the conclusion. Introduce `hmem`. Establish `h` using `hsmall F hmem d`.

Rewrite `h` using `[((geoMultiHomog_iff F d).mp hF).weightedHomogeneousComponent_same]`. Then use the resulting hypothesis. Conclude with `fun h ↦ Ideal.subset_span ⟨d, hF, h⟩`.
-/
theorem OrbitCenterMemIff.proof : OrbitCenterMemIff.Statement := by
  classical
  intro ι _ _ n x hx v F d hF
  set M : ι → ℝ := fun k ↦ ⨆ i, v (coordVec x k i) with hMdef
  have hMle : ∀ k i, v (coordVec x k i) ≤ M k := fun k i ↦
    le_ciSup (Set.finite_range fun i ↦ v (coordVec x k i)).bddAbove i
  have hM0 : ∀ k, 0 < M k := by
    intro k
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact (FinitePlace.pos_iff.mpr fun h ↦ hi (congrArg Subtype.val h)).trans_le (hMle k i)
  have hP0 : ∀ e : ι → ℕ, 0 < ∏ k, M k ^ e k := fun e ↦
    Finset.prod_pos fun k _ ↦ pow_pos (hM0 k) _
  let P : MvPolynomial (Coord n) ℤ → Prop := fun G ↦ ∀ e : ι → ℕ,
    v (evalCone (coordVec x) (weightedHomogeneousComponent (coordDeg n) e G)) < ∏ k, M k ^ e k
  have hadd : ∀ G H, P G → P H → P (G + H) := fun G H hG hH e ↦ by
    rw [map_add, evalCone, eval₂_add]
    exact (FinitePlace.add_le v _ _).trans_lt (max_lt (hG e) (hH e))
  have hC : ∀ (m : ℤ) G, P G → P (C m * G) := fun m G hG e ↦ by
    rw [weightedHomogeneousComponent_C_mul, evalCone, eval₂_mul, eval₂_C, map_mul]
    have hm : v (Int.castRingHom (coordField x) m) ≤ 1 :=
      IsNonarchimedean.apply_intCast_le_one (FinitePlace.add_le v)
    exact (mul_le_of_le_one_left (by positivity) hm).trans_lt (hG e)
  have hX : ∀ j G, P G → P (X j * G) := fun j G hG e ↦ by
    rw [weightedHomogeneousComponent_X_mul]
    split_ifs with h
    · have hsplit : ∏ k, M k ^ e k = M j.1 * ∏ k, M k ^ (e - coordDeg n j) k := by
        have h1 : ∏ k, M k ^ e k = (∏ k, M k ^ coordDeg n j k) * ∏ k, M k ^ (e - coordDeg n j) k := by
          rw [← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun k _ ↦ ?_
          rw [← pow_add, Pi.sub_apply, Nat.add_sub_cancel' (h k)]
        rw [h1]
        congr 1
        simp [coordDeg, Pi.single_apply, pow_ite]
      rw [hsplit, evalCone, eval₂_mul, eval₂_X, map_mul]
      calc v (coordVec x j.1 j.2) * v (evalCone (coordVec x) _)
          ≤ M j.1 * v (evalCone (coordVec x) _) :=
            mul_le_mul_of_nonneg_right (hMle _ _) (by positivity)
        _ < _ := mul_lt_mul_of_pos_left (hG _) (hM0 _)
    · rw [evalCone, eval₂_zero, map_zero]
      exact hP0 e
  have hmul : ∀ a G, P G → P (a * G) := by
    intro a
    induction a using MvPolynomial.induction_on with
    | C m => exact hC m
    | add p q hp hq => exact fun G hG ↦ by rw [add_mul]; exact hadd _ _ (hp G hG) (hq G hG)
    | mul_X p j hp => exact fun G hG ↦ by rw [mul_assoc]; exact hp _ (hX j G hG)
  have hsmall : ∀ G ∈ orbitCenter x v, P G := by
    intro G hG
    refine Submodule.span_induction (p := fun G _ ↦ P G) ?_ ?_ ?_ ?_ hG
    · rintro F₀ ⟨d₀, hd₀, hlt⟩ e
      have hh := (geoMultiHomog_iff F₀ d₀).mp hd₀
      by_cases he : e = d₀
      · subst he
        rwa [hh.weightedHomogeneousComponent_same]
      · rw [hh.weightedHomogeneousComponent_ne e he, evalCone, eval₂_zero, map_zero]
        exact hP0 e
    · intro e
      rw [map_zero, evalCone, eval₂_zero, map_zero]
      exact hP0 e
    · exact fun G H _ _ hG hH ↦ hadd G H hG hH
    · exact fun a G _ hG ↦ hmul a G hG
  constructor
  · intro hmem
    have h := hsmall F hmem d
    rwa [((geoMultiHomog_iff F d).mp hF).weightedHomogeneousComponent_same] at h
  · exact fun h ↦ Ideal.subset_span ⟨d, hF, h⟩

end GroundTheory.Heights₂.Heights
