import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

namespace AddBlockData

variable {P : ArithVariety n} (D : AddBlockData P)

/- English proof (translation)
Use `MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)` and prove the remaining obligations. Simplify using `[extMap, liftOld, oldCoord, extVal]`.
-/
theorem extMap_comp_liftOld :
    D.extMap.comp D.liftOld.toRingHom =
      eval₂Hom (Int.castRingHom _) fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1) := by
  refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun v ↦ ?_)
  simp [extMap, liftOld, oldCoord, extVal]

/- English proof (translation)
Rewrite using `[coe_eval₂Hom, eval₂_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, weight_coordDeg_apply, Fintype.prod_sigma, Finset.prod_pow_eq_pow_sum]`. Simplify using `[mul_assoc]`.
-/
theorem eval₂Hom_monomial_blockVal (d : Coord n →₀ ℕ) (r : ℤ) :
    eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
        (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) (monomial d r) =
      C (P.mkF (monomial d r)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) d k) := by
  rw [coe_eval₂Hom, eval₂_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow,
    weight_coordDeg_apply, Fintype.prod_sigma, Finset.prod_pow_eq_pow_sum]
  simp [mul_assoc]

/- English proof (translation)
Establish `h : D.extMap (D.liftOld f) = eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField)) (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) f`. Rewrite using `[← D.extMap_comp_liftOld]`. Both sides reduce to the same expression. Rewrite using `[h]`. Use `conv_lhs => rw [f.as_sum]`.

Use `conv_rhs => rw [f.as_sum]`. Rewrite using `[map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd ↦ ?_` and prove the remaining obligations. Rewrite using `[eval₂Hom_monomial_blockVal, hf (mem_support_iff.mp hd)]`.
-/
theorem extMap_liftOld_of_isWeightedHomogeneous {f : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hf : IsWeightedHomogeneous (coordDeg n) f δ) :
    D.extMap (D.liftOld f) = C (P.mkF f) * ∏ k, X (some k) ^ δ k := by
  have h : D.extMap (D.liftOld f) = eval₂Hom (Int.castRingHom (MvPolynomial (Option ι) P.FunField))
      (fun v : Coord n ↦ C (P.mkF (X v)) * X (some v.1)) f := by
    rw [← D.extMap_comp_liftOld]
    rfl
  rw [h]
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [eval₂Hom_monomial_blockVal, hf (mem_support_iff.mp hd)]

/- English proof (translation)
Simplify using `only [evalCone, liftOld]`. Rewrite using `[eval₂_rename]`. Both sides reduce to the same expression.
-/
theorem evalCone_liftOld {F : Type*} [CommRing F] (w : Cone D.extSizes F) (f : MvPolynomial (Coord n) ℤ) :
    evalCone w (D.liftOld f) = evalCone (D.basePart₂ w) f := by
  simp only [evalCone, liftOld]
  rw [eval₂_rename]
  rfl

/- English proof (translation)
Rewrite using `[extIdeal, RingHom.mem_ker]`. Use `conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_eq_zero fun m _ ↦ ?_` and prove the remaining obligations. Rewrite using `[D.extMap_liftOld_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous m f), (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, zero_mul]`.
-/
theorem liftOld_mem_extIdeal {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ P.ideal) :
    D.liftOld f ∈ D.extIdeal := by
  rw [extIdeal, RingHom.mem_ker]
  conv_lhs => rw [← sum_weightedHomogeneousComponent (coordDeg n) f,
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
  rw [map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [D.extMap_liftOld_of_isWeightedHomogeneous (weightedHomogeneousComponent_isWeightedHomogeneous m f),
    (P.mkF_eq_zero_iff _).mpr (P.homogeneous f hf m), map_zero, zero_mul]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by`. Simplify `hc` using `[ArithVariety.IsLive]`. Conclude with `P.ideal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)) (P.ideal.pow_mem_of_mem hk (d k) (hd k))`.
-/
theorem chartMonomial_mem_of_not_isLive {c : (k : ι) → Fin (n k + 1)} (hc : ¬ P.IsLive c)
    {d : ι → ℕ} (hd : ∀ k, 1 ≤ d k) : chartMonomial c d ∈ P.ideal := by
  obtain ⟨k, hk⟩ : ∃ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∈ P.ideal := by
    simpa [ArithVariety.IsLive] using hc
  exact P.ideal.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))
    (P.ideal.pow_mem_of_mem hk (d k) (hd k))

/- English proof (translation)
Distinguish the cases in `hc : P.IsLive c`. Distinguish the cases in `hc' : P.IsLive c'`. Rewrite using `[← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg.dead c' hc' j, mul_zero, sub_zero]`.

Conclude with `P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc' hg.pos)`. Rewrite using `[hg.dead c hc j, mul_zero, zero_sub]`. Conclude with `P.ideal.neg_mem_iff.mpr (P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc hg.pos))`.
-/
theorem IsFormSystem.cross_mem {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) (c c' : (k : ι) → Fin (n k + 1)) (j : Fin (D.size + 1)) :
    chartMonomial c' d * g c j - chartMonomial c d * g c' j ∈ P.ideal := by
  by_cases hc : P.IsLive c
  · by_cases hc' : P.IsLive c'
    · rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, hg.value c hc j, hg.value c' hc' j]
      ring
    · rw [hg.dead c' hc' j, mul_zero, sub_zero]
      exact P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc' hg.pos)
  · rw [hg.dead c hc j, mul_zero, zero_sub]
    exact P.ideal.neg_mem_iff.mpr (P.ideal.mul_mem_right _ (chartMonomial_mem_of_not_isLive hc hg.pos))

end AddBlockData

open AddBlockData in

/- English proof (translation)
Introduce `ι _ _ n P D d g hg`. Establish `hom : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ (d k + D.deg k).toNat)`. Introduce `c j`. Take `⟨δ, hδ, hδk⟩` from `hg.homog c j`. Use `hδ using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Rewrite using `[← hδk k, Int.toNat_natCast]`. Establish `hX : ∀ i, D.extMap (X (D.newCoord i)) = C (D.elt i) * X none` using `fun i ↦ by`. Simplify using `[extMap, newCoord, extVal]`. Establish `part1 : ∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.size + 1)), D.liftOld (g c j) * X (D.newCoord i) - D.liftOld (g c i) * X (D.newCoord j) ∈ D.extIdeal`.

Introduce `c i j`. Rewrite using `[extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, hX, hX, D.extMap_liftOld_of_isWeightedHomogeneous (hom c j), D.extMap_liftOld_of_isWeightedHomogeneous (hom c i)]`. Distinguish the cases in `hc : P.IsLive c`. Rewrite using `[hg.value c hc j, hg.value c hc i]`. Simplify using `only [map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hg.dead c hc j, hg.dead c hc i]`. Simplify using the standard rewrite rules. Use `⟨part1, fun w hw ↦ ?_⟩` and prove the remaining obligations. Use `set z := D.basePart₂ w with hz`.

Use `set z' := D.newPart w with hz'`. Establish `hzP : z ∈ P.points ℂ` using `⟨fun k ↦ hw.1 (some k), fun f hf ↦ by`. Rewrite using `[← D.evalCone_liftOld]`. Conclude with `hw.2 _ (D.liftOld_mem_extIdeal hf)⟩`. Establish `rel : ∀ c i j, evalCone z (g c j) * z' i = evalCone z (g c i) * z' j`.

Introduce `c i j`. Establish `h` using `hw.2 _ (part1 c i j)`. Unfold `evalCone at h`. Rewrite `h` using `[eval₂_sub, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X]`. Express the relevant statement in the definitionally equal form `evalCone w (D.liftOld (g c j)) * _ - evalCone w (D.liftOld (g c i)) * _ = 0 at h`.

Rewrite `h` using `[evalCone_liftOld, evalCone_liftOld]`. Rewrite using `[← sub_eq_zero]`. Conclude with `h`. Establish `cross : ∀ c c' j, evalCone z (chartMonomial c' d) * evalCone z (g c j) = evalCone z (chartMonomial c d) * evalCone z (g c' j)`. Introduce `c c' j`.

Establish `h` using `hzP.2 _ (hg.cross_mem D c c' j)`. Rewrite using `[← sub_eq_zero]`. Simplify `h` using `[evalCone]`. Establish `hne : ∀ k, ∃ i, z k i ≠ 0` using `fun k ↦ Function.ne_iff.mp (hzP.1 k)`. Use `choose c₀ hc₀ using hne`.

Establish `hm₀ : evalCone z (chartMonomial c₀ d) ≠ 0`. Simplify using `only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc₀ k)`. Choose the witnesses or unpack the hypotheses as in `⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c₀ j) ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Simplify using `only [not_exists, not_not] at h`. Conclude with `hm₀ ((hV ι n P D d g hg z hzP c₀).mp h)`. Establish `hz'₀ : z' j₀ ≠ 0`. Introduce `h0`. Apply `hw.1 none` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `rel c₀ i j₀` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `(mul_eq_zero.mp this).resolve_left hj₀`. Use `⟨hzP, z' j₀ * evalCone z (chartMonomial c₀ d) / evalCone z (g c₀ j₀), div_ne_zero (mul_ne_zero hz'₀ hm₀) hj₀, fun c hc j ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_div_iff hc, div_mul_eq_mul_div, eq_div_iff hj₀]`. Take the linear combination `evalCone z (chartMonomial c d) * rel c₀ j j₀ - z' j₀ * cross c c₀ j`.
-/
theorem ConePoints.proof (hV : ChartVanishing.Statement) : ConePoints.Statement := by
  intro ι _ _ n P D d g hg
  have hom : ∀ c j, IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ (d k + D.deg k).toNat) := by
    intro c j
    obtain ⟨δ, hδ, hδk⟩ := hg.homog c j
    convert hδ using 1
    funext k
    rw [← hδk k, Int.toNat_natCast]
  have hX : ∀ i, D.extMap (X (D.newCoord i)) = C (D.elt i) * X none := fun i ↦ by
    simp [extMap, newCoord, extVal]
  have part1 : ∀ (c : (k : ι) → Fin (n k + 1)) (i j : Fin (D.size + 1)),
      D.liftOld (g c j) * X (D.newCoord i) - D.liftOld (g c i) * X (D.newCoord j) ∈ D.extIdeal := by
    intro c i j
    rw [extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, hX, hX,
      D.extMap_liftOld_of_isWeightedHomogeneous (hom c j), D.extMap_liftOld_of_isWeightedHomogeneous (hom c i)]
    by_cases hc : P.IsLive c
    · rw [hg.value c hc j, hg.value c hc i]
      simp only [map_mul]
      ring
    · rw [hg.dead c hc j, hg.dead c hc i]
      simp
  refine ⟨part1, fun w hw ↦ ?_⟩
  set z := D.basePart₂ w with hz
  set z' := D.newPart w with hz'
  have hzP : z ∈ P.points ℂ :=
    ⟨fun k ↦ hw.1 (some k), fun f hf ↦ by
      rw [← D.evalCone_liftOld]
      exact hw.2 _ (D.liftOld_mem_extIdeal hf)⟩

  have rel : ∀ c i j, evalCone z (g c j) * z' i = evalCone z (g c i) * z' j := by
    intro c i j
    have h := hw.2 _ (part1 c i j)
    unfold evalCone at h
    rw [eval₂_sub, eval₂_mul, eval₂_mul, eval₂_X, eval₂_X] at h
    change evalCone w (D.liftOld (g c j)) * _ - evalCone w (D.liftOld (g c i)) * _ = 0 at h
    rw [evalCone_liftOld, evalCone_liftOld] at h
    rw [← sub_eq_zero]
    exact h

  have cross : ∀ c c' j, evalCone z (chartMonomial c' d) * evalCone z (g c j) =
      evalCone z (chartMonomial c d) * evalCone z (g c' j) := by
    intro c c' j
    have h := hzP.2 _ (hg.cross_mem D c c' j)
    rw [← sub_eq_zero]
    simpa [evalCone] using h

  have hne : ∀ k, ∃ i, z k i ≠ 0 := fun k ↦ Function.ne_iff.mp (hzP.1 k)
  choose c₀ hc₀ using hne
  have hm₀ : evalCone z (chartMonomial c₀ d) ≠ 0 := by
    simp only [evalCone, chartMonomial, eval₂_prod, eval₂_pow, eval₂_X]
    exact Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc₀ k)
  obtain ⟨j₀, hj₀⟩ : ∃ j, evalCone z (g c₀ j) ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hm₀ ((hV ι n P D d g hg z hzP c₀).mp h)
  have hz'₀ : z' j₀ ≠ 0 := by
    intro h0
    apply hw.1 none
    funext i
    have := rel c₀ i j₀
    rw [h0, mul_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hj₀
  refine ⟨hzP, z' j₀ * evalCone z (chartMonomial c₀ d) / evalCone z (g c₀ j₀),
    div_ne_zero (mul_ne_zero hz'₀ hm₀) hj₀, fun c hc j ↦ ?_⟩
  rw [eq_div_iff hc, div_mul_eq_mul_div, eq_div_iff hj₀]
  linear_combination evalCone z (chartMonomial c d) * rel c₀ j j₀ - z' j₀ * cross c c₀ j

end

end GroundTheory.Heights₂.Heights
