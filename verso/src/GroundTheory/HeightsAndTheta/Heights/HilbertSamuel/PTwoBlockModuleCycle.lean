import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockModuleCycle
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockFnField
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DimOfMinimal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockModuleCycleAlt

section General

variable {K : Type} {ι : K → Type} {τ : Type}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨⟨h.1.1, key W h.1.1 le_rfl h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, hJ.trans hQ.2⟩ hQW⟩`. Introduce `h`. Conclude with `⟨⟨h.1.1, hJ.trans h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, key Q hQ.1 hQW hQ.2⟩ hQW⟩`.
-/
theorem mem_minimalPrimes_iff_of {R : Type*} [CommRing R] {J J' W : Ideal R} (hJ : J ≤ J')
    (key : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → J ≤ Q → J' ≤ Q) :
    W ∈ J.minimalPrimes ↔ W ∈ J'.minimalPrimes := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, key W h.1.1 le_rfl h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, hJ.trans hQ.2⟩ hQW⟩
  · intro h
    exact ⟨⟨h.1.1, hJ.trans h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, key Q hQ.1 hQW hQ.2⟩ hQW⟩

/- English proof (translation)
Use `sup_le le_sup_left (Ideal.span_le.mpr ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))`.
-/
theorem sup_range_le {R : Type*} [CommRing R] (P : Ideal R) (s : R) (v : τ → R) :
    P ⊔ Ideal.span (Set.range fun j => s * v j) ≤ P ⊔ Ideal.span {s} := by
  refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

/- English proof (translation)
Take `⟨p, hp, r, hr, rfl⟩` from `Submodule.mem_sup.mp hy`. Take `⟨t, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`. Rewrite using `[mul_add]`. Use `Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hp)) (Ideal.mem_sup_right ?_)` and prove the remaining obligations. Establish `e : v i * (t * s) = t * (s * v i)` using `by ring`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)`.
-/
theorem mul_mem_sup_range {R : Type*} [CommRing R] {P : Ideal R} {s : R} {v : τ → R} (i : τ) {y : R}
    (hy : y ∈ P ⊔ Ideal.span {s}) : v i * y ∈ P ⊔ Ideal.span (Set.range fun j => s * v j) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hp)) (Ideal.mem_sup_right ?_)
  have e : v i * (t * s) = t * (s * v i) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Use `hW` as an intermediate fact. Unfold `multAt`. Rewrite using `[dif_pos hW, dif_pos hW, GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedQuot_eq_of_mul_le (sup_range_le P s v) hi (fun y hy => mul_mem_sup_range i hy)]`.
-/
theorem multAt_sup_range_eq {P W : Ideal (MRing ι)} {s : MRing ι} {v : τ → MRing ι} (hW : W.IsPrime) {i : τ}
    (hi : v i ∉ W) : multAt (P ⊔ Ideal.span (Set.range fun j => s * v j)) W = multAt (P ⊔ Ideal.span {s}) W := by
  have := hW
  unfold multAt
  rw [dif_pos hW, dif_pos hW, GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedQuot_eq_of_mul_le
    (sup_range_le P s v) hi (fun y hy => mul_mem_sup_range i hy)]

/- English proof (translation)
Use `hW` as an intermediate fact. Unfold `multAt`. Rewrite using `[dif_pos hW, Module.length_eq_zero_iff.mpr (GroundTheory.Heights₂.Heights.NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]`. Both sides reduce to the same expression.
-/
theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dif_pos hW, Module.length_eq_zero_iff.mpr
    (GroundTheory.Heights₂.Heights.NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

/- English proof (translation)
Establish `hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0` using `(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h`. Simplify using `[charOf, hg]`.
-/
theorem log_charOf_of_horizontal {W : Ideal (MRing ι)} (h : IsHorizontal W) : Real.log (charOf W) = 0 := by
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h
  simp [charOf, hg]

open Classical in

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[log_charOf_of_horizontal h, zero_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vert_weight_eq (W : Ideal (MRing ι)) (g : ℤ) :
    (if IsHorizontal W then 0 else (g : ℝ) * Real.log (charOf W)) = Real.log (charOf W) * g := by
  split_ifs with h
  · rw [log_charOf_of_horizontal h, zero_mul]
  · ring

end General

section TwoBlock

variable {Ω : Type} [Field Ω] {κ : Type}

/- English proof (translation)
The claim follows from `RingHom.mem_ker`.
-/
theorem mem_twoBlockIdeal {x x' : Ix κ → Ω} {f : MRing (FinTwoTypeFamily κ)} :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (ι := FinTwoTypeFamily κ) (pair x x') f = 0 :=
  RingHom.mem_ker

/- English proof (translation)
Simplify using `[mConeMap, pair]`.
-/
theorem mConeMap_X_zero (x x' : Ix κ → Ω) (i : κ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (X ⟨0, i⟩) = MvPolynomial.C (x ⟨(), i⟩) * MvPolynomial.X 0 := by
  simp [mConeMap, pair]

/- English proof (translation)
Simplify using `[twoBlockNum, mConeMap, pair, Finset.sum_mul, mul_assoc, map_sum]`.
-/
theorem mConeMap_num [Fintype κ] (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (twoBlockNum l) =
      MvPolynomial.C (∑ j, (l j : Ω) * x' j) * MvPolynomial.X 1 := by
  simp [twoBlockNum, mConeMap, pair, Finset.sum_mul, mul_assoc, map_sum]

/- English proof (translation)
Rewrite using `[mem_twoBlockIdeal, map_sub, map_mul, map_mul, mConeMap_num, mConeMap_num, twoBlockDen, mConeMap_X_zero, mConeMap_X_zero, ← hl, ← hm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rel_mem [Fintype κ] (x x' : Ix κ → Ω) (c : κ) (l m : Ix κ → ℤ) (i : κ)
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j) (hm : x ⟨(), i⟩ = ∑ j, (m j : Ω) * x' j) :
    X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum m ∈ twoBlockIdeal x x' := by
  rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, mConeMap_num, mConeMap_num, twoBlockDen,
    mConeMap_X_zero, mConeMap_X_zero, ← hl, ← hm]
  ring

end TwoBlock

end TwoBlockModuleCycleAlt

open TwoBlockModuleCycleAlt in

/- English proof (translation)
Introduce `D Ω _ _ κ _ x B c l hX hx hB hsp hl e`. Take `⟨hFp, -⟩` from `TwoBlockFnField.proof Ω κ x B hB`. Establish `hxA : IsArithVar (mCoordIdeal (ι` using `GlobalTheory κ) x) (D + 1) := by`. Rewrite using `[← coordIdeal_eq_mCoordIdeal]`. Conclude with `hX`.

Establish `hxc : x ⟨(), c⟩ ≠ 0` using `hx.ne_zero _`. Establish `hx0 : x ≠ 0` using `fun h => hxc (by rw [h]; rfl)`. Take `⟨B', -, hB'⟩` from `isInvMat_mul hB`. Establish `hBx0 : matAct B x ≠ 0` using `fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)`. Take `⟨⟨⟨⟩, i₀⟩, hi₀⟩` from `Function.ne_iff.mp hx0`.

Take `⟨⟨⟨⟩, i₁⟩, hi₁⟩` from `Function.ne_iff.mp hBx0`. Establish `hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1)` using `CoordArithOfFnField.proof Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩ (fun k => by fin_cases k`. Conclude with `⟨i₀, by simpa [pair] using hi₀⟩`. Conclude with `⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA`. Establish `hPp : (twoBlockIdeal x (matAct B x)).IsPrime` using `hpA.2.1.1`.

Establish `hdim` using `hpA.2.2.2`. Establish `hnumP : twoBlockNum l ∉ twoBlockIdeal x (matAct B x)`. Rewrite using `[mem_twoBlockIdeal, mConeMap_num, ← hl]`. Simplify using `[hxc]`. Establish `hm : ∀ i : κ, ∃ m : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (m j : Ω) * matAct B x j`.

Introduce `i`. Establish `h` using `hsp (Submodule.subset_span ⟨⟨(), i⟩, rfl⟩)`. Take `⟨m, hm⟩` from `(Submodule.mem_span_range_iff_exists_fun ℤ).mp h`. Conclude with `⟨m, by rw [← hm]; simp [zsmul_eq_mul]⟩`. Use `choose m hm using hm`.

Establish `hden_num : ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → twoBlockIdeal x (matAct B x) ≤ Q → (∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q) → twoBlockDen c ∈ Q → twoBlockNum l ∈ Q`. Introduce and unpack `Q hQ hPQ ⟨i, hi⟩ hd`. Establish `h1` using `hPQ (rel_mem x (matAct B x) c l (m i) i hl (hm i))`. Establish `h2 : X ⟨0, i⟩ * twoBlockNum l ∈ Q`. Establish `e : X ⟨0, i⟩ * twoBlockNum l = (X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum (m i)) + twoBlockDen c * twoBlockNum (m i)`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Q.add_mem h1 (Q.mul_mem_right _ hd)`. Conclude with `(hQ.mem_or_mem h2).resolve_left hi`. Establish `hmin : ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsRelevant W → (W ∈ (twoBlockMInner x (matAct B x) l).minimalPrimes ↔ W ∈ (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}).minimalPrimes)`.

Introduce `W hrel`. Use `mem_minimalPrimes_iff_of (sup_range_le _ _ _) fun Q hQ hQW hJQ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hrel 0`. Establish `hiQ : (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q` using `fun h => hi (hQW h)`. Establish `hn : twoBlockNum l * X ⟨0, i⟩ ∈ Q` using `hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))`.

Conclude with `sup_le (le_sup_left.trans hJQ) ((Ideal.span_singleton_le_iff_mem _).mpr ((hQ.mem_or_mem hn).resolve_right hiQ))`. Establish `hT : topComps (twoBlockMInner x (matAct B x) l) D = divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l)`. Use extensionality with `W`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hW, hrel, -⟩`.

Conclude with `⟨(hmin W hrel).mp hW, hrel⟩`. Introduce and unpack `⟨hW, hrel⟩`. Conclude with `⟨(hmin W hrel).mpr hW, hrel, dim_of_minimal hnumP hW hdim⟩`. Establish `hsub : divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) ⊆ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l)`. Introduce and unpack `W ⟨hW, hrel⟩`.

Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hPW : twoBlockIdeal x (matAct B x) ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hdW : twoBlockDen c ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Establish `hnW` using `hden_num W hWp hPW (hrel 0) hdW`. Take `⟨Q, hQ, hQW⟩` from `Ideal.exists_minimalPrimes_le (sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hnW))`.

Establish `hQeq : Q = W` using `ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes hPp hW hQ.1.1 (le_sup_left.trans hQ.1.2) (hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hnumP hQW`. Conclude with `⟨hQeq ▸ hQ, hrel⟩`. Establish `hback : ∀ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l), twoBlockDen c ∈ W → W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c)`. Introduce and unpack `W ⟨hW, hrel⟩ hdW`. Use `⟨⟨⟨hW.1.1, sup_le (le_sup_left.trans hW.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hdW)⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, ?_⟩ hQW⟩, hrel⟩` and prove the remaining obligations.

Establish `hPQ` using `le_sup_left.trans hQ.2`. Establish `hrQ : ∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q`. Take `⟨i, hi⟩` from `hrel 0`. Conclude with `⟨i, fun h => hi (hQW h)⟩`. Conclude with `sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr (hden_num Q hQ.1 hPQ hrQ (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))))`.

Rewrite using `[hT]`. Unfold `twoBlockVert vertCycleNum`. Establish `hfin` using `divSupp_finite (twoBlockIdeal x (matAct B x)) (twoBlockNum l)`. Establish `hden_sum : ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c), (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) = ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBloc …`. Use `finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => hsub h, fun h => hback W h ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hd`. Apply `hW` to reduce the goal to its premises. Use `show (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * _ = 0`. Rewrite using `[multAt_eq_zero_of_not_le h.1.1.1 fun hle => hd (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))]`. Simplify using the standard rewrite rules.

Rewrite using `[hden_sum, ← finsum_mem_sub_distrib _ _ hfin]`. Use `finsum_mem_congr rfl fun W hW => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hW.2 0`. Take `⟨j, hj⟩` from `hW.2 1`. Establish `h1 : multAt (twoBlockMInner x (matAct B x) l) W = multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W` using `multAt_sup_range_eq (s := twoBlockNum l) (v := fun i : κ => (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hi`.

Establish `h2 : multAt (twoBlockMOuter x (matAct B x) c) W = multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W` using `multAt_sup_range_eq (s := twoBlockDen c) (v := fun j : κ => (X ⟨1, j⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hj`. Rewrite using `[h1, h2, vert_weight_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem TwoBlockModuleCycle.proof : TwoBlockModuleCycle.Statement := by
  classical
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl e

  obtain ⟨hFp, -⟩ := TwoBlockFnField.proof Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hX
  have hxc : x ⟨(), c⟩ ≠ 0 := hx.ne_zero _
  have hx0 : x ≠ 0 := fun h => hxc (by rw [h]; rfl)
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    CoordArithOfFnField.proof Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hPp : (twoBlockIdeal x (matAct B x)).IsPrime := hpA.2.1.1
  have hdim := hpA.2.2.2

  have hnumP : twoBlockNum l ∉ twoBlockIdeal x (matAct B x) := by
    rw [mem_twoBlockIdeal, mConeMap_num, ← hl]
    simp [hxc]

  have hm : ∀ i : κ, ∃ m : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (m j : Ω) * matAct B x j := by
    intro i
    have h := hsp (Submodule.subset_span ⟨⟨(), i⟩, rfl⟩)
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨m, by rw [← hm]; simp [zsmul_eq_mul]⟩
  choose m hm using hm

  have hden_num : ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → twoBlockIdeal x (matAct B x) ≤ Q →
      (∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q) → twoBlockDen c ∈ Q → twoBlockNum l ∈ Q := by
    rintro Q hQ hPQ ⟨i, hi⟩ hd
    have h1 := hPQ (rel_mem x (matAct B x) c l (m i) i hl (hm i))
    have h2 : X ⟨0, i⟩ * twoBlockNum l ∈ Q := by
      have e : X ⟨0, i⟩ * twoBlockNum l =
          (X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum (m i)) + twoBlockDen c * twoBlockNum (m i) := by
        ring
      rw [e]
      exact Q.add_mem h1 (Q.mul_mem_right _ hd)
    exact (hQ.mem_or_mem h2).resolve_left hi

  have hmin : ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsRelevant W →
      (W ∈ (twoBlockMInner x (matAct B x) l).minimalPrimes ↔
        W ∈ (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}).minimalPrimes) := by
    intro W hrel
    refine mem_minimalPrimes_iff_of (sup_range_le _ _ _) fun Q hQ hQW hJQ => ?_
    obtain ⟨i, hi⟩ := hrel 0
    have hiQ : (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := fun h => hi (hQW h)
    have hn : twoBlockNum l * X ⟨0, i⟩ ∈ Q :=
      hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    exact sup_le (le_sup_left.trans hJQ)
      ((Ideal.span_singleton_le_iff_mem _).mpr ((hQ.mem_or_mem hn).resolve_right hiQ))
  have hT : topComps (twoBlockMInner x (matAct B x) l) D = divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    ext W
    constructor
    · rintro ⟨hW, hrel, -⟩
      exact ⟨(hmin W hrel).mp hW, hrel⟩
    · rintro ⟨hW, hrel⟩
      exact ⟨(hmin W hrel).mpr hW, hrel, dim_of_minimal hnumP hW hdim⟩

  have hsub : divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) ⊆
      divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    rintro W ⟨hW, hrel⟩
    have hWp : W.IsPrime := hW.1.1
    have hPW : twoBlockIdeal x (matAct B x) ≤ W := le_sup_left.trans hW.1.2
    have hdW : twoBlockDen c ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnW := hden_num W hWp hPW (hrel 0) hdW
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hnW))
    have hQeq : Q = W := ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes hPp hW hQ.1.1
      (le_sup_left.trans hQ.1.2) (hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hnumP hQW
    exact ⟨hQeq ▸ hQ, hrel⟩

  have hback : ∀ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l), twoBlockDen c ∈ W →
      W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) := by
    rintro W ⟨hW, hrel⟩ hdW
    refine ⟨⟨⟨hW.1.1, sup_le (le_sup_left.trans hW.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hdW)⟩,
      fun Q hQ hQW => hW.2 ⟨hQ.1, ?_⟩ hQW⟩, hrel⟩
    have hPQ := le_sup_left.trans hQ.2
    have hrQ : ∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := by
      obtain ⟨i, hi⟩ := hrel 0
      exact ⟨i, fun h => hi (hQW h)⟩
    exact sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr
      (hden_num Q hQ.1 hPQ hrQ (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))))

  rw [hT]
  unfold twoBlockVert vertCycleNum
  have hfin := divSupp_finite (twoBlockIdeal x (matAct B x)) (twoBlockNum l)
  have hden_sum :
      ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) =
        ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) := by
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => hsub h, fun h => hback W h ?_⟩
    by_contra hd
    apply hW
    show (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * _ = 0
    rw [multAt_eq_zero_of_not_le h.1.1.1 fun hle =>
      hd (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))]
    simp
  rw [hden_sum, ← finsum_mem_sub_distrib _ _ hfin]
  refine finsum_mem_congr rfl fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 0
  obtain ⟨j, hj⟩ := hW.2 1
  have h1 : multAt (twoBlockMInner x (matAct B x) l) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W :=
    multAt_sup_range_eq (s := twoBlockNum l) (v := fun i : κ => (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hi
  have h2 : multAt (twoBlockMOuter x (matAct B x) c) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W :=
    multAt_sup_range_eq (s := twoBlockDen c) (v := fun j : κ => (X ⟨1, j⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hj
  rw [h1, h2, vert_weight_eq]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
