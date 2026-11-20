import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.TPos

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Unfold `reAt`. Establish `h` using `InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x`. Rewrite using `[← h, Complex.ofReal_re]`.
-/
theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  unfold reAt
  have h := InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v) x
  rw [← h, Complex.ofReal_re]

/- English proof (translation)
Rewrite using `[reAt_eq, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]`.
-/
theorem abs_reAt (v : InfinitePlace F) (x : F) : |reAt v x| = v x := by
  rw [reAt_eq, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v), Real.norm_eq_abs]

/- English proof (translation)
Use `set φ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) with hφ`. Establish `hx : (fun i => reAt v (x i)) = φ ∘ x`. Use function extensionality and compare the values at `i`. Simplify using `[reAt_eq, hφ]`. Establish `hG : (G.map (Int.cast : ℤ → ℝ)) = (G.map (Int.cast : ℤ → F)).map φ`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hx, hG, reAt_eq, ← hφ]`. Unfold `QF BF`. Rewrite using `[map_div₀, map_ofNat, RingHom.map_dotProduct]`.

Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `RingHom.map_mulVec φ _ x i`.
-/
theorem reAt_QF {κ : Type} [Fintype κ] (G : Matrix κ κ ℤ) (x : κ → F) (v : InfinitePlace F) :
    reAt v (QF G x) =
      (fun i => reAt v (x i)) ⬝ᵥ (G.map (Int.cast : ℤ → ℝ)) *ᵥ (fun i => reAt v (x i)) / 2 := by
  set φ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) with hφ
  have hx : (fun i => reAt v (x i)) = φ ∘ x := by
    funext i
    simp [reAt_eq, hφ]
  have hG : (G.map (Int.cast : ℤ → ℝ)) = (G.map (Int.cast : ℤ → F)).map φ := by
    ext i j
    simp
  rw [hx, hG, reAt_eq, ← hφ]
  unfold QF BF
  rw [map_div₀, map_ofNat, RingHom.map_dotProduct]
  congr 2
  funext i
  exact RingHom.map_mulVec φ _ x i

/- English proof (translation)
Break down `isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩` into its components or cases. Use `⟨1, one_pos, fun y => ?_⟩` and prove the remaining obligations. Simplify using `[dotProduct]`. Use `set f : (κ → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hf`. Establish `hfc : Continuous f`.

Simplify using `only [hf, dotProduct, Matrix.mulVec]`. Use `fun_prop`. Establish `hpos : ∀ y : κ → ℝ, y ≠ 0 → 0 < f y`. Introduce `y hy`. Use `(Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hy` as an intermediate fact.

Simplify `this` using `[hf]`. Use `set S : Set (κ → ℝ) := {y | ∑ i, y i ^ 2 = 1} with hS`. Establish `hSc : IsCompact S`. Apply `Metric.isCompact_of_isClosed_isBounded` to reduce the goal to its premises. Conclude with `isClosed_eq (by fun_prop) continuous_const`.

Rewrite using `[Metric.isBounded_iff_subset_closedBall 0]`. Use `⟨1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]`. Introduce `i`. Rewrite using `[Real.norm_eq_abs]`.

Establish `h1 : y i ^ 2 ≤ ∑ j, y j ^ 2` using `Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Rewrite `h1` using `[show ∑ j, y j ^ 2 = 1 from hy]`. Conclude with `(sq_le_one_iff_abs_le_one _).mp h1`. Establish `hSn : S.Nonempty` using `⟨Pi.single i0 1, by simp [hS, Pi.single_apply]⟩`. Take `⟨y0, hy0S, hmin⟩` from `hSc.exists_isMinOn hSn hfc.continuousOn`.

Establish `hy0 : y0 ≠ 0`. Introduce and unpack `rfl`. Simplify using `[hS] at hy0S`. Use `⟨f y0, hpos y0 hy0, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y = 0`.

Substitute `hy` using the available equality. Simplify using the standard rewrite rules. Use `set s := ∑ i, y i ^ 2 with hs`. Establish `hs0 : 0 < s`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hy`.

Establish `h1 : y i ^ 2 ≤ s` using `Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `hi' : y i ≠ 0` using `by simpa using hi`. Establish `: 0 < y i ^ 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set t := Real.sqrt s with ht`.

Establish `ht0 : 0 < t` using `Real.sqrt_pos.mpr hs0`. Establish `htt : t ^ 2 = s` using `Real.sq_sqrt hs0.le`. Establish `hz : t⁻¹ • y ∈ S`. Simplify using `only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]`. Rewrite using `[← Finset.mul_sum, ← hs, inv_pow, htt, inv_mul_cancel₀ hs0.ne']`.

Establish `hfz : f (t⁻¹ • y) = (t ^ 2)⁻¹ * f y`. Simplify using `only [hf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `hmin hz` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq] at this`.

Rewrite `this` using `[hfz, htt]`. Establish `h2` using `mul_le_mul_of_nonneg_left this hs0.le`. Rewrite `h2` using `[← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul]`. Combine the linear relations using `[mul_comm s (f y0)]`.
-/
theorem posDef_lower {κ : Type} [Fintype κ] (M : Matrix κ κ ℝ) (hM : M.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : κ → ℝ, c * ∑ i, y i ^ 2 ≤ y ⬝ᵥ M *ᵥ y := by
  classical
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
  · refine ⟨1, one_pos, fun y => ?_⟩
    simp [dotProduct]
  set f : (κ → ℝ) → ℝ := fun y => y ⬝ᵥ M *ᵥ y with hf
  have hfc : Continuous f := by
    simp only [hf, dotProduct, Matrix.mulVec]
    fun_prop
  have hpos : ∀ y : κ → ℝ, y ≠ 0 → 0 < f y := by
    intro y hy
    have := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hy
    simpa [hf] using this
  set S : Set (κ → ℝ) := {y | ∑ i, y i ^ 2 = 1} with hS
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact isClosed_eq (by fun_prop) continuous_const
    · rw [Metric.isBounded_iff_subset_closedBall 0]
      refine ⟨1, fun y hy => ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro i
      rw [Real.norm_eq_abs]
      have h1 : y i ^ 2 ≤ ∑ j, y j ^ 2 :=
        Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      rw [show ∑ j, y j ^ 2 = 1 from hy] at h1
      exact (sq_le_one_iff_abs_le_one _).mp h1
  have hSn : S.Nonempty := ⟨Pi.single i0 1, by simp [hS, Pi.single_apply]⟩
  obtain ⟨y0, hy0S, hmin⟩ := hSc.exists_isMinOn hSn hfc.continuousOn
  have hy0 : y0 ≠ 0 := by
    rintro rfl
    simp [hS] at hy0S
  refine ⟨f y0, hpos y0 hy0, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp
  set s := ∑ i, y i ^ 2 with hs
  have hs0 : 0 < s := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    have h1 : y i ^ 2 ≤ s :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hi' : y i ≠ 0 := by simpa using hi
    have : 0 < y i ^ 2 := by positivity
    linarith
  set t := Real.sqrt s with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hs0
  have htt : t ^ 2 = s := Real.sq_sqrt hs0.le
  have hz : t⁻¹ • y ∈ S := by
    simp only [hS, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum, ← hs, inv_pow, htt, inv_mul_cancel₀ hs0.ne']
  have hfz : f (t⁻¹ • y) = (t ^ 2)⁻¹ * f y := by
    simp only [hf, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have := hmin hz
  simp only [Set.mem_setOf_eq] at this
  rw [hfz, htt] at this
  have h2 := mul_le_mul_of_nonneg_left this hs0.le
  rw [← mul_assoc, mul_inv_cancel₀ hs0.ne', one_mul] at h2
  linarith [mul_comm s (f y0)]

end GlobalTheory.TPos

open GlobalTheory.TPos in

/- English proof (translation)
Introduce `F _ _ _ κ _ _ G hG`. Establish `hM : (G.map (Int.cast : ℤ → ℝ)).PosDef` using `hG.1`. Take `⟨c, hc, hcb⟩` from `posDef_lower _ hM`. Establish `key : ∀ (x : κ → F) v, (c / 2) * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)`. Introduce `x v`.

Rewrite using `[reAt_QF]`. Use `hcb (fun i => reAt v (x i))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hinj : ∀ (v : InfinitePlace F) (y : F), reAt v y = 0 → y = 0`. Introduce `v y h`.

Rewrite `h` using `[reAt_eq]`. Conclude with `(InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)).injective (by simpa using h)`. Use `⟨?_, ⟨c / 2, by positivity, key⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx v`. Take `⟨i, hi⟩` from `Function.ne_iff.mp hx`.

Establish `hyi : reAt v (x i) ≠ 0` using `fun h => hi (hinj v _ h)`. Establish `h1 : reAt v (x i) ^ 2 ≤ ∑ j, reAt v (x j) ^ 2` using `Finset.single_le_sum (f := fun j => reAt v (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `h2 : 0 < reAt v (x i) ^ 2` using `by positivity`. Establish `h3` using `mul_pos (half_pos hc) (lt_of_lt_of_le h2 h1)`. Use `key x v` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `a ξ`. Distinguish the cases in `ha : a = 0`. Apply `(Set.finite_singleton (0 : κ → F)).subset` to reduce the goal to its premises. Introduce and unpack `x ⟨hx, -⟩`.

Unfold `aL at hx`. Take `⟨z, -, rfl⟩` from `AddSubgroup.mem_map.mp hx`. Simplify using `[ha]`. Use `set B : ℝ := ∑ v : InfinitePlace F, Real.sqrt (reAt v ξ / (c / 2)) / v a with hB`. Use `set T : Set F := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B} with hT`.

Establish `hTf : T.Finite` using `NumberField.Embeddings.finite_of_norm_le F ℂ B`. Apply `((Set.Finite.pi (t := fun _ : κ => T) (fun _ => hTf)).image (fun z => a • z)).subset` to reduce the goal to its premises. Introduce and unpack `x ⟨hx, hxξ⟩`. Unfold `aL at hx`. Take `⟨z, hz, rfl⟩` from `AddSubgroup.mem_map.mp hx`.

Use `⟨z, fun i _ => ?_, rfl⟩` and prove the remaining obligations. Unfold `LL at hz`. Establish `hzi` using `(AddSubgroup.mem_pi _).mp hz i (Set.mem_univ _)`. Use `⟨hzi, fun φ => ?_⟩` and prove the remaining obligations. Rewrite using `[← NumberField.InfinitePlace.apply]`.

Use `set w := InfinitePlace.mk φ`. Establish `hxi : (DistribMulAction.toAddMonoidHom (κ → F) a z) i = a * z i` using `by simp`. Establish `hwa : 0 < w a` using `(InfinitePlace.pos_iff).mpr ha`. Establish `hk` using `key (DistribMulAction.toAddMonoidHom (κ → F) a z) w`. Rewrite `hk` using `[hxξ]`.

Establish `h1 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ ∑ j, reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2` using `Finset.single_le_sum (f := fun j => reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `h2 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ reAt w ξ / (c / 2)`. Rewrite using `[le_div_iff₀ (half_pos hc)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `Real.abs_le_sqrt h2`.

Rewrite `h3` using `[abs_reAt, hxi, map_mul]`. Establish `h4 : w (z i) ≤ Real.sqrt (reAt w ξ / (c / 2)) / w a`. Rewrite using `[le_div_iff₀ hwa]`. Combine the linear relations using `[mul_comm (w a) (w (z i))]`. Use `h4.trans ?_` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun v : InfinitePlace F => Real.sqrt (reAt v ξ / (c / 2)) / v a) (fun v _ => div_nonneg (Real.sqrt_nonneg _) (apply_nonneg v a)) (Finset.mem_univ w)`.
-/
theorem GlobalTheory.HilbertThetaSeries.qf_totPos_proper : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧
      ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  intro F _ _ _ κ _ _ G hG
  have hM : (G.map (Int.cast : ℤ → ℝ)).PosDef := hG.1
  obtain ⟨c, hc, hcb⟩ := posDef_lower _ hM
  have key : ∀ (x : κ → F) v, (c / 2) * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x) := by
    intro x v
    rw [reAt_QF]
    have := hcb (fun i => reAt v (x i))
    linarith
  have hinj : ∀ (v : InfinitePlace F) (y : F), reAt v y = 0 → y = 0 := by
    intro v y h
    rw [reAt_eq] at h
    exact (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)).injective (by simpa using h)
  refine ⟨?_, ⟨c / 2, by positivity, key⟩, ?_⟩
  · intro x hx v
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hyi : reAt v (x i) ≠ 0 := fun h => hi (hinj v _ h)
    have h1 : reAt v (x i) ^ 2 ≤ ∑ j, reAt v (x j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt v (x j) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : 0 < reAt v (x i) ^ 2 := by positivity
    have h3 := mul_pos (half_pos hc) (lt_of_lt_of_le h2 h1)
    have := key x v
    linarith
  · intro a ξ
    by_cases ha : a = 0
    · apply (Set.finite_singleton (0 : κ → F)).subset
      rintro x ⟨hx, -⟩
      unfold aL at hx
      obtain ⟨z, -, rfl⟩ := AddSubgroup.mem_map.mp hx
      simp [ha]
    set B : ℝ := ∑ v : InfinitePlace F, Real.sqrt (reAt v ξ / (c / 2)) / v a with hB
    set T : Set F := {y : F | IsIntegral ℤ y ∧ ∀ φ : F →+* ℂ, ‖φ y‖ ≤ B} with hT
    have hTf : T.Finite := NumberField.Embeddings.finite_of_norm_le F ℂ B
    apply ((Set.Finite.pi (t := fun _ : κ => T) (fun _ => hTf)).image (fun z => a • z)).subset
    rintro x ⟨hx, hxξ⟩
    unfold aL at hx
    obtain ⟨z, hz, rfl⟩ := AddSubgroup.mem_map.mp hx
    refine ⟨z, fun i _ => ?_, rfl⟩
    unfold LL at hz
    have hzi := (AddSubgroup.mem_pi _).mp hz i (Set.mem_univ _)
    refine ⟨hzi, fun φ => ?_⟩
    rw [← NumberField.InfinitePlace.apply]
    set w := InfinitePlace.mk φ
    have hxi : (DistribMulAction.toAddMonoidHom (κ → F) a z) i = a * z i := by simp
    have hwa : 0 < w a := (InfinitePlace.pos_iff).mpr ha
    have hk := key (DistribMulAction.toAddMonoidHom (κ → F) a z) w
    rw [hxξ] at hk
    have h1 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤
        ∑ j, reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2 :=
      Finset.single_le_sum (f := fun j => reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : reAt w ((DistribMulAction.toAddMonoidHom (κ → F) a z) i) ^ 2 ≤ reAt w ξ / (c / 2) := by
      rw [le_div_iff₀ (half_pos hc)]
      nlinarith
    have h3 := Real.abs_le_sqrt h2
    rw [abs_reAt, hxi, map_mul] at h3
    have h4 : w (z i) ≤ Real.sqrt (reAt w ξ / (c / 2)) / w a := by
      rw [le_div_iff₀ hwa]
      linarith [mul_comm (w a) (w (z i))]
    refine h4.trans ?_
    exact Finset.single_le_sum (f := fun v : InfinitePlace F => Real.sqrt (reAt v ξ / (c / 2)) / v a)
      (fun v _ => div_nonneg (Real.sqrt_nonneg _) (apply_nonneg v a)) (Finset.mem_univ w)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.qf_totPos_proper | exact GlobalTheory.HilbertThetaSeries.qf_totPos_proper | (intros; apply GlobalTheory.HilbertThetaSeries.qf_totPos_proper <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.evenPosGram_quadForm_totallyPositive_properness : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix κ κ ℤ), EvenPos G → (∀ x : κ → F, x ≠ 0 → TP (QF G x)) ∧ (∃ c : ℝ, 0 < c ∧ ∀ (x : κ → F) v, c * ∑ i, reAt v (x i) ^ 2 ≤ reAt v (QF G x)) ∧ ∀ (a ξ : F), {x : κ → F | x ∈ aL κ a ∧ QF G x = ξ}.Finite := by
  first | exact @GlobalTheory.HilbertThetaSeries.qf_totPos_proper | exact GlobalTheory.HilbertThetaSeries.qf_totPos_proper | (intros; apply GlobalTheory.HilbertThetaSeries.qf_totPos_proper <;> assumption)
