import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.FibreNormCharpolyFalse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial

noncomputable section

namespace PullFormsGeneric

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]`. Conclude with `intCast_mem F a`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `add_mem hp hq`.

Consider the case `mul_X p q hp => rw [map_mul, aeval_X]`. Conclude with `mul_mem hp (hw q)`.
-/
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)

omit [CharZero Ω] in

/- English proof (translation)
Establish `h` using `congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)`. Rewrite `h` using `[map_mul, eval_C, map_prod]`. Simplify using `only [map_pow, eval_X] at h`. Rewrite using `[← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]`. Use `congr 1`.

Conclude with `RingHom.ext_int _ _`. Use function extensionality and compare the values at `p`. Simplify using the standard rewrite rules.
-/
theorem aeval_scale {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (y : (Σ k, ι k) → Ω) (t : K → Ω) :
    aeval (fun p => y p * t p.1) g = aeval y g * ∏ k, t k ^ d k := by
  have h := congrArg (MvPolynomial.eval t) (ProjLine.mConeMap_eq_of_isMultiHomog y hg)
  rw [map_mul, eval_C, map_prod] at h
  simp only [map_pow, eval_X] at h
  rw [← h, mConeMap, aeval_def, aeval_def, eval₂_comp_left]
  congr 1
  · exact RingHom.ext_int _ _
  · funext p
    simp

/- English proof (translation)
Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Take `⟨d, g, h, hg, hh, hh0, hgh⟩` from `hB x`. Use `set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹`. Establish `ht : ∏ k, t k ^ d k ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))`. Establish `hw : ∀ p, y p * t p.1 ∈ blockFnField y` using `fun p => IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩`.

Establish `hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h`. Rewrite using `[aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]`. Rewrite using `[hx]`. Conclude with `div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)`.
-/
theorem blockFnField_eq_top {y : (Σ k, ι k) → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hB : Birational y) : blockFnField y = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB x
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
  have hw : ∀ p, y p * t p.1 ∈ blockFnField y := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, by simp [t, div_eq_mul_inv]⟩
  have hx : x = aeval (fun p => y p * t p.1) g / aeval (fun p => y p * t p.1) h := by
    rw [aeval_scale hg, aeval_scale hh, hgh, mul_div_mul_right _ _ ht, mul_div_cancel_right₀ _ hh0]
  rw [hx]
  exact div_mem (aeval_mem _ _ hw g) (aeval_mem _ _ hw h)

/- English proof (translation)
Take `⟨_, ⟨_, _, hrel⟩, _, hdim⟩` from `hA`. Take `⟨c, hc⟩` from `CoordArithOfFnField.nonzero_of_relevant y hrel`. Rewrite `hdim` using `[CoordArithOfFnField.dim_eq y c hc]`. Establish `h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D`. Generalize the expression as in `(Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢`.

Proceed by induction on `n using ENat.recTopCoe with`. Consider the case `top`. It suffices to derive a contradiction. Simplify using `only [top_add] at hdim`. Normalize the coercions in `at hdim`.

Consider the case `coe n`. Normalize the coercions in `at hdim ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[Cardinal.toENat_eq_natCast]`. Establish `hE : blockFnField y ≃ₐ[ℤ] Ω` using `((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv`.

Establish `h2 : Algebra.trdeg ℤ Ω = D` using `by rw [← hE.trdeg_eq]; convert h1`. Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)`. Rewrite using `[← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]`.
-/
theorem trdeg_eq {y : (Σ k, ι k) → Ω} {D : ℕ} (hA : IsArithVar (mCoordIdeal y) (D + 1))
    (hB : Birational y) : Algebra.trdeg ℚ Ω = D := by
  obtain ⟨_, ⟨_, _, hrel⟩, _, hdim⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = D := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have hE : blockFnField y ≃ₐ[ℤ] Ω :=
    ((IntermediateField.equivOfEq (blockFnField_eq_top c hc hB)).trans
      IntermediateField.topEquiv).toRingEquiv.toIntAlgEquiv
  have h2 : Algebra.trdeg ℤ Ω = D := by rw [← hE.trdeg_eq]; convert h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h2, ← trdeg_add_eq ℤ ℚ (A := Ω), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]

omit [CharZero Ω] in

/- English proof (translation)
Establish `hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y` using `fun h => (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)`. Take `⟨z, hzP, -⟩` from `exists_mcPts_not_mem_mcPts hA hne`. Take `⟨j, hj⟩` from `hz z hzP`. Use `⟨j, fun h0 => hj (hzP.2 _ ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mConeMap y (L j) = 0`.

Rewrite using `[ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]`.
-/
theorem exists_ne_zero {y : (Σ k, ι k) → Ω} {D : ℕ} {e : K → ℕ} {L : Fin (D + 1) → MRing ι}
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hL : ∀ j, IsMultiHomog (L j) e)
    (hz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) :
    ∃ j, aeval y (L j) ≠ 0 := by
  have hne : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    (RingHom.ker_isPrime (mConeMap y)).ne_top (top_le_iff.mp h)
  obtain ⟨z, hzP, -⟩ := exists_mcPts_not_mem_mcPts hA hne
  obtain ⟨j, hj⟩ := hz z hzP
  refine ⟨j, fun h0 => hj (hzP.2 _ ?_)⟩
  change mConeMap y (L j) = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y (hL j), h0, map_zero, zero_mul]

def dehom {D : ℕ} (j₀ : Fin (D + 1)) (F : MvPolynomial (Fin (D + 1)) ℚ) : MvPolynomial {i // i ≠ j₀} ℚ :=
  bind₁ (fun i => if h : i = j₀ then 1 else X ⟨i, h⟩) F

omit [Field Ω] [CharZero Ω] in
/- English proof (translation)
Rewrite using `[dehom, aeval_bind₁]`. Use `congrArg (fun f => aeval f F) (funext fun i => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℚ A] {D : ℕ} (j₀ : Fin (D + 1))
    (F : MvPolynomial (Fin (D + 1)) ℚ) (u : {i // i ≠ j₀} → A) :
    aeval u (dehom j₀ F) = aeval (fun i => if h : i = j₀ then 1 else u ⟨i, h⟩) F := by
  rw [dehom, aeval_bind₁]
  refine congrArg (fun f => aeval f F) (funext fun i => ?_)
  split_ifs <;> simp

end PullFormsGeneric

open PullFormsGeneric in

/- English proof (translation)
Introduce `K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0`. Take `⟨j₀, hj₀⟩` from `exists_ne_zero hA hL hz`. Use `set a := aeval y (L j₀)`. Use `set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a`. Establish `hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r)`.

Establish `hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r)`. Introduce `i`. Distinguish the cases in `h : i = j₀`. Substitute `h` using the available equality. Rewrite using `[div_self hj₀]`.

Conclude with `one_mem _`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[pullField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, j, hj, rfl⟩`.

Rewrite using `[← div_div_div_cancel_right₀ hj₀]`. Conclude with `div_mem (hw i) (hw j)`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩`.

Take `⟨_, ⟨_, _, hrel⟩, _, _⟩` from `hA`. Take `⟨c, hc⟩` from `CoordArithOfFnField.nonzero_of_relevant y hrel`. Establish `hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => ⟨c k, hc k⟩`. Establish `halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω`. Use `⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩` and prove the remaining obligations.

Establish `hle : blockFnField y ≤ (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ`. Rewrite using `[blockFnField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨p, q, hpq, rfl⟩`. Use `(IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)` and prove the remaining obligations. Use `hR K ι Ω y D e L hrel' he hL hz p q hpq` as an intermediate fact.

Rewrite `this` using `[hP]`. Then use the resulting hypothesis. Establish `hx` using `hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)`. Conclude with `mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)`. Establish `hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω`. Rewrite using `[trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]`.

Use `norm_cast`. Simplify using `[Fintype.card_subtype_compl]`. Establish `hind : AlgebraicIndependent ℚ r` using `(Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1`. Establish `hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a`. Use function extensionality and compare the values at `i`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `(div_self hj₀).symm`. Both sides reduce to the same expression. Establish `hr0 : aeval r (dehom j₀ F) = 0`.

Rewrite using `[aeval_dehom, hw]`. Establish `h1` using `FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)`. Simplify using `only [mul_div_cancel₀ _ hj₀] at h1`. Rewrite `h1` using `[h0]`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)`.

Establish `hG : dehom j₀ F = 0` using `hind.eq_zero_of_aeval_eq_zero _ hr0`. Establish `hFX : F * X j₀ = 0`. Use `MvPolynomial.funext fun x => ?_` and prove the remaining obligations. Rewrite using `[map_mul, eval_X, map_zero]`. Distinguish the cases in `hx : x j₀ = 0`.

Rewrite using `[hx, mul_zero]`. Establish `h1` using `FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)`. Establish `h2` using `aeval_dehom j₀ F (fun i => x i.1 / x j₀)`. Establish `hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀`. Use function extensionality and compare the values at `i`.

Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `(div_self hx).symm`. Both sides reduce to the same expression. Rewrite `h2` using `[hG, map_zero, hw']`.

Establish `e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F`. Establish `hs : (fun j => x j₀ * (x j / x j₀)) = x` using `funext fun j => mul_div_cancel₀ _ hx`. Rewrite `h1` using `[hs]`. Rewrite using `[← coe_aeval_eq_eval, ← coe_aeval_eq_eval]`. Conclude with `h1`.

Establish `e2 : eval (fun i => x i / x j₀) F = 0`. Rewrite using `[← coe_aeval_eq_eval]`. Conclude with `h2.symm`. Rewrite using `[e1, e2, mul_zero, zero_mul]`. Conclude with `(mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)`.
-/
theorem PullFormsGeneric.proof (hR : PullRatiosAlgebraic.Statement) : PullFormsGeneric.Statement := by
  intro K _ ι _ Ω _ _ y D e L hA hB he hL hz d F hF h0
  classical
  obtain ⟨j₀, hj₀⟩ := exists_ne_zero hA hL hz
  set a := aeval y (L j₀)
  set r : {i // i ≠ j₀} → Ω := fun i => aeval y (L i.1) / a

  have hP : pullField y L = IntermediateField.adjoin ℚ (Set.range r) := by
    have hw : ∀ i, aeval y (L i) / a ∈ IntermediateField.adjoin ℚ (Set.range r) := by
      intro i
      by_cases h : i = j₀
      · subst h; rw [div_self hj₀]; exact one_mem _
      · exact IntermediateField.subset_adjoin _ _ ⟨⟨i, h⟩, rfl⟩
    apply le_antisymm
    · rw [pullField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, j, hj, rfl⟩
      rw [← div_div_div_cancel_right₀ hj₀]
      exact div_mem (hw i) (hw j)
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin _ _ ⟨i.1, j₀, hj₀, rfl⟩

  obtain ⟨_, ⟨_, _, hrel⟩, _, _⟩ := hA
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hrel
  have hrel' : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => ⟨c k, hc k⟩
  have halg : Algebra.IsAlgebraic (Algebra.adjoin ℚ (Set.range r)) Ω := by
    refine ⟨fun x => IntermediateField.isAlgebraic_adjoin_iff.mp ?_⟩
    have hle : blockFnField y ≤
        (algebraicClosure (IntermediateField.adjoin ℚ (Set.range r)) Ω).restrictScalars ℚ := by
      rw [blockFnField, IntermediateField.adjoin_le_iff]
      rintro _ ⟨p, q, hpq, rfl⟩
      refine (IntermediateField.mem_restrictScalars _).mpr (mem_algebraicClosure_iff.mpr ?_)
      have := hR K ι Ω y D e L hrel' he hL hz p q hpq
      rwa [hP] at this
    have hx := hle ((blockFnField_eq_top c hc hB).symm ▸ IntermediateField.mem_top : x ∈ blockFnField y)
    exact mem_algebraicClosure_iff.mp ((IntermediateField.mem_restrictScalars _).mp hx)

  have hcard : Cardinal.mk {i : Fin (D + 1) // i ≠ j₀} ≤ Algebra.trdeg ℚ Ω := by
    rw [trdeg_eq ⟨‹_›, ⟨‹_›, ‹_›, hrel⟩, ‹_›, ‹_›⟩ hB, Cardinal.mk_fintype]
    norm_cast
    simp [Fintype.card_subtype_compl]
  have hind : AlgebraicIndependent ℚ r :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℚ r hcard).1

  have hw : (fun i => if h : i = j₀ then (1 : Ω) else r ⟨i, h⟩) = fun i => aeval y (L i) / a := by
    funext i
    split_ifs with h
    · subst h; exact (div_self hj₀).symm
    · rfl
  have hr0 : aeval r (dehom j₀ F) = 0 := by
    rw [aeval_dehom, hw]
    have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous hF a (fun i => aeval y (L i) / a)
    simp only [mul_div_cancel₀ _ hj₀] at h1
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (pow_ne_zero _ hj₀)
  have hG : dehom j₀ F = 0 := hind.eq_zero_of_aeval_eq_zero _ hr0

  have hFX : F * X j₀ = 0 := by
    refine MvPolynomial.funext fun x => ?_
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x j₀ = 0
    · rw [hx, mul_zero]
    · have h1 := FibreNormCharpoly.aeval_mul_of_isHomogeneous (Ω := ℚ) hF (x j₀) (fun i => x i / x j₀)
      have h2 := aeval_dehom j₀ F (fun i => x i.1 / x j₀)
      have hw' : (fun i => if h : i = j₀ then (1 : ℚ) else x i / x j₀) = fun i => x i / x j₀ := by
        funext i
        split_ifs with h
        · subst h; exact (div_self hx).symm
        · rfl
      rw [hG, map_zero, hw'] at h2
      have e1 : eval x F = x j₀ ^ d * eval (fun i => x i / x j₀) F := by
        have hs : (fun j => x j₀ * (x j / x j₀)) = x := funext fun j => mul_div_cancel₀ _ hx
        rw [hs] at h1
        rw [← coe_aeval_eq_eval, ← coe_aeval_eq_eval]
        exact h1
      have e2 : eval (fun i => x i / x j₀) F = 0 := by
        rw [← coe_aeval_eq_eval]
        exact h2.symm
      rw [e1, e2, mul_zero, zero_mul]
  exact (mul_eq_zero.mp hFX).resolve_right (X_ne_zero _)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
