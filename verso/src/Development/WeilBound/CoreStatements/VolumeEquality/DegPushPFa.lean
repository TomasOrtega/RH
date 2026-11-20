import Development.WeilBound.CoreStatements.VolumeEquality.DegPushDefs
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg

noncomputable section

namespace SheetDecomposition.PF

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ b, Fintype (ι b)] {K' : Type} [Fintype K'] {ι' : K' → Type}
  [∀ b, Fintype (ι' b)]

/- English proof (translation)
Take `⟨i, hi⟩` from `h.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Rewrite using `[mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]`.
-/
theorem ne_of_arith {Ω : Type} [Field Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `: CharZero Ω` using `algebraRat.charZero Ω`. Take `rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra` from `Subsingleton.elim _ _`. Use `choose c hc using h1`. Establish `hF : fnField ℚ y ≤ IntermediateField.adjoin ℚ (coneRatios y c)`.

Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i⟩, ⟨k', j⟩, e, rfl⟩`. Take `rfl : k = k'` from `e`. Establish `: y ⟨k, i⟩ / y ⟨k, j⟩ = (y ⟨k, i⟩ / y ⟨k, c k⟩) / (y ⟨k, j⟩ / y ⟨k, c k⟩)`. Rewrite using `[div_div_div_cancel_right₀ (hc k)]`.

Rewrite using `[SetLike.mem_coe, this]`. Conclude with `div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, rfl⟩)`. Establish `hA : Algebra.IsAlgebraic (Algebra.adjoin ℚ (fnField ℚ y : Set Ω)) Ω`. Establish `e : Algebra.adjoin ℚ (fnField ℚ y : Set Ω) = (fnField ℚ y).toSubalgebra` using `Algebra.adjoin_eq (fnField ℚ y).toSubalgebra`. Rewrite using `[e]`.

Conclude with `inferInstanceAs (Algebra.IsAlgebraic (fnField ℚ y) Ω)`. Take `⟨t, ht, hb⟩` from `exists_isTranscendenceBasis_subset (R := ℚ) (fnField ℚ y : Set Ω)`. Establish `hc' : Cardinal.mk t = d` using `hb.cardinalMk_eq_trdeg.trans h3`. Take `⟨e⟩ : Nonempty (Fin d ≃ t)` from `Cardinal.eq.1 (by simp [hc'])`. Establish `hb'` using `hb.comp_equiv e`.

Use `hb'.isAlgebraic_field` as an intermediate fact. Conclude with `CoordConeArithVar.proof IntDomainDim.full K ι Ω y c d _ inferInstance hc hb'.1 (fun i => hF (ht (e i).2)) fun r _ => Algebra.IsAlgebraic.isAlgebraic r`.
-/
theorem arith_of_isPt [Nonempty K] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {y : (Σ b, ι b) → Ω} {d : ℕ} (h : IsPt ℚ y d) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  have : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : ‹Algebra ℚ Ω› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  choose c hc using h1
  have hF : fnField ℚ y ≤ IntermediateField.adjoin ℚ (coneRatios y c) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨⟨k, i⟩, ⟨k', j⟩, e, rfl⟩
    obtain rfl : k = k' := e
    have : y ⟨k, i⟩ / y ⟨k, j⟩ = (y ⟨k, i⟩ / y ⟨k, c k⟩) / (y ⟨k, j⟩ / y ⟨k, c k⟩) := by
      rw [div_div_div_cancel_right₀ (hc k)]
    rw [SetLike.mem_coe, this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨⟨k, i⟩, rfl⟩) (IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, rfl⟩)
  have hA : Algebra.IsAlgebraic (Algebra.adjoin ℚ (fnField ℚ y : Set Ω)) Ω := by
    have e : Algebra.adjoin ℚ (fnField ℚ y : Set Ω) = (fnField ℚ y).toSubalgebra := Algebra.adjoin_eq (fnField ℚ y).toSubalgebra
    rw [e]
    exact inferInstanceAs (Algebra.IsAlgebraic (fnField ℚ y) Ω)
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℚ) (fnField ℚ y : Set Ω)
  have hc' : Cardinal.mk t = d := hb.cardinalMk_eq_trdeg.trans h3
  obtain ⟨e⟩ : Nonempty (Fin d ≃ t) := Cardinal.eq.1 (by simp [hc'])
  have hb' := hb.comp_equiv e
  have := hb'.isAlgebraic_field
  exact CoordConeArithVar.proof IntDomainDim.full K ι Ω y c d _ inferInstance hc hb'.1 (fun i => hF (ht (e i).2))
    fun r _ => Algebra.IsAlgebraic.isAlgebraic r

/- English proof (translation)
Use `choose c hc using hne`. Establish `key : ∀ (g : MRing ι) (d : K → ℕ), IsMultiHomog g d → i (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) ∈ F`. Introduce `g d hg`. Establish `h1 : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g`. Establish `h` using `congrArg (eval fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap_of_isMultiHomog y hg)`.

Establish `h' : (eval fun k => (y ⟨k, c k⟩)⁻¹).comp (mConeMap y : MRing ι →+* MvPolynomial K Ω₁) = ((aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω₁) : MRing ι →+* Ω₁)`. Use `ringHom_ext (fun c => by simp) fun p => ?_` and prove the remaining obligations. Simplify using `[mConeMap, div_eq_mul_inv]`. Establish `h''` using `DFunLike.congr_fun h' g`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe] at h''`.

Rewrite using `[← h'', h, map_mul, eval_C]`. Simplify using `[div_eq_mul_inv]`. Rewrite using `[h1]`. Use `clear h1 hg`. Proceed by induction on `g using MvPolynomial.induction_on with`.

Consider the case `C a => simp`. Consider the case `add f g hf hg => simpa using add_mem hf hg`. Consider the case `mul_X f p hf => simpa using mul_mem hf (hF p.1 p.2 (c p.1))`. Take `⟨d, g, h, hg, hh, h0, e⟩` from `hb s`. Establish `hp : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`.

Establish `: s = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) / (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k)`. Rewrite using `[div_div_div_cancel_right₀ hp, e, mul_div_cancel_right₀ _ h0]`. Rewrite using `[this, map_div₀]`. Conclude with `div_mem (key g d hg) (key h d hh)`.
-/
theorem mem_of_birational {Ω₁ Ω : Type} [Field Ω₁] [Field Ω] (i : Ω₁ →+* Ω) {y : (Σ b, ι b) → Ω₁} (hb : Birational y)
    (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) (F : Subfield Ω) (hF : ∀ k j j', i (y ⟨k, j⟩) / i (y ⟨k, j'⟩) ∈ F) (s : Ω₁) : i s ∈ F := by
  choose c hc using hne
  have key : ∀ (g : MRing ι) (d : K → ℕ), IsMultiHomog g d → i (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) ∈ F := by
    intro g d hg
    have h1 : aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      have h := congrArg (eval fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap_of_isMultiHomog y hg)
      have h' : (eval fun k => (y ⟨k, c k⟩)⁻¹).comp (mConeMap y : MRing ι →+* MvPolynomial K Ω₁) =
          ((aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) : MRing ι →ₐ[ℤ] Ω₁) : MRing ι →+* Ω₁) := by
        refine ringHom_ext (fun c => by simp) fun p => ?_
        simp [mConeMap, div_eq_mul_inv]
      have h'' := DFunLike.congr_fun h' g
      simp only [RingHom.comp_apply, RingHom.coe_coe] at h''
      rw [← h'', h, map_mul, eval_C]
      simp [div_eq_mul_inv]
    rw [h1]
    clear h1 hg
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add f g hf hg => simpa using add_mem hf hg
    | mul_X f p hf => simpa using mul_mem hf (hF p.1 p.2 (c p.1))
  obtain ⟨d, g, h, hg, hh, h0, e⟩ := hb s
  have hp : ∏ k, y ⟨k, c k⟩ ^ d k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have : s = (aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k) / (aeval y h / ∏ k, y ⟨k, c k⟩ ^ d k) := by
    rw [div_div_div_cancel_right₀ hp, e, mul_div_cancel_right₀ _ h0]
  rw [this, map_div₀]
  exact div_mem (key g d hg) (key h d hh)

variable {Ω₁ : Type} [Field Ω₁] [Algebra ℚ Ω₁] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [Algebra Ω₁ Ω]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]`. Introduce and unpack `_ (⟨q, rfl⟩ | ⟨⟨k | k, j⟩, ⟨k', j'⟩, e, rfl⟩)`. Simplify using the standard rewrite rules. Take `rfl : Sum.inl k = k'` from `e`.

Conclude with `div_mem ((fnField Ω₁ y').algebraMap_mem _) ((fnField Ω₁ y').algebraMap_mem _)`. Take `rfl : Sum.inr k = k'` from `e`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, ⟨k, j'⟩, rfl, rfl⟩`. Rewrite using `[fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]`. Introduce and unpack `_ (⟨s, rfl⟩ | ⟨⟨k, j⟩, ⟨k', j'⟩, e, rfl⟩)`.

Use `mem_of_birational _ hb hne _ (fun k j j' => ?_) s` and prove the remaining obligations. Conclude with `IntermediateField.subset_adjoin ℚ _ ⟨⟨.inl k, j⟩, ⟨.inl k, j'⟩, rfl, rfl⟩`. Take `rfl : k = k'` from `e`. Conclude with `IntermediateField.subset_adjoin _ _ ⟨⟨.inr k, j⟩, ⟨.inr k, j'⟩, rfl, rfl⟩`.
-/
theorem fnField_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield = (fnField Ω₁ y').toSubfield := by
  apply le_antisymm
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨q, rfl⟩ | ⟨⟨k | k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · simp
    · obtain rfl : Sum.inl k = k' := e
      exact div_mem ((fnField Ω₁ y').algebraMap_mem _) ((fnField Ω₁ y').algebraMap_mem _)
    · obtain rfl : Sum.inr k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, j⟩, ⟨k, j'⟩, rfl, rfl⟩
  · rw [fnField, IntermediateField.adjoin_toSubfield, Subfield.closure_le]
    rintro _ (⟨s, rfl⟩ | ⟨⟨k, j⟩, ⟨k', j'⟩, e, rfl⟩)
    · refine mem_of_birational _ hb hne _ (fun k j j' => ?_) s
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨.inl k, j⟩, ⟨.inl k, j'⟩, rfl, rfl⟩
    · obtain rfl : k = k' := e
      exact IntermediateField.subset_adjoin _ _ ⟨⟨.inr k, j⟩, ⟨.inr k, j'⟩, rfl, rfl⟩

/- English proof (translation)
Use `show Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield Ω = Module.finrank (fnField Ω₁ y').toSubfield Ω`. Rewrite using `[fnField_join y' hb hne]`.
-/
theorem finrank_join {y : (Σ b, ι b) → Ω₁} (y' : (Σ b, ι' b) → Ω) (hb : Birational y) (hne : ∀ k, ∃ j, y ⟨k, j⟩ ≠ 0) :
    Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')) Ω = Module.finrank (fnField Ω₁ y') Ω := by
  show Module.finrank (fnField ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y')).toSubfield Ω =
    Module.finrank (fnField Ω₁ y').toSubfield Ω
  rw [fnField_join y' hb hne]

/- English proof (translation)
Establish `hne` using `ne_of_arith ha`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(k | k)`. Take `⟨j, hj⟩` from `hne k`. Conclude with `⟨j, (map_ne_zero (algebraMap Ω₁ Ω)).2 hj⟩`.

Conclude with `h.1 k`. Use `h.2.1` as an intermediate fact. Conclude with `Module.finite_of_finrank_pos (by rw [finrank_join y' hb hne]; exact Module.finrank_pos)`. Establish `h1` using `FnFieldTrdeg.full K ι Ω₁ y n hb ha`. Establish `: CharZero Ω₁` using `algebraRat.charZero Ω₁`.

Establish `: IsScalarTower ℤ ℚ Ω₁` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `: IsScalarTower ℚ Ω₁ Ω` using `IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)`. Establish `h2` using `trdeg_add_eq ℤ ℚ (A := Ω₁)`. Rewrite `h2` using `[trdeg_eq_zero, zero_add, h1]`.

Rewrite using `[← trdeg_add_eq ℚ Ω₁ (A := Ω), h2, h.2.2, Nat.cast_add]`.
-/
theorem isPt_join {y : (Σ b, ι b) → Ω₁} {y' : (Σ b, ι' b) → Ω} {n r : ℕ} (hb : Birational y)
    (ha : IsArithVar (mCoordIdeal y) (n + 1)) (h : IsPt Ω₁ y' r) :
    IsPt ℚ (joinPt (fun x => algebraMap Ω₁ Ω (y x)) y') (n + r) := by
  have hne := ne_of_arith ha
  refine ⟨?_, ?_, ?_⟩
  · rintro (k | k)
    · obtain ⟨j, hj⟩ := hne k
      exact ⟨j, (map_ne_zero (algebraMap Ω₁ Ω)).2 hj⟩
    · exact h.1 k
  · have := h.2.1
    exact Module.finite_of_finrank_pos (by rw [finrank_join y' hb hne]; exact Module.finrank_pos)
  · have h1 := FnFieldTrdeg.full K ι Ω₁ y n hb ha
    have : CharZero Ω₁ := algebraRat.charZero Ω₁
    have : IsScalarTower ℤ ℚ Ω₁ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : IsScalarTower ℚ Ω₁ Ω := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
    have h2 := trdeg_add_eq ℤ ℚ (A := Ω₁)
    rw [trdeg_eq_zero, zero_add, h1] at h2
    rw [← trdeg_add_eq ℚ Ω₁ (A := Ω), h2, h.2.2, Nat.cast_add]

end SheetDecomposition.PF
