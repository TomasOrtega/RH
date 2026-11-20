import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocRankFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSemilocFinite
import GroundTheory.HeightsAndTheta.Heights.Intersections.StRankFracDegree
import GroundTheory.HeightsAndTheta.Heights.Intersections.StSemilocChartRatio
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace SemilocRankFrac

section Scale

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `conv_lhs => rw [u.as_sum]`. Use `conv_rhs => rw [u.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, mul_assoc]`.

Use `congr 1`. Simplify using `only [mul_pow]`. Rewrite using `[Finsupp.prod_mul]`. Use `congr 1`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show ∏ i, c k ^ m ⟨k, i⟩ = _`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hu m hm k]`.
-/
theorem aeval_scale (y : (Σ k, ι k) → Ω) (c : K → Ω) {u : MRing ι} {a : K → ℕ} (hu : IsMultiHomog u a) :
    aeval (fun p => y p * c p.1) u = aeval y u * ∏ k, c k ^ a k := by
  conv_lhs => rw [u.as_sum]
  conv_rhs => rw [u.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  simp only [mul_pow]
  rw [Finsupp.prod_mul]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  show ∏ i, c k ^ m ⟨k, i⟩ = _
  rw [Finset.prod_pow_eq_pow_sum, hu m hm k]

/- English proof (translation)
Rewrite using `[aeval_scale y c hu, aeval_scale y c hw, mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]`.
-/
theorem aeval_scale_div (y : (Σ k, ι k) → Ω) {c : K → Ω} (hc : ∀ k, c k ≠ 0) {u w : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) :
    aeval (fun p => y p * c p.1) u / aeval (fun p => y p * c p.1) w = aeval y u / aeval y w := by
  rw [aeval_scale y c hu, aeval_scale y c hw,
    mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]

/- English proof (translation)
Proceed by induction on `u using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, algebraMap_int_eq, eq_intCast]`. Conclude with `intCast_mem _ a`. Consider the case `add f g hf hg`.

Rewrite using `[map_add]`. Conclude with `add_mem hf hg`. Consider the case `mul_X f p hf`. Rewrite using `[map_mul, aeval_X]`. Conclude with `mul_mem hf (hy p)`.
-/
theorem aeval_mem [Algebra ℚ Ω] (L : IntermediateField ℚ Ω) {y : (Σ k, ι k) → Ω} (hy : ∀ p, y p ∈ L)
    (u : MRing ι) : aeval y u ∈ L := by
  induction u using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, algebraMap_int_eq, eq_intCast]
    exact intCast_mem _ a
  | add f g hf hg =>
    rw [map_add]
    exact add_mem hf hg
  | mul_X f p hf =>
    rw [map_mul, aeval_X]
    exact mul_mem hf (hy p)

end Scale

section Eval

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  (x' : (Σ k, ι' k) → Ω) (P' : Ideal (MRing ι')) [P'.IsPrime]
  (h : RingHom.ker (aeval x' : MRing ι' →ₐ[ℤ] Ω) = P')

def quotEval : MRing ι' ⧸ P' →+* Ω :=
  Ideal.Quotient.lift P' (aeval x' : MRing ι' →ₐ[ℤ] Ω).toRingHom fun f hf => by
    rw [← h] at hf
    exact RingHom.mem_ker.1 hf

/- English proof (translation)
The claim follows from `(Ideal.injective_lift_iff _).2 h`.
-/
theorem quotEval_injective : Function.Injective (quotEval x' P' h) :=
  (Ideal.injective_lift_iff _).2 h

def fracEval : FractionRing (MRing ι' ⧸ P') →+* Ω :=
  IsFractionRing.lift (quotEval_injective x' P' h)

/- English proof (translation)
Rewrite using `[fracEval, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem fracEval_algebraMap (f : MRing ι') :
    fracEval x' P' h (algebraMap _ _ (Ideal.Quotient.mk P' f)) = aeval x' f := by
  rw [fracEval, IsFractionRing.lift_algebraMap]
  rfl

end Eval

end SemilocRankFrac

open SemilocRankFrac in

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' _ hQ hs hsQ hW hi'`. Use `hP'.2.1.1` as an intermediate fact. Use `imageZ_isPrime_of_prime v P'` as an intermediate fact. Set `_` to `(locToSemiloc hv P' W).toAlgebra`. Establish `hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0` using `fun k' h0 => hi' k' (by rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X, h0])`.

Establish `hch : ∀ {a b : K'}, a = b → G.x' ⟨a, i' a⟩ = G.x' ⟨b, i' b⟩`. Introduce and unpack `a b rfl`. Both sides reduce to the same expression. Set `ψ` to `fracEval G.x' P' G.genericFibre_ker_target`. Set `y' : (Σ k', ι' k') → G.Φ'` to `fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩`.

Set `L₀` to `IntermediateField.adjoin ℚ (Set.range (y' ∘ v))`. Set `L` to `IntermediateField.adjoin ℚ (Set.range y')`. Establish `hx' : G.x' = fun q => y' q * G.x' ⟨q.1, i' q.1⟩` using `funext fun q => (div_mul_cancel₀ _ (hx q.1)).symm`. Establish `hxv : G.x' ∘ v = fun p => (y' ∘ v) p * G.x' ⟨κ p.1, i' (κ p.1)⟩` using `funext fun p => by show G.x' (v p) = G.x' (v p) / G.x' ⟨(v p).1, i' (v p).1⟩ * G.x' ⟨κ p.1, i' (κ p.1)⟩`. Rewrite using `[hch (hv.2.2.1 p), div_mul_cancel₀ _ (hx _)]`.

Establish `hψ : ∀ u w : MRing ι', (hw : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P')) → ψ (IsLocalization.mk' _ (Ideal.Quotient.mk P' u) ⟨_, hw⟩) = aeval G.x' u / aeval G.x' w` using `fun u w hw => by`. Rewrite using `[IsFractionRing.mk'_eq_div, map_div₀, fracEval_algebraMap, fracEval_algebraMap]`. Set `f` to `ψ.comp ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype)`. Set `g` to `ψ.comp (semiLocRing P' (fibreOver v P' W)).subtype`. Establish `hf : ∀ u w : MRing ι, (hw : Ideal.Quotient.mk (imageZ v P') w ∈ nonZeroDivisors (MRing ι ⧸ imageZ v P')) → ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ u) ⟨_, hw⟩)) = aeval (G.x' ∘ v) u / aeval (G.x' ∘ v) w` using `fun u w hw => by`.

Rewrite using `[IsFractionRing.mk'_eq_div, map_div₀, map_div₀, fracMapZ_algebraMap, fracMapZ_algebraMap, fracEval_algebraMap, fracEval_algebraMap, aeval_rename, aeval_rename]`. Establish `hfL : ∀ a, f a ∈ L₀`. Establish `hle : locRing (imageZ v P') W ≤ (L₀.toSubalgebra.toSubring.comap ψ).comap (fracMapZ v P')`. Rewrite using `[locRing, Subring.closure_le]`. Introduce and unpack `_ ⟨u, w, a, hw, -, hu, hwa, rfl⟩`.

Use `show ψ (fracMapZ v P' _) ∈ L₀`. Rewrite using `[hf, hxv, aeval_scale_div _ (fun k => hx _) hu hwa]`. Conclude with `div_mem (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) u) (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) w)`. Conclude with `fun a => hle a.2`. Establish `hgL : ∀ b, g b ∈ L`.

Establish `hle : semiLocRing P' (fibreOver v P' W) ≤ L.toSubalgebra.toSubring.comap ψ`. Rewrite using `[semiLocRing, Subring.closure_le]`. Introduce and unpack `_ ⟨u, w, a, hw, -, hu, hwa, rfl⟩`. Use `show ψ _ ∈ L`. Establish `e` using `aeval_scale_div y' hx hu hwa`.

Rewrite `e` using `[← hx']`. Rewrite using `[hψ, e]`. Conclude with `div_mem (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) u) (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) w)`. Conclude with `fun b => hle b.2`. Establish `hgen : ∀ (T : Set G.Φ') (S : Subfield G.Φ'), T ⊆ S → (IntermediateField.adjoin ℚ T).toSubfield ≤ S` using `fun T S hT z hz => (IntermediateField.adjoin_le_iff (F := ℚ) (T := S.toIntermediateField fun r => by`.

Rewrite using `[eq_ratCast]`. Conclude with `SubfieldClass.ratCast_mem S r)).2 hT hz`. Establish `hL₀ : L₀.toSubfield ≤ Subfield.closure (Set.range f)`. Use `hgen _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`.

Take `⟨j, hj⟩` from `hW.2 k`. Take `⟨⟨k0, i0⟩, hp0⟩` from `hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩`. Take `rfl : k0 = k` from `hv.1 ((hv.2.2.1 ⟨k0, i0⟩).symm.trans (congrArg Sigma.fst hp0))`. Establish `hjQ : (X ⟨k0, j⟩ : MRing ι) ∉ imageZ v P'` using `fun h0 => hj (hW.1.1.2 (Ideal.mem_sup_left h0))`. Establish `hw : Ideal.Quotient.mk (imageZ v P') (X ⟨k0, j⟩) ∈ nonZeroDivisors _` using `mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])`.

Establish `hx0 : G.x' (v ⟨k0, j⟩) ≠ 0` using `fun h0 => hjQ (by`. Rewrite using `[imageZ, Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker]`. Simplify `h0)` using `[aeval_rename]`. Establish `mem : ∀ i₁ : ι k0, IsLocalization.mk' (FractionRing (MRing ι ⧸ imageZ v P')) (Ideal.Quotient.mk _ (X ⟨k0, i₁⟩)) ⟨_, hw⟩ ∈ locRing (imageZ v P') W` using `fun i₁ => Subring.subset_closure ⟨_, _, Pi.single k0 1, hw, hj, AvoidRing.isMultiHomog_X k0 i₁, AvoidRing.isMultiHomog_X k0 j, rfl⟩`. Establish `e : (y' ∘ v) ⟨k0, i⟩ = f ⟨_, mem i⟩ / f ⟨_, mem i0⟩` using `by show G.x' (v ⟨k0, i⟩) / G.x' ⟨(v ⟨k0, i⟩).1, i' (v ⟨k0, i⟩).1⟩ = ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i⟩)) ⟨_, hw⟩)) / ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i0⟩)) ⟨_, hw⟩))`.

Rewrite using `[hf, hf, hch (hv.2.2.1 _)]`. Simplify using `only [aeval_X, Function.comp, hp0]`. Rewrite using `[div_div_div_cancel_right₀ hx0]`. Rewrite using `[e]`. Conclude with `div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)`.

Establish `hL : L.toSubfield ≤ Subfield.closure (Set.range g)`. Use `hgen _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Take `⟨b, b', hb', e⟩` from `hC K ι K' ι' κ v P' n s α W i' hv hP' hQ hs hsQ hW hi' q`. Establish `e'` using `congrArg ψ e`.

Rewrite `e'` using `[map_mul, map_mul, fracEval_algebraMap, fracEval_algebraMap, aeval_X, aeval_X]`. Establish `hψb' : g b' ≠ 0` using `(map_ne_zero ψ).2 hb'`. Establish `: y' q = g b / g b'`. Rewrite using `[div_eq_div_iff (hx _) hψb']`. Use `show G.x' q * ψ b' = ψ b * G.x' ⟨q.1, i' q.1⟩`.

Rewrite using `[e']`. Conclude with `mul_comm _ _`. Rewrite using `[this]`. Conclude with `div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)`. Conclude with `hR ℚ G.Φ' _ _ L₀ L f g (ψ.injective.comp ((fracMapZ v P').injective.comp Subtype.val_injective)) (ψ.injective.comp Subtype.val_injective) (fun _ => rfl) hfL hgL hL₀ hL (hF K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW).1`.
-/
theorem SemilocRankFrac.proof (hR : RankFracDegree.Statement) (hF : SemilocFinite.Statement)
    (hC : SemilocChartRatio.Statement) : SemilocRankFrac.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n G s α W i' hv hP' _ hQ hs hsQ hW hi'
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  let _ := (locToSemiloc hv P' W).toAlgebra
  have hx : ∀ k', G.x' ⟨k', i' k'⟩ ≠ 0 := fun k' h0 =>
    hi' k' (by rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X, h0])
  have hch : ∀ {a b : K'}, a = b → G.x' ⟨a, i' a⟩ = G.x' ⟨b, i' b⟩ := by
    rintro a b rfl
    rfl
  let ψ := fracEval G.x' P' G.genericFibre_ker_target
  let y' : (Σ k', ι' k') → G.Φ' := fun q => G.x' q / G.x' ⟨q.1, i' q.1⟩
  let L₀ := IntermediateField.adjoin ℚ (Set.range (y' ∘ v))
  let L := IntermediateField.adjoin ℚ (Set.range y')
  have hx' : G.x' = fun q => y' q * G.x' ⟨q.1, i' q.1⟩ := funext fun q => (div_mul_cancel₀ _ (hx q.1)).symm
  have hxv : G.x' ∘ v = fun p => (y' ∘ v) p * G.x' ⟨κ p.1, i' (κ p.1)⟩ := funext fun p => by
    show G.x' (v p) = G.x' (v p) / G.x' ⟨(v p).1, i' (v p).1⟩ * G.x' ⟨κ p.1, i' (κ p.1)⟩
    rw [hch (hv.2.2.1 p), div_mul_cancel₀ _ (hx _)]
  have hψ : ∀ u w : MRing ι', (hw : Ideal.Quotient.mk P' w ∈ nonZeroDivisors (MRing ι' ⧸ P')) →
      ψ (IsLocalization.mk' _ (Ideal.Quotient.mk P' u) ⟨_, hw⟩) = aeval G.x' u / aeval G.x' w := fun u w hw => by
    rw [IsFractionRing.mk'_eq_div, map_div₀, fracEval_algebraMap, fracEval_algebraMap]
  let f := ψ.comp ((fracMapZ v P').comp (locRing (imageZ v P') W).subtype)
  let g := ψ.comp (semiLocRing P' (fibreOver v P' W)).subtype
  have hf : ∀ u w : MRing ι, (hw : Ideal.Quotient.mk (imageZ v P') w ∈ nonZeroDivisors (MRing ι ⧸ imageZ v P')) →
      ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ u) ⟨_, hw⟩)) =
        aeval (G.x' ∘ v) u / aeval (G.x' ∘ v) w := fun u w hw => by
    rw [IsFractionRing.mk'_eq_div, map_div₀, map_div₀, fracMapZ_algebraMap, fracMapZ_algebraMap,
      fracEval_algebraMap, fracEval_algebraMap, aeval_rename, aeval_rename]

  have hfL : ∀ a, f a ∈ L₀ := by
    have hle : locRing (imageZ v P') W ≤ (L₀.toSubalgebra.toSubring.comap ψ).comap (fracMapZ v P') := by
      rw [locRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
      show ψ (fracMapZ v P' _) ∈ L₀
      rw [hf, hxv, aeval_scale_div _ (fun k => hx _) hu hwa]
      exact div_mem (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) u)
        (aeval_mem L₀ (fun p => IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩) w)
    exact fun a => hle a.2
  have hgL : ∀ b, g b ∈ L := by
    have hle : semiLocRing P' (fibreOver v P' W) ≤ L.toSubalgebra.toSubring.comap ψ := by
      rw [semiLocRing, Subring.closure_le]
      rintro _ ⟨u, w, a, hw, -, hu, hwa, rfl⟩
      show ψ _ ∈ L
      have e := aeval_scale_div y' hx hu hwa
      rw [← hx'] at e
      rw [hψ, e]
      exact div_mem (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) u)
        (aeval_mem L (fun q => IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩) w)
    exact fun b => hle b.2

  have hgen : ∀ (T : Set G.Φ') (S : Subfield G.Φ'), T ⊆ S →
      (IntermediateField.adjoin ℚ T).toSubfield ≤ S := fun T S hT z hz =>
    (IntermediateField.adjoin_le_iff (F := ℚ) (T := S.toIntermediateField fun r => by
      rw [eq_ratCast]; exact SubfieldClass.ratCast_mem S r)).2 hT hz
  have hL₀ : L₀.toSubfield ≤ Subfield.closure (Set.range f) := by
    refine hgen _ _ ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    obtain ⟨j, hj⟩ := hW.2 k
    obtain ⟨⟨k0, i0⟩, hp0⟩ := hv.2.2.2 ⟨κ k, i' (κ k)⟩ ⟨k, rfl⟩
    obtain rfl : k0 = k := hv.1 ((hv.2.2.1 ⟨k0, i0⟩).symm.trans (congrArg Sigma.fst hp0))
    have hjQ : (X ⟨k0, j⟩ : MRing ι) ∉ imageZ v P' := fun h0 => hj (hW.1.1.2 (Ideal.mem_sup_left h0))
    have hw : Ideal.Quotient.mk (imageZ v P') (X ⟨k0, j⟩) ∈ nonZeroDivisors _ :=
      mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
    have hx0 : G.x' (v ⟨k0, j⟩) ≠ 0 := fun h0 => hjQ (by
      rw [imageZ, Ideal.mem_comap, ← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa [aeval_rename] using h0)
    classical
    have mem : ∀ i₁ : ι k0, IsLocalization.mk' (FractionRing (MRing ι ⧸ imageZ v P'))
        (Ideal.Quotient.mk _ (X ⟨k0, i₁⟩)) ⟨_, hw⟩ ∈ locRing (imageZ v P') W := fun i₁ =>
      Subring.subset_closure ⟨_, _, Pi.single k0 1, hw, hj, AvoidRing.isMultiHomog_X k0 i₁,
        AvoidRing.isMultiHomog_X k0 j, rfl⟩
    have e : (y' ∘ v) ⟨k0, i⟩ = f ⟨_, mem i⟩ / f ⟨_, mem i0⟩ := by
      show G.x' (v ⟨k0, i⟩) / G.x' ⟨(v ⟨k0, i⟩).1, i' (v ⟨k0, i⟩).1⟩ =
        ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i⟩)) ⟨_, hw⟩)) /
          ψ (fracMapZ v P' (IsLocalization.mk' _ (Ideal.Quotient.mk _ (X ⟨k0, i0⟩)) ⟨_, hw⟩))
      rw [hf, hf, hch (hv.2.2.1 _)]
      simp only [aeval_X, Function.comp, hp0]
      rw [div_div_div_cancel_right₀ hx0]
    rw [e]
    exact div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
  have hL : L.toSubfield ≤ Subfield.closure (Set.range g) := by
    refine hgen _ _ ?_
    rintro _ ⟨q, rfl⟩
    obtain ⟨b, b', hb', e⟩ := hC K ι K' ι' κ v P' n s α W i' hv hP' hQ hs hsQ hW hi' q
    have e' := congrArg ψ e
    rw [map_mul, map_mul, fracEval_algebraMap, fracEval_algebraMap, aeval_X, aeval_X] at e'
    have hψb' : g b' ≠ 0 := (map_ne_zero ψ).2 hb'
    have : y' q = g b / g b' := by
      rw [div_eq_div_iff (hx _) hψb']
      show G.x' q * ψ b' = ψ b * G.x' ⟨q.1, i' q.1⟩
      rw [e']
      exact mul_comm _ _
    rw [this]
    exact div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
  exact hR ℚ G.Φ' _ _ L₀ L f g (ψ.injective.comp ((fracMapZ v P').injective.comp Subtype.val_injective))
    (ψ.injective.comp Subtype.val_injective) (fun _ => rfl) hfL hgL hL₀ hL
    (hF K ι K' ι' κ v P' n s α W hv hP' hQ hs hsQ hW).1

end GroundTheory.Heights₂.Heights.Inter
