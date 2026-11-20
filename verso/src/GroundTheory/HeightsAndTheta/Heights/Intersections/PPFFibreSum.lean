import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreSum
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreBij
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFFibreMult
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Homog

variable {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[Pi.single_apply]`.
-/
theorem weight_blockSingle (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) d = fun k => ∑ i, d ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [Pi.single_apply]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h d hd`. Rewrite using `[weight_blockSingle]`. Use function extensionality and compare the values at `k`. Conclude with `h d (mem_support_iff.mpr hd) k`.

Introduce `h m hm k`. Use `h (mem_support_iff.mp hm)` as an intermediate fact. Rewrite `this` using `[weight_blockSingle]`. Conclude with `congrFun this k`.
-/
theorem isMultiHomog_iff_weighted (f : MRingOver R ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (fun q : Σ k, ι k => (Pi.single q.1 1 : K → ℕ)) f a := by
  constructor
  · intro h d hd
    rw [weight_blockSingle]
    funext k
    exact h d (mem_support_iff.mpr hd) k
  · intro h m hm k
    have := h (mem_support_iff.mp hm)
    rw [weight_blockSingle] at this
    exact congrFun this k

end Homog

section Subst

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

/- English proof (translation)
Establish `h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) : MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) = (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]`. Introduce `q`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]`. Unfold `baseSubst`. Rewrite using `[eval₂Hom_X']`. Use `split_ifs with h h'`. Rewrite using `[aeval_C, ← G.compat, h'.choose_spec]`.

Conclude with `absurd (hv.2.2.2 q h) h'`. Rewrite using `[aeval_X]`. Conclude with `DFunLike.congr_fun h f`.
-/
theorem aeval_baseSubst (hv : IsBlockMap κ v) (G : GenFibre v P') (f : MRing ι') :
    aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) (baseSubst κ G f) = aeval G.x' f := by
  have h : ((aeval (fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩) :
      MRingOver G.Φ (fibreIdx ι' κ) →ₐ[G.Φ] G.Φ').toRingHom.comp (baseSubst κ G)) =
      (aeval G.x' : MRing ι' →ₐ[ℤ] G.Φ').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [show (C r : MRing ι') = (r : MRing ι') from eq_intCast C r, map_intCast]
    · intro q
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
      unfold baseSubst
      rw [eval₂Hom_X']
      split_ifs with h h'
      · rw [aeval_C, ← G.compat, h'.choose_spec]
      · exact absurd (hv.2.2.2 q h) h'
      · rw [aeval_X]
  exact DFunLike.congr_fun h f

/- English proof (translation)
Rewrite `hs`, the goal using `[isMultiHomog_iff_weighted]`. Establish `hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ)) (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0) else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ)) (fun k : Fibre …`. Introduce `q`. Distinguish the cases in `h : q.1 ∈ Set.range κ`. Establish `h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0`.

Use function extensionality and compare the values at `k`. Establish `: k.1 ≠ q.1` using `fun e => k.2 (e ▸ h)`. Simplify using `[this]`. Rewrite using `[dif_pos h, h0]`. Use `split_ifs`.

Conclude with `isWeightedHomogeneous_C _ _`. Conclude with `isWeightedHomogeneous_zero _ _ _`. Rewrite using `[dif_neg h]`. Establish `e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ)`. Use function extensionality and compare the values at `k`.

Simplify using `[Pi.single_apply, Subtype.ext_iff]`. Rewrite using `[e]`. Conclude with `isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)`. Proceed by induction on `hs using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => rw [map_zero]`.

Conclude with `isWeightedHomogeneous_zero _ _ _`. Consider the case `add p q hp hq ihp ihq => rw [map_add]`. Conclude with `ihp.add ihq`. Consider the case `monomial d r hr`. Unfold `baseSubst`.

Rewrite using `[coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]`. Use `((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[← hr]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`.
-/
theorem baseSubst_isMultiHomog (G : GenFibre v P') {s : MRing ι'} {a : K' → ℕ} (hs : IsMultiHomog s a) :
    IsMultiHomog (baseSubst κ G s) (fun k : FibreBlock κ => a k.1) := by
  classical
  rw [isMultiHomog_iff_weighted] at hs ⊢
  have hg : ∀ q : Σ k', ι' k', IsWeightedHomogeneous
      (fun q : Σ k : FibreBlock κ, ι' k.1 => (Pi.single q.1 1 : FibreBlock κ → ℕ))
      (if h : q.1 ∈ Set.range κ then (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
        else X ⟨⟨q.1, h⟩, q.2⟩ : MRingOver G.Φ (fibreIdx ι' κ))
      (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) := by
    intro q
    by_cases h : q.1 ∈ Set.range κ
    · have h0 : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) = 0 := by
        funext k
        have : k.1 ≠ q.1 := fun e => k.2 (e ▸ h)
        simp [this]
      rw [dif_pos h, h0]
      split_ifs
      · exact isWeightedHomogeneous_C _ _
      · exact isWeightedHomogeneous_zero _ _ _
    · rw [dif_neg h]
      have e : (fun k : FibreBlock κ => (Pi.single q.1 1 : K' → ℕ) k.1) =
          (Pi.single (⟨q.1, h⟩ : FibreBlock κ) 1 : FibreBlock κ → ℕ) := by
        funext k
        simp [Pi.single_apply, Subtype.ext_iff]
      rw [e]
      exact isWeightedHomogeneous_X G.Φ _ (⟨⟨q.1, h⟩, q.2⟩ : Σ k : FibreBlock κ, ι' k.1)
  induction hs using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero _ _ _
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    unfold baseSubst
    rw [coe_eval₂Hom, eval₂_monomial, MvPolynomial.algebraMap_apply, Finsupp.prod]
    convert ((IsWeightedHomogeneous.prod d.support _ _ fun q _ => (hg q).pow (d q)).C_mul _) using 1
    funext k
    rw [← hr]
    simp [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]

end Subst

/- English proof (translation)
Introduce `K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP`. Establish `hV : IsProjVarF (fibreIdeal κ G) (r + 1)` using `hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP`. Establish `hmem : ∀ g : MRing ι', baseSubst κ G g ∈ fibreIdeal κ G ↔ g ∈ P'`. Introduce `g`. Rewrite using `[fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]`.

Establish `hsec : IsRatSection (fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1`. Use `⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs, (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h), fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩` and prove the remaining obligations. Simplify using `[fibreDeg, hNa]`. Establish `hb' : J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) = cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a)) (ratDiv (fibreIdeal κ G) (baseSubst κ G s) 1)`. Rewrite using `[← hJ.2 _ r _ _ _ _ hV hsec]`.

Conclude with `congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm`. Establish `hdiv1 : divCycle (fibreIdeal κ G) 1 = 0`. Use extensionality with `W`. Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]`. Rewrite using `[if_neg]`.

Simplify using `[divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]`. Use `set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a`. Use `set V := fibreIdeal κ G`. Use `set f := baseSubst κ G s`. Establish `hD : ∀ Q, (divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0`.

Introduce `Q`. Simplify using `only [divCycle, Finsupp.ofSupportFinite_coe]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) = ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ)`. Rewrite using `[ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval, Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum, finsum_mem_def]`.

Simplify using `only [Int.cast_mul, Int.cast_natCast]`. Establish `hsupp : Function.support (fun Q => (divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(divCycle V f).support`. Introduce `Q hQ`. Rewrite `hQ` using `[Function.mem_support]`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff]`.

Introduce `h0`. Conclude with `hQ (by rw [h0]; simp)`. Rewrite using `[← finsum_eq_sum_of_support_subset _ hsupp]`. Use `congr 1`. Use function extensionality and compare the values at `Q`.

Rewrite using `[hD]`. Apply the tactic sequence `by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]`. Establish `hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) = ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'}, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf …`. Rewrite using `[finsum_mem_def, finsum_mem_def]`. Use `congr 1`.

Use function extensionality and compare the values at `W`. Apply the tactic sequence `by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>`. Simplify using `[Set.indicator, hW, hH]`. Rewrite using `[hb', hR, hL]`. Use `finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_` and prove the remaining obligations.

Introduce and unpack `W ⟨hW, hH, hI⟩`. Rewrite using `[hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]`.
-/
theorem PFFibreSum.proof (hFD : FibreDimStatement) (hBij : PFFibreBij.Statement) (hMult : PFFibreMult.Statement) :
    PFFibreSum.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r G J N s a hv hP' hP hJ hNa hs hsP
  classical
  have hV : IsProjVarF (fibreIdeal κ G) (r + 1) := hFD K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hmem : ∀ g : MRing ι', baseSubst κ G g ∈ fibreIdeal κ G ↔ g ∈ P' := by
    intro g
    rw [fibreIdeal, RingHom.mem_ker, aeval_baseSubst hv, ← RingHom.mem_ker, G.genericFibre_ker_target]
  have hsec : IsRatSection (fibreIdeal κ G) (fibreDeg κ (N (Fin.last r)).a) (baseSubst κ G s) 1 := by
    refine ⟨fun k => a k.1, 0, baseSubst_isMultiHomog G hs,
      (isMultiHomog_iff_weighted _ _).mpr (isWeightedHomogeneous_one _ _), fun h => hsP ((hmem s).mp h),
      fun h1 => hV.1.1.ne_top ((Ideal.eq_top_iff_one _).mpr h1), fun k => ?_⟩
    simp [fibreDeg, hNa]
  have hb' : J (fibreIdeal κ G) (r + 1) (fun j => fibreDeg κ (N j).a) =
      cycEval (fun W => J W r (fun j => fibreDeg κ (N (Fin.castSucc j)).a))
        (ratDiv (fibreIdeal κ G) (baseSubst κ G s) 1) := by
    rw [← hJ.2 _ r _ _ _ _ hV hsec]
    exact congrArg _ (Fin.snoc_init_self (α := fun _ => FibreBlock κ → ℤ) (fun j => fibreDeg κ (N j).a)).symm
  have hdiv1 : divCycle (fibreIdeal κ G) 1 = 0 := by
    ext W
    simp only [divCycle, Finsupp.ofSupportFinite_coe, Finsupp.coe_zero, Pi.zero_apply]
    rw [if_neg]
    simp [divSupp, Ideal.span_singleton_one, Ideal.minimalPrimes_top]
  set L := fun j : Fin r => fibreDeg κ (N (Fin.castSucc j)).a
  set V := fibreIdeal κ G
  set f := baseSubst κ G s
  have hD : ∀ Q, (divCycle V f Q : ℝ) = if Q ∈ divSupp V f then (multAt (V ⊔ Ideal.span {f}) Q : ℝ) else 0 := by
    intro Q
    simp only [divCycle, Finsupp.ofSupportFinite_coe]
    split_ifs <;> simp

  have hR : ((cycEval (fun W => J W r L) (ratDiv V f 1) : ℤ) : ℝ) =
      ∑ᶠ Q ∈ divSupp V f, (multAt (V ⊔ Ideal.span {f}) Q : ℝ) * (J Q r L : ℝ) := by
    rw [ratDiv, hdiv1, Finsupp.mapRange_zero, sub_zero, cycEval,
      Finsupp.sum_mapRange_index (fun _ => zero_mul _), Finsupp.sum, Int.cast_sum,
      finsum_mem_def]
    simp only [Int.cast_mul, Int.cast_natCast]
    have hsupp : Function.support (fun Q => (divCycle V f Q : ℝ) * (J Q r L : ℝ)) ⊆ ↑(divCycle V f).support := by
      intro Q hQ
      rw [Function.mem_support] at hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      exact hQ (by rw [h0]; simp)
    rw [← finsum_eq_sum_of_support_subset _ hsupp]
    congr 1
    funext Q
    rw [hD]
    by_cases hQ : Q ∈ divSupp V f <;> simp [hQ, Set.indicator]

  have hL : ∑ᶠ W ∈ divSupp P' s, (multAt (P' ⊔ Ideal.span {s}) W : ℝ) *
        (if IsHorizontal W ∧ imageZ v W = imageZ v P' then (J (fibreOf κ G W) r L : ℝ) else 0) =
      ∑ᶠ W ∈ {W | W ∈ divSupp P' s ∧ IsHorizontal W ∧ imageZ v W = imageZ v P'},
        (multAt (P' ⊔ Ideal.span {s}) W : ℝ) * (J (fibreOf κ G W) r L : ℝ) := by
    rw [finsum_mem_def, finsum_mem_def]
    congr 1
    funext W
    by_cases hW : W ∈ divSupp P' s <;> by_cases hH : IsHorizontal W ∧ imageZ v W = imageZ v P' <;>
      simp [Set.indicator, hW, hH]
  rw [hb', hR, hL]
  refine finsum_mem_eq_of_bijOn (fibreOf κ G) (hBij K ι K' ι' κ v P' d (d + r + 1) G s hv hP' hP) ?_
  rintro W ⟨hW, hH, hI⟩
  rw [hMult K ι K' ι' κ v P' d (d + r + 1) G s W hv hP' hP hW hH hI]

end

end GroundTheory.Heights₂.Heights.Inter
