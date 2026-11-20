import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingChartLoc
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P W hP hW hPW hrel`. Set `L` to `FractionRing (MRing ι ⧸ P)`. Set `q : MRing ι →+* L` to `(algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)`. Establish `hq : ∀ f, f ∉ W → q f ≠ 0` using `fun f hf h => hf (hPW (by`. Rewrite using `[RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))` and apply the resulting hypothesis.

Establish `hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)` using `fun v hv => mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))`. Establish `hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W`. Introduce `u v a hu hv hvW`. Use `Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩` and prove the remaining obligations. Rewrite using `[IsFractionRing.mk'_eq_div]`.

Both sides reduce to the same expression. Use `choose c hc using hrel`. Set `g : (Σ k, ι k) → L` to `fun p => q (X p) / q (X ⟨p.1, c p.1⟩)`. Set `B : Subring L` to `Subring.closure (Set.range g)`. Establish `hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B`.

Rewrite using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Establish `hBS : B ≤ locRing P W` using `Subring.closure_le.mpr (by`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))`. Set `θ : MRing ι →+* L` to `eval₂Hom (Int.castRingHom L) g`.

Establish `hθB : ∀ f, θ f ∈ B`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C r => rw [eval₂Hom_C, eq_intCast]`. Conclude with `intCast_mem _ r`.

Consider the case `add f₁ f₂ h₁ h₂ => rw [map_add]`. Conclude with `add_mem h₁ h₂`. Consider the case `mul_X f p hf => rw [map_mul, eval₂Hom_X']`. Conclude with `mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)`. Establish `hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k)`.

Introduce `u a hu`. Use `conv_lhs => rw [u.as_sum]`. Use `conv_rhs => rw [u.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.sum_mul, map_prod]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations.

Establish `hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p`. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩`. Rewrite using `[map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]`.

Establish `hθm : θ (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, g p ^ m p`. Rewrite using `[show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Establish `hqm : q (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, q (X p) ^ m p`. Rewrite using `[monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]`. Simplify using `only [map_pow]`.

Use `congr 1`. Conclude with `eq_intCast (q.comp C) _`. Rewrite using `[hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]`. Use `congr 1`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_pow]`. Use `congr 1`. Conclude with `(div_mul_cancel₀ _ (hq _ (hc p.1))).symm`. Use `⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[hTB]`.

Take `⟨u, v, a, hu, hv, hvW, hzv⟩` from `LocRingFrac.proof K ι P W hP hW hPW z hz`. Establish `hTW` using `AvoidRing.coordProd_not_mem hW c hc a`. Establish `hu'` using `hkey u a hu`. Establish `hv'` using `hkey v a hv`. Establish `hinv` using `hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW`.

Establish `hθv : θ v ≠ 0` using `fun h => hq v hvW (by rw [hv', h, zero_mul])`. Use `⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩` and prove the remaining obligations. Establish `he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v`. Rewrite using `[eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]`. Rewrite using `[he]`.

Conclude with `hinv`. Apply `mul_right_cancel₀ (hq _ hTW)` to reduce the goal to its premises. Rewrite using `[mul_assoc, ← hv', ← hu']`. Conclude with `hzv`.
-/
theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm
  refine ⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩
  rw [hTB]
  obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := LocRingFrac.proof K ι P W hP hW hPW z hz
  have hTW := AvoidRing.coordProd_not_mem hW c hc a
  have hu' := hkey u a hu
  have hv' := hkey v a hv
  have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
  have hθv : θ v ≠ 0 := fun h => hq v hvW (by rw [hv', h, zero_mul])
  refine ⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩
  · have he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v := by
      rw [eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]
    rw [he]
    exact hinv
  · apply mul_right_cancel₀ (hq _ hTW)
    rw [mul_assoc, ← hv', ← hu']
    exact hzv

end

end GroundTheory.Heights₂.Heights.Inter
