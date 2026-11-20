import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingNoeth
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P s a W hP hs hsP hW`. Take `⟨hPp, hPh, -⟩` from `hP`. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hW.1.1.2`. Establish `hsW : s ∈ W` using `hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))`.

Take `⟨hloc, hunit⟩` from `hL K ι P W hPp hWp hPW`. Establish `hNoeth` using `hN K ι P W hPp hWp hPW hW.2`. Use `⟨hNoeth, hloc, ?_⟩` and prove the remaining obligations. Use `choose c hc using hW.2`. Establish `ht` using `AvoidRing.isMultiHomog_coordProd (R := ℤ) c a`.

Establish `htW` using `AvoidRing.coordProd_not_mem hWp c hc a`. Use `set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k`. Establish `htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P)` using `mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))`. Use `set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩`. Establish `hxA : x ∈ locRing P W` using `Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩`.

Establish `hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s)` using `IsLocalization.mk'_spec _ _ _`. Use `set x' : locRing P W := ⟨x, hxA⟩`. Establish `hxu : ¬ IsUnit x'` using `fun h => (hunit x' s t a hs ht htW hx).mp h hsW`. Establish `hx0 : x' ≠ 0`. Introduce `h`.

Establish `h0 : x = 0` using `congrArg Subtype.val h`. Rewrite `hx` using `[h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hsP hx`. Establish `hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes`. Use `⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩` and prove the remaining obligations.

Rewrite `hy` using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Take `⟨u, v, b, hu, hv, hvW, hyuv⟩` from `hF K ι P W hPp hWp hPW y y.2`. Establish `huW : u ∈ W`. Assume the negation of the conclusion as `h`. Conclude with `hy ((hunit y u v b hu hv hvW hyuv).mpr h)`.

Take `⟨n, z, hz, hyn⟩` from `hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv`. Establish `hyn' : y ^ n = x' * ⟨z, hz⟩` using `Subtype.ext (by simpa using hyn)`. Establish `hyQ : y ^ n ∈ Q` using `hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))`. Conclude with `hQ.1.mem_of_pow_mem n hyQ`. Establish `hle` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin`.

Establish `hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥` using `fun h => hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)`. Establish `h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1` using `le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]`. Both sides reduce to the same expression.
-/
theorem LocRingDimOne.proof (hF : LocRingFrac.Statement) (hN : LocRingNoeth.Statement)
    (hL : LocRingLocal.Statement) (hPow : LocRingPow.Statement) : LocRingDimOne.Statement := by
  classical
  intro K _ ι _ P s a W hP hs hsP hW
  obtain ⟨hPp, hPh, -⟩ := hP
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
  obtain ⟨hloc, hunit⟩ := hL K ι P W hPp hWp hPW
  have hNoeth := hN K ι P W hPp hWp hPW hW.2
  refine ⟨hNoeth, hloc, ?_⟩

  choose c hc using hW.2
  have ht := AvoidRing.isMultiHomog_coordProd (R := ℤ) c a
  have htW := AvoidRing.coordProd_not_mem hWp c hc a
  set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
  have htP : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero fun h => htW (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))
  set x : FractionRing (MRing ι ⧸ P) := IsLocalization.mk' _ (Ideal.Quotient.mk P s) ⟨_, htP⟩
  have hxA : x ∈ locRing P W := Subring.subset_closure ⟨s, t, a, htP, htW, hs, ht, rfl⟩
  have hx : x * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) :=
    IsLocalization.mk'_spec _ _ _
  set x' : locRing P W := ⟨x, hxA⟩
  have hxu : ¬ IsUnit x' := fun h => (hunit x' s t a hs ht htW hx).mp h hsW
  have hx0 : x' ≠ 0 := by
    intro h
    have h0 : x = 0 := congrArg Subtype.val h
    rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hsP hx

  have hmin : IsLocalRing.maximalIdeal (locRing P W) ∈ (Ideal.span {x'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).mpr hxu⟩, fun Q hQ _ y hy => ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy
    obtain ⟨u, v, b, hu, hv, hvW, hyuv⟩ := hF K ι P W hPp hWp hPW y y.2
    have huW : u ∈ W := by
      by_contra h
      exact hy ((hunit y u v b hu hv hvW hyuv).mpr h)
    obtain ⟨n, z, hz, hyn⟩ :=
      hPow K ι P s t a W x u v b y hPp hPh hs hsP hW ht htW hx hu hv huW hvW hyuv
    have hyn' : y ^ n = x' * ⟨z, hz⟩ := Subtype.ext (by simpa using hyn)
    have hyQ : y ^ n ∈ Q := hyn' ▸ Ideal.mul_mem_right _ _ (hQ.2 (Ideal.mem_span_singleton_self x'))
    exact hQ.1.mem_of_pow_mem n hyQ
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : IsLocalRing.maximalIdeal (locRing P W) ≠ ⊥ := fun h =>
    hx0 (by simpa [h] using (IsLocalRing.mem_maximalIdeal x').mpr hxu)
  have h1 : (IsLocalRing.maximalIdeal (locRing P W)).height = 1 :=
    le_antisymm hle (Order.one_le_iff_ne_zero.mpr (fun h => hne (Ideal.height_eq_zero_iff_eq_bot.mp h)))
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h1]
  rfl

end

end GroundTheory.Heights₂.Heights.Inter
