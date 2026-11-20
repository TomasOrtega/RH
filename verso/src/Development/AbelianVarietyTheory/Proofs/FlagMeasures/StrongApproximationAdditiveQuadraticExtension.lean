import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
The claim follows from `(PlacesInt.mem_int_iff T _).2 (p.valuation_le_one a)`.
-/
theorem int_of (T : LocAt F E sig p) (a : 𝓞 F) :
    valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a)) ≤ 1 :=
  (PlacesInt.mem_int_iff T _).2 (p.valuation_le_one a)

/- English proof (translation)
Use `haveI := T.lf`. Establish `hw0 : valuation T.Fp w ≠ 0` using `by simpa using hw`. Establish `hn : {z : T.Fp | valuation T.Fp (z - w) < valuation T.Fp w} ∈ nhds w` using `IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hw0, fun z hz => hz⟩`. Take `⟨k, hk⟩` from `T.dense.mem_nhds hn`. Establish `hk' : valuation T.Fp (T.ιF k - w) < valuation T.Fp w` using `hk`.

Establish `hkv : valuation T.Fp (T.ιF k) = valuation T.Fp w`. Establish `e : T.ιF k = w + (T.ιF k - w)` using `by ring`. Rewrite using `[e, Valuation.map_add_eq_of_lt_left _ hk']`. Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) k`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`.

Establish `hsK : algebraMap (𝓞 F) F s ≠ 0` using `by simpa using hs0`. Use `⟨a, fun ha => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hkv` using `[ha, map_zero, zero_div, map_zero, map_zero]`. Conclude with `hw0 hkv.symm`. Establish `e : T.ιF (algebraMap (𝓞 F) F a) = T.ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) * T.ιF (algebraMap (𝓞 F) F s)`.

Rewrite using `[← map_mul, div_mul_cancel₀ _ hsK]`. Rewrite using `[e, Valuation.map_mul, hkv]`. Conclude with `mul_le_of_le_one_right' (int_of T s)`.
-/
theorem small_local (T : LocAt F E sig p) (w : T.Fp) (hw : w ≠ 0) :
    ∃ a : 𝓞 F, a ≠ 0 ∧ valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a)) ≤ valuation T.Fp w := by
  haveI := T.lf
  have hw0 : valuation T.Fp w ≠ 0 := by simpa using hw
  have hn : {z : T.Fp | valuation T.Fp (z - w) < valuation T.Fp w} ∈ nhds w :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hw0, fun z hz => hz⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - w) < valuation T.Fp w := hk
  have hkv : valuation T.Fp (T.ιF k) = valuation T.Fp w := by
    have e : T.ιF k = w + (T.ιF k - w) := by ring
    rw [e, Valuation.map_add_eq_of_lt_left _ hk']
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := by simpa using hs0
  refine ⟨a, fun ha => ?_, ?_⟩
  · rw [ha, map_zero, zero_div, map_zero, map_zero] at hkv
    exact hw0 hkv.symm
  · have e : T.ιF (algebraMap (𝓞 F) F a) =
        T.ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F s) * T.ιF (algebraMap (𝓞 F) F s) := by
      rw [← map_mul, div_mul_cancel₀ _ hsK]
    rw [e, Valuation.map_mul, hkv]
    exact mul_le_of_le_one_right' (int_of T s)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `insert q S hq ih`. Take `⟨h, hh, hS⟩` from `ih (fun p hp => hw p (Finset.mem_insert_of_mem hp))`. Take `⟨a, ha, ha'⟩` from `small_local (A.loc q) (w q) (hw q (Finset.mem_insert_self q S))`.

Use `⟨h * a, mul_ne_zero hh ha, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Valuation.map_mul]`. Break down `Finset.mem_insert.mp hp with rfl | hp` into its components or cases. Conclude with `(mul_le_of_le_one_left' (int_of _ h)).trans ha'`. Conclude with `(mul_le_of_le_one_right' (int_of _ a)).trans (hS p hp)`.
-/
theorem small (A : Places F E sig) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (w : ∀ p, (A.loc p).Fp) (hw : ∀ p ∈ S, w p ≠ 0) :
    ∃ h : 𝓞 F, h ≠ 0 ∧ ∀ p ∈ S,
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ valuation (A.loc p).Fp (w p) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert q S hq ih =>
    obtain ⟨h, hh, hS⟩ := ih (fun p hp => hw p (Finset.mem_insert_of_mem hp))
    obtain ⟨a, ha, ha'⟩ := small_local (A.loc q) (w q) (hw q (Finset.mem_insert_self q S))
    refine ⟨h * a, mul_ne_zero hh ha, fun p hp => ?_⟩
    rw [map_mul, map_mul, Valuation.map_mul]
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (mul_le_of_le_one_left' (int_of _ h)).trans ha'
    · exact (mul_le_of_le_one_right' (int_of _ a)).trans (hS p hp)

/- English proof (translation)
Use `haveI := T.lf`. Establish `hhK : algebraMap (𝓞 F) F h ≠ 0` using `by simpa using hh`. Establish `hh0 : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) ≠ 0` using `by simpa using hhK`. Establish `hn : {x : T.Fp | valuation T.Fp (x - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))} ∈ nhds z` using `IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hh0, fun x hx => hx⟩`. Take `⟨k, hk⟩` from `T.dense.mem_nhds hn`.

Establish `hk' : valuation T.Fp (T.ιF k - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))` using `hk`. Establish `hk1 : p.valuation F k ≤ 1`. Rewrite using `[← PlacesInt.mem_int_iff T]`. Establish `e : T.ιF k = (T.ιF k - z) + z` using `by ring`. Use `show valuation T.Fp (T.ιF k) ≤ 1`.

Rewrite using `[e]`. Conclude with `(valuation T.Fp).map_add_le (hk'.le.trans (int_of T h)) hz`. Establish `hpv : p.valuation F (algebraMap (𝓞 F) F h) ≠ 0` using `by simpa using hhK`. Take `⟨a, ha⟩` from `p.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hpv)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - k)) ≤ valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))` using `(PlacesInt.val_le_iff T _ _).2 ha.le`. Establish `e : z - T.ιF (algebraMap (𝓞 F) F a) = -(T.ιF k - z) - T.ιF (algebraMap (𝓞 F) F a - k)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `((valuation T.Fp).map_sub _ _).trans (max_le ?_ ha')` and prove the remaining obligations. Rewrite using `[Valuation.map_neg]`. Conclude with `hk'.le`.
-/
theorem approx_local (T : LocAt F E sig p) (z : T.Fp) (hz : valuation T.Fp z ≤ 1) (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, valuation T.Fp (z - T.ιF (algebraMap (𝓞 F) F a)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := by
  haveI := T.lf
  have hhK : algebraMap (𝓞 F) F h ≠ 0 := by simpa using hh
  have hh0 : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) ≠ 0 := by simpa using hhK
  have hn : {x : T.Fp | valuation T.Fp (x - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h))} ∈ nhds z :=
    IsValuativeTopology.mem_nhds_iff'.2 ⟨Units.mk0 _ hh0, fun x hx => hx⟩
  obtain ⟨k, hk⟩ := T.dense.mem_nhds hn
  have hk' : valuation T.Fp (T.ιF k - z) < valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) := hk
  have hk1 : p.valuation F k ≤ 1 := by
    rw [← PlacesInt.mem_int_iff T]
    have e : T.ιF k = (T.ιF k - z) + z := by ring
    show valuation T.Fp (T.ιF k) ≤ 1
    rw [e]
    exact (valuation T.Fp).map_add_le (hk'.le.trans (int_of T h)) hz
  have hpv : p.valuation F (algebraMap (𝓞 F) F h) ≠ 0 := by simpa using hhK
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hk1 (Units.mk0 _ hpv)
  refine ⟨a, ?_⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - k)) ≤
      valuation T.Fp (T.ιF (algebraMap (𝓞 F) F h)) :=
    (PlacesInt.val_le_iff T _ _).2 ha.le
  have e : z - T.ιF (algebraMap (𝓞 F) F a) = -(T.ιF k - z) - T.ιF (algebraMap (𝓞 F) F a - k) := by
    rw [map_sub]; ring
  rw [e]
  refine ((valuation T.Fp).map_sub _ _).trans (max_le ?_ ha')
  rw [Valuation.map_neg]; exact hk'.le

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

/- English proof (translation)
Establish `hT : {p : HeightOneSpectrum (𝓞 F) | p.asIdeal ∣ Ideal.span {h}}.Finite` using `Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hh)`. Use `choose a0 ha0 using fun p => approx_local (A.loc p) (z p) (hz p) h hh`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := hT.toFinset) (fun p => p.asIdeal) (fun p => multiplicity p.asIdeal (Ideal.span {h})) (fun p _ => p.prime) (fun p _ q _ hpq e => hpq (HeightOneSpectrum.ext e)) (fun p => a0 p.1)`. Use `⟨a, fun p => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp : p ∈ hT.toFinset`.

Establish `h1` using `ha p hp`. Rewrite `h1` using `[← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity p hh, ← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)]`. Establish `h2` using `(PlacesInt.val_le_iff (A.loc p) _ _).2 h1`. Establish `e : z p - (A.loc p).ιF (algebraMap (𝓞 F) F a) = (z p - (A.loc p).ιF (algebraMap (𝓞 F) F (a0 p))) - (A.loc p).ιF (algebraMap (𝓞 F) F (a - a0 p))`. Rewrite using `[map_sub, map_sub]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (ha0 p) h2)`. Establish `h1 : p.intValuation h = 1`. Rewrite using `[HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]`.

Use `Ideal.mem_primeCompl_iff.mpr fun hmem => hp ?_` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `Ideal.dvd_span_singleton.mpr hmem`. Establish `h2 : p.valuation F (algebraMap (𝓞 F) F 1) ≤ p.valuation F (algebraMap (𝓞 F) F h)`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, h1, map_one]`.

Establish `h3` using `(PlacesInt.val_le_iff (A.loc p) _ _).2 h2`. Rewrite `h3` using `[map_one, map_one, map_one]`. Use `le_trans ?_ h3` and prove the remaining obligations. Conclude with `((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (hz p) (int_of _ a))`.
-/
theorem approx (A : Places F E sig) (z : ∀ p, (A.loc p).Fp) (hz : ∀ p, valuation (A.loc p).Fp (z p) ≤ 1)
    (h : 𝓞 F) (hh : h ≠ 0) :
    ∃ a : 𝓞 F, ∀ p, valuation (A.loc p).Fp (z p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) ≤
      valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F h)) := by
  have hT : {p : HeightOneSpectrum (𝓞 F) | p.asIdeal ∣ Ideal.span {h}}.Finite :=
    Ideal.finite_factors (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hh)
  choose a0 ha0 using fun p => approx_local (A.loc p) (z p) (hz p) h hh
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hT.toFinset) (fun p => p.asIdeal)
    (fun p => multiplicity p.asIdeal (Ideal.span {h})) (fun p _ => p.prime)
    (fun p _ q _ hpq e => hpq (HeightOneSpectrum.ext e)) (fun p => a0 p.1)
  refine ⟨a, fun p => ?_⟩
  by_cases hp : p ∈ hT.toFinset
  · have h1 := ha p hp
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem,
      ← HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity p hh,
      ← HeightOneSpectrum.valuation_of_algebraMap (K := F), ← HeightOneSpectrum.valuation_of_algebraMap (K := F)] at h1
    have h2 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h1
    have e : z p - (A.loc p).ιF (algebraMap (𝓞 F) F a) =
        (z p - (A.loc p).ιF (algebraMap (𝓞 F) F (a0 p))) - (A.loc p).ιF (algebraMap (𝓞 F) F (a - a0 p)) := by
      rw [map_sub, map_sub]; ring
    rw [e]
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (ha0 p) h2)
  · have h1 : p.intValuation h = 1 := by
      rw [HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl]
      refine Ideal.mem_primeCompl_iff.mpr fun hmem => hp ?_
      rw [Set.Finite.mem_toFinset]; exact Ideal.dvd_span_singleton.mpr hmem
    have h2 : p.valuation F (algebraMap (𝓞 F) F 1) ≤ p.valuation F (algebraMap (𝓞 F) F h) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, h1, map_one]
    have h3 := (PlacesInt.val_le_iff (A.loc p) _ _).2 h2
    rw [map_one, map_one, map_one] at h3
    refine le_trans ?_ h3
    exact ((valuation (A.loc p).Fp).map_sub _ _).trans (max_le (hz p) (int_of _ a))

/- English proof (translation)
Take `⟨r, hr, hr'⟩` from `small A hy.toFinset (fun p => (y p)⁻¹) (fun p hp => by`. Establish `hp' : y p ∉ 𝒪[(A.loc p).Fp]` using `hy.mem_toFinset.mp hp`. Conclude with `inv_ne_zero fun h0 => hp' (h0 ▸ zero_mem _))`. Establish `hrK : algebraMap (𝓞 F) F r ≠ 0` using `by simpa using hr`. Establish `hz : ∀ p, valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p) ≤ 1`.

Introduce `p`. Rewrite using `[Valuation.map_mul]`. Distinguish the cases in `hp : y p ∈ 𝒪[(A.loc p).Fp]`. Conclude with `mul_le_one' (int_of _ r) hp`. Establish `h1` using `hr' p (hy.mem_toFinset.mpr hp)`.

Establish `hy0 : y p ≠ 0` using `fun h0 => hp (h0 ▸ zero_mem _)`. Establish `hy1 : valuation (A.loc p).Fp (y p) ≠ 0` using `by simpa using hy0`. Rewrite `h1` using `[map_inv₀]`. Combine the equalities or inequalities in the displayed calculation. Establish `hr0 : {p : HeightOneSpectrum (𝓞 F) | p.valuation F (algebraMap (𝓞 F) F r) < 1}.Finite`.

Use `(HeightOneSpectrum.Support.finite (𝓞 F) (algebraMap (𝓞 F) F r)⁻¹).subset fun p hp => ?_` and prove the remaining obligations. Establish `hp' : p.valuation F (algebraMap (𝓞 F) F r) < 1` using `hp`. Use `show 1 < p.valuation F (algebraMap (𝓞 F) F r)⁻¹`. Rewrite using `[map_inv₀]`. Conclude with `one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hrK), hp'⟩`.

Take `⟨h, hh, hh'⟩` from `small A (hc.union hr0).toFinset (fun p => (A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) (fun p _ => mul_ne_zero (by simpa using hrK) (c p).ne_zero)`. Take `⟨a, ha⟩` from `approx A _ hz h hh`. Use `⟨algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r, fun p => ?_⟩` and prove the remaining obligations. Use `set v := valuation (A.loc p).Fp`. Establish `hrp : (A.loc p).ιF (algebraMap (𝓞 F) F r) ≠ 0` using `by simpa using hrK`.

Establish `hvr : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) ≠ 0` using `by simpa using hrp`. Establish `hcv : v (c p : (A.loc p).Fp) ≠ 0` using `by simpa using (c p).ne_zero`. Establish `key : v ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r) * c p)`. Distinguish the cases in `hp : p ∈ (hc.union hr0).toFinset`. Conclude with `hh' p hp`.

Rewrite `hp` using `[Set.Finite.mem_toFinset, Set.mem_union, not_or]`. Take `⟨u, hu⟩` from `not_not.mp hp.1`. Establish `hu1 : v (c p : (A.loc p).Fp) = 1`. Rewrite using `[← hu]`. Conclude with `(Valuation.integer.integers v).one_of_isUnit u.isUnit`.

Establish `hr1 : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) = 1`. Use `le_antisymm (int_of _ r) ?_` and prove the remaining obligations. Use `(PlacesInt.val_le_iff (A.loc p) 1 (algebraMap (𝓞 F) F r)).2 (not_lt.mp hp.2 |>.trans_eq' (by simp))` as an intermediate fact. Simplify using `using this`. Rewrite using `[Valuation.map_mul, hu1, hr1, mul_one]`.

Conclude with `int_of _ h`. Use `set d := (A.loc p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r) - y p`. Establish `hd : d = -((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) * ((A.loc p).ιF (algebraMap (𝓞 F) F r))⁻¹`. Simplify using `only [d, map_div₀]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hdv : v d ≤ v (c p : (A.loc p).Fp)`. Rewrite using `[hd, Valuation.map_mul, Valuation.map_neg, map_inv₀]`. Use `(ha p).trans key` as an intermediate fact. Rewrite `this` using `[Valuation.map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨⟨(c p : (A.loc p).Fp)⁻¹ * d, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show v ((c p : (A.loc p).Fp)⁻¹ * d) ≤ 1`. Rewrite using `[Valuation.map_mul, map_inv₀]`. Combine the equalities or inequalities in the displayed calculation.

Use `show d = c p * ((c p : (A.loc p).Fp)⁻¹ * d)`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ (c p).ne_zero, one_mul]`.
-/
theorem approxF (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Fp) (hy : {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite) :
    ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o := by

  obtain ⟨r, hr, hr'⟩ := small A hy.toFinset (fun p => (y p)⁻¹) (fun p hp => by
    have hp' : y p ∉ 𝒪[(A.loc p).Fp] := hy.mem_toFinset.mp hp
    exact inv_ne_zero fun h0 => hp' (h0 ▸ zero_mem _))
  have hrK : algebraMap (𝓞 F) F r ≠ 0 := by simpa using hr
  have hz : ∀ p, valuation (A.loc p).Fp ((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p) ≤ 1 := by
    intro p
    rw [Valuation.map_mul]
    by_cases hp : y p ∈ 𝒪[(A.loc p).Fp]
    · exact mul_le_one' (int_of _ r) hp
    · have h1 := hr' p (hy.mem_toFinset.mpr hp)
      have hy0 : y p ≠ 0 := fun h0 => hp (h0 ▸ zero_mem _)
      have hy1 : valuation (A.loc p).Fp (y p) ≠ 0 := by simpa using hy0
      rw [map_inv₀] at h1
      calc _ ≤ (valuation (A.loc p).Fp (y p))⁻¹ * valuation (A.loc p).Fp (y p) := mul_le_mul' h1 le_rfl
        _ = 1 := inv_mul_cancel₀ hy1

  have hr0 : {p : HeightOneSpectrum (𝓞 F) | p.valuation F (algebraMap (𝓞 F) F r) < 1}.Finite := by
    refine (HeightOneSpectrum.Support.finite (𝓞 F) (algebraMap (𝓞 F) F r)⁻¹).subset fun p hp => ?_
    have hp' : p.valuation F (algebraMap (𝓞 F) F r) < 1 := hp
    show 1 < p.valuation F (algebraMap (𝓞 F) F r)⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.2 ⟨zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hrK), hp'⟩
  obtain ⟨h, hh, hh'⟩ := small A (hc.union hr0).toFinset
    (fun p => (A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) (fun p _ => mul_ne_zero (by simpa using hrK) (c p).ne_zero)
  obtain ⟨a, ha⟩ := approx A _ hz h hh
  refine ⟨algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r, fun p => ?_⟩
  set v := valuation (A.loc p).Fp
  have hrp : (A.loc p).ιF (algebraMap (𝓞 F) F r) ≠ 0 := by simpa using hrK
  have hvr : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) ≠ 0 := by simpa using hrp
  have hcv : v (c p : (A.loc p).Fp) ≠ 0 := by simpa using (c p).ne_zero

  have key : v ((A.loc p).ιF (algebraMap (𝓞 F) F h)) ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r) * c p) := by
    by_cases hp : p ∈ (hc.union hr0).toFinset
    · exact hh' p hp
    · rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hp
      obtain ⟨u, hu⟩ := not_not.mp hp.1
      have hu1 : v (c p : (A.loc p).Fp) = 1 := by
        rw [← hu]
        exact (Valuation.integer.integers v).one_of_isUnit u.isUnit
      have hr1 : v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) = 1 := by
        refine le_antisymm (int_of _ r) ?_
        have := (PlacesInt.val_le_iff (A.loc p) 1 (algebraMap (𝓞 F) F r)).2 (not_lt.mp hp.2 |>.trans_eq' (by simp))
        simpa using this
      rw [Valuation.map_mul, hu1, hr1, mul_one]
      exact int_of _ h
  set d := (A.loc p).ιF (algebraMap (𝓞 F) F a / algebraMap (𝓞 F) F r) - y p
  have hd : d = -((A.loc p).ιF (algebraMap (𝓞 F) F r) * y p - (A.loc p).ιF (algebraMap (𝓞 F) F a)) *
      ((A.loc p).ιF (algebraMap (𝓞 F) F r))⁻¹ := by
    simp only [d, map_div₀]; field_simp; ring
  have hdv : v d ≤ v (c p : (A.loc p).Fp) := by
    rw [hd, Valuation.map_mul, Valuation.map_neg, map_inv₀]
    have := (ha p).trans key
    rw [Valuation.map_mul] at this
    calc _ ≤ v ((A.loc p).ιF (algebraMap (𝓞 F) F r)) * v (c p : (A.loc p).Fp) *
          (v ((A.loc p).ιF (algebraMap (𝓞 F) F r)))⁻¹ := mul_le_mul' this le_rfl
      _ = v (c p : (A.loc p).Fp) := by field_simp
  refine ⟨⟨(c p : (A.loc p).Fp)⁻¹ * d, ?_⟩, ?_⟩
  · show v ((c p : (A.loc p).Fp)⁻¹ * d) ≤ 1
    rw [Valuation.map_mul, map_inv₀]
    calc _ ≤ (v (c p : (A.loc p).Fp))⁻¹ * v (c p : (A.loc p).Fp) := mul_le_mul' le_rfl hdv
      _ = 1 := inv_mul_cancel₀ hcv
  · show d = c p * ((c p : (A.loc p).Fp)⁻¹ * d)
    rw [← mul_assoc, mul_inv_cancel₀ (c p).ne_zero, one_mul]

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

/- English proof (translation)
Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩`.
-/
theorem exists_place (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩⟩

/- English proof (translation)
Take `⟨p⟩` from `exists_place F`. Use `haveI := PlacesInt.nontrivial_Ep (A.loc p)`. Apply `(A.loc p).ιE.injective` to reduce the goal to its premises. Rewrite using `[← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]`.
-/
theorem sig_sig (A : Places F E sig) (y : E) : sig (sig y) = y := by
  obtain ⟨p⟩ := exists_place F
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  apply (A.loc p).ιE.injective
  rw [← (A.loc p).cj_ιE, ← (A.loc p).cj_ιE, ← A.L_cj, (A.L p).cj_cj]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨p⟩` from `exists_place F`. Establish `h2 : ∀ z, (A.loc p).cj z = z`. Introduce `z`.

Establish `hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE)`. Rewrite using `[(A.loc p).span]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨y, rfl⟩ := hz`.

Rewrite using `[(A.loc p).cj_ιE, hne]`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`. Consider the case `smul c a _ ha => rw [map_smul, ha]`. Establish `h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep)`.

Introduce `z`. Conclude with `((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)`. Establish `h4` using `LinearMap.finrank_le_finrank_of_surjective h3`. Rewrite `h4` using `[(A.loc p).rank, Module.finrank_self]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sig_ne (A : Places F E sig) : ∃ e : E, sig e ≠ e := by
  by_contra hne
  push_neg at hne
  obtain ⟨p⟩ := exists_place F
  have h2 : ∀ z, (A.loc p).cj z = z := by
    intro z
    have hz : z ∈ Submodule.span (A.loc p).Fp (Set.range (A.loc p).ιE) := by
      rw [(A.loc p).span]; trivial
    induction hz using Submodule.span_induction with
    | mem z hz => obtain ⟨y, rfl⟩ := hz; rw [(A.loc p).cj_ιE, hne]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]
  have h3 : Function.Surjective (Algebra.linearMap (A.loc p).Fp (A.loc p).Ep) := by
    intro z
    exact ((A.L p).cj_fix z).1 (by rw [A.L_cj]; exact h2 z)
  have h4 := LinearMap.finrank_le_finrank_of_surjective h3
  rw [(A.loc p).rank, Module.finrank_self] at h4
  omega

/- English proof (translation)
Establish `hint : ∀ o : 𝓞 E, IsIntegral ℤ (sig (o : E))` using `fun o => (o.isIntegral_coe).map (sig.toRingHom.toIntAlgHom)`. It suffices to establish `h : ∃ o : 𝓞 E, sig (o : E) ≠ o by`. Take `⟨o, ho⟩` from `h`. Use `⟨o - ⟨sig o, hint o⟩, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `sig ((o : E) - sig o) = -((o : E) - sig o)`.

Rewrite using `[map_sub, sig_sig A]`. Expand and normalize the polynomial expressions, which then agree. Express the relevant statement in the definitionally equal form `(o : E) - sig o ≠ 0`. Rewrite using `[sub_ne_zero]`. Conclude with `fun h => ho h.symm`.

Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Take `⟨e, he⟩` from `sig_ne A`. Take `⟨a, s, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) e`. Apply `he` to reduce the goal to its premises.

Rewrite using `[map_div₀]`. Conclude with `congrArg₂ (· / ·) (hne a) (hne s)`.
-/
theorem exists_d (A : Places F E sig) : ∃ d : 𝓞 E, sig (d : E) = -(d : E) ∧ (d : E) ≠ 0 := by
  have hint : ∀ o : 𝓞 E, IsIntegral ℤ (sig (o : E)) := fun o =>
    (o.isIntegral_coe).map (sig.toRingHom.toIntAlgHom)
  suffices h : ∃ o : 𝓞 E, sig (o : E) ≠ o by
    obtain ⟨o, ho⟩ := h
    refine ⟨o - ⟨sig o, hint o⟩, ?_, ?_⟩
    · change sig ((o : E) - sig o) = -((o : E) - sig o)
      rw [map_sub, sig_sig A]; ring
    · change (o : E) - sig o ≠ 0
      rw [sub_ne_zero]
      exact fun h => ho h.symm
  by_contra hne
  push_neg at hne
  obtain ⟨e, he⟩ := sig_ne A
  obtain ⟨a, s, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
  apply he
  rw [map_div₀]
  exact congrArg₂ (· / ·) (hne a) (hne s)

/- English proof (translation)
Use `haveI := PlacesInt.nontrivial_Ep (A.loc p)`. Rewrite `h` using `[(A.L p).O_def]`. Establish `h2 : IsIntegral 𝒪[(A.loc p).Fp] w` using `(isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep) (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h`. Conclude with `Valuation.Integers.mem_of_integral (Valuation.integer.integers (valuation (A.loc p).Fp)) h2`.
-/
theorem mem_int_of_O (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (w : (A.loc p).Fp)
    (h : algebraMap (A.loc p).Fp (A.loc p).Ep w ∈ (A.L p).O) : w ∈ 𝒪[(A.loc p).Fp] := by
  haveI := PlacesInt.nontrivial_Ep (A.loc p)
  rw [(A.L p).O_def] at h
  have h2 : IsIntegral 𝒪[(A.loc p).Fp] w :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[(A.loc p).Fp] (A.loc p).Fp (A.loc p).Ep)
      (algebraMap (A.loc p).Fp (A.loc p).Ep).injective).1 h
  exact Valuation.Integers.mem_of_integral (Valuation.integer.integers (valuation (A.loc p).Fp)) h2

/- English proof (translation)
Rewrite using `[(A.L p).O_def]`. Conclude with `(isIntegral_algebraMap (x := o)).algebraMap`.
-/
theorem O_of_int (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (o : 𝒪[(A.loc p).Fp]) :
    algebraMap (A.loc p).Fp (A.loc p).Ep (o : (A.loc p).Fp) ∈ (A.L p).O := by
  rw [(A.L p).O_def]
  exact (isIntegral_algebraMap (x := o)).algebraMap

/- English proof (translation)
Rewrite `h`, the goal using `[(A.L p).O_def]`. Conclude with `h.map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])`.
-/
theorem cj_mem (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) (y : (A.loc p).Ep)
    (h : y ∈ (A.L p).O) : (A.L p).cj y ∈ (A.L p).O := by
  rw [(A.L p).O_def] at h ⊢
  exact h.map ((A.L p).cj.toAlgHom.restrictScalars 𝒪[(A.loc p).Fp])

end GlobalTheory.HL.StrongApprox

namespace GlobalTheory.HL.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

/- English proof (translation)
Establish `cjE : ∀ x, (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x)`. Introduce `x`. Rewrite using `[A.L_cj]`. Conclude with `(A.loc p).cj_ιE x`. Take `⟨u, hu⟩` from `((A.L p).cj_fix (y + (A.L p).cj y)).1 (by rw [map_add, (A.L p).cj_cj, add_comm])`.

Take `⟨w, hw⟩` from `((A.L p).cj_fix ((y - (A.L p).cj y) * (A.loc p).ιE d⁻¹)).1 (by`. Rewrite using `[map_mul, map_sub, (A.L p).cj_cj, cjE, map_inv₀, hd, inv_neg, map_neg]`. Use the proof step `ring)`. Establish `hh : algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF 2⁻¹) = (A.loc p).ιE (algebraMap F E 2⁻¹)` using `((A.loc p).compat _).symm`. Establish `e1 : (A.loc p).ιE d⁻¹ * (A.loc p).ιE d = 1`.

Rewrite using `[← map_mul, inv_mul_cancel₀ hd0, map_one]`. Establish `e2 : (A.loc p).ιE (algebraMap F E 2⁻¹) * 2 = 1`. Establish `: algebraMap F E 2⁻¹ * 2 = 1`. Rewrite using `[map_inv₀, map_ofNat]`. Conclude with `inv_mul_cancel₀ two_ne_zero`.

Rewrite using `[← map_ofNat (A.loc p).ιE 2, ← map_mul, this, map_one]`. Use `⟨u * (A.loc p).ιF 2⁻¹, w * (A.loc p).ιF 2⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hu, hw, hh]`. Take the linear combination `(-((A.loc p).ιE (algebraMap F E 2⁻¹) * (y - (A.L p).cj y))) * e1 + (-y) * e2`. Rewrite using `[map_mul, hu, hh, mul_comm]`.

Introduce `hy hdi h2i`. Establish `hcy` using `cj_mem A p y hy`. Use `⟨mul_mem (mem_int_of_O A p u (hu ▸ add_mem hy hcy)) h2i, mul_mem (mem_int_of_O A p w (hw ▸ mul_mem (sub_mem hy hcy) hdi)) h2i⟩` and prove the remaining obligations.
-/
theorem decomp (A : Places F E sig) (d : E) (hd : sig d = -d) (hd0 : d ≠ 0) (p : HeightOneSpectrum (𝓞 F))
    (y : (A.loc p).Ep) : ∃ a b : (A.loc p).Fp,
      y = algebraMap _ _ a + algebraMap _ _ b * (A.loc p).ιE d ∧
      algebraMap _ _ a = (A.loc p).ιE (algebraMap F E 2⁻¹) * (y + (A.L p).cj y) ∧
      (y ∈ (A.L p).O → (A.loc p).ιE d⁻¹ ∈ (A.L p).O → (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] →
        a ∈ 𝒪[(A.loc p).Fp] ∧ b ∈ 𝒪[(A.loc p).Fp]) := by
  have cjE : ∀ x, (A.L p).cj ((A.loc p).ιE x) = (A.loc p).ιE (sig x) := by
    intro x; rw [A.L_cj]; exact (A.loc p).cj_ιE x
  obtain ⟨u, hu⟩ := ((A.L p).cj_fix (y + (A.L p).cj y)).1 (by rw [map_add, (A.L p).cj_cj, add_comm])
  obtain ⟨w, hw⟩ := ((A.L p).cj_fix ((y - (A.L p).cj y) * (A.loc p).ιE d⁻¹)).1 (by
    rw [map_mul, map_sub, (A.L p).cj_cj, cjE, map_inv₀, hd, inv_neg, map_neg]; ring)
  have hh : algebraMap (A.loc p).Fp (A.loc p).Ep ((A.loc p).ιF 2⁻¹) = (A.loc p).ιE (algebraMap F E 2⁻¹) :=
    ((A.loc p).compat _).symm
  have e1 : (A.loc p).ιE d⁻¹ * (A.loc p).ιE d = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hd0, map_one]
  have e2 : (A.loc p).ιE (algebraMap F E 2⁻¹) * 2 = 1 := by
    have : algebraMap F E 2⁻¹ * 2 = 1 := by
      rw [map_inv₀, map_ofNat]; exact inv_mul_cancel₀ two_ne_zero
    rw [← map_ofNat (A.loc p).ιE 2, ← map_mul, this, map_one]
  refine ⟨u * (A.loc p).ιF 2⁻¹, w * (A.loc p).ιF 2⁻¹, ?_, ?_, ?_⟩
  · rw [map_mul, map_mul, hu, hw, hh]
    linear_combination (-((A.loc p).ιE (algebraMap F E 2⁻¹) * (y - (A.L p).cj y))) * e1 + (-y) * e2
  · rw [map_mul, hu, hh, mul_comm]
  · intro hy hdi h2i
    have hcy := cj_mem A p y hy
    refine ⟨mul_mem (mem_int_of_O A p u (hu ▸ add_mem hy hcy)) h2i,
      mul_mem (mem_int_of_O A p w (hw ▸ mul_mem (sub_mem hy hcy) hdi)) h2i⟩

/- English proof (translation)
Use `(HeightOneSpectrum.Support.finite (𝓞 F) (2⁻¹ : F)).subset fun p hp => ?_` and prove the remaining obligations. Establish `hp' : ¬ (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp]` using `hp`. Rewrite `hp'` using `[PlacesInt.mem_int_iff, not_le]`. Conclude with `hp'`.
-/
theorem fin_two (A : Places F E sig) :
    {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]}.Finite := by
  refine (HeightOneSpectrum.Support.finite (𝓞 F) (2⁻¹ : F)).subset fun p hp => ?_
  have hp' : ¬ (A.loc p).ιF 2⁻¹ ∈ 𝒪[(A.loc p).Fp] := hp
  rw [PlacesInt.mem_int_iff, not_le] at hp'
  exact hp'

/- English proof (translation)
Take `⟨d, hd, hd0⟩` from `exists_d A`. Establish `hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O` using `(PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩`. Establish `hdi` using `(PlacesInt.integers_local A).2.1 (d : E)⁻¹`. Use `choose a b hab _ hint using fun p => decomp A d hd hd0 p (y p)`. Establish `hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪ {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} → a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp]`.

Introduce `p hp`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp`. Conclude with `hint p hp.1.1 hp.1.2 hp.2`. Establish `hfin` using `(hy.union hdi).union (fin_two A)`. Take `⟨α, hα⟩` from `approxF A c hc a (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).1)`.

Take `⟨β, hβ⟩` from `approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)`. Use `⟨algebraMap F E α + algebraMap F E β * d, fun p => ?_⟩` and prove the remaining obligations. Take `⟨o1, ho1⟩` from `hα p`. Take `⟨o2, ho2⟩` from `hβ p`. Use `⟨algebraMap _ _ (o1 : (A.loc p).Fp) + algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d, add_mem (O_of_int A p o1) (mul_mem (O_of_int A p o2) (hdO p)), ?_⟩` and prove the remaining obligations.

Establish `e1` using `congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho1`. Establish `e2` using `congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2`. Rewrite `e1`, `e2` using `[map_sub, map_mul]`. Rewrite using `[map_add, map_mul, (A.loc p).compat, (A.loc p).compat]`. Take the linear combination `e1 + (A.loc p).ιE d * e2 - hab p`.
-/
theorem approxE (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (y : ∀ p, (A.loc p).Ep) (hy : {p | y p ∉ (A.L p).O}.Finite) :
    ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  obtain ⟨d, hd, hd0⟩ := exists_d A
  have hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O := (PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩
  have hdi := (PlacesInt.integers_local A).2.1 (d : E)⁻¹
  choose a b hab _ hint using fun p => decomp A d hd hd0 p (y p)
  have hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪
      {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} →
      a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp] := by
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    exact hint p hp.1.1 hp.1.2 hp.2
  have hfin := (hy.union hdi).union (fin_two A)
  obtain ⟨α, hα⟩ := approxF A c hc a (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).1)
  obtain ⟨β, hβ⟩ := approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)
  refine ⟨algebraMap F E α + algebraMap F E β * d, fun p => ?_⟩
  obtain ⟨o1, ho1⟩ := hα p
  obtain ⟨o2, ho2⟩ := hβ p
  refine ⟨algebraMap _ _ (o1 : (A.loc p).Fp) + algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d,
    add_mem (O_of_int A p o1) (mul_mem (O_of_int A p o2) (hdO p)), ?_⟩
  have e1 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho1
  have e2 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2
  rw [map_sub, map_mul] at e1 e2
  rw [map_add, map_mul, (A.loc p).compat, (A.loc p).compat]
  linear_combination e1 + (A.loc p).ιE d * e2 - hab p

/- English proof (translation)
Take `⟨d, hd, hd0⟩` from `exists_d A`. Establish `hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O` using `(PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩`. Establish `hdi` using `(PlacesInt.integers_local A).2.1 (d : E)⁻¹`. Establish `ht : sig t = t`. Take `⟨p⟩` from `exists_place F`.

Use `haveI := PlacesInt.nontrivial_Ep (A.loc p)`. Apply `(A.loc p).ιE.injective` to reduce the goal to its premises. Rewrite using `[← (A.loc p).cj_ιE, ← A.L_cj, ← hyt p, map_add, (A.L p).cj_cj, add_comm]`. Use `choose a b hab hA hint using fun p => decomp A d hd hd0 p (y p)`. Establish `hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪ {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} → a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp]`.

Introduce `p hp`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp`. Conclude with `hint p hp.1.1 hp.1.2 hp.2`. Establish `hfin` using `(hy.union hdi).union (fin_two A)`. Take `⟨β, hβ⟩` from `approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)`.

Use `⟨algebraMap F E 2⁻¹ * t + algebraMap F E β * d, ?_, fun p => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, ht, hd, map_inv₀, map_ofNat]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨o2, ho2⟩` from `hβ p`.

Use `⟨algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d, mul_mem (O_of_int A p o2) (hdO p), ?_⟩` and prove the remaining obligations. Establish `e2` using `congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2`. Rewrite `e2` using `[map_sub, map_mul]`. Rewrite using `[map_add, map_mul, map_mul, (A.loc p).compat β]`. Take the linear combination `(A.loc p).ιE d * e2 - hab p - hA p - (A.loc p).ιE (algebraMap F E 2⁻¹) * hyt p`.
-/
theorem approxTr (A : Places F E sig) (c : ∀ p, ((A.loc p).Fp)ˣ)
    (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
    (t : E) (y : ∀ p, (A.loc p).Ep) (hy : {p | y p ∉ (A.L p).O}.Finite)
    (hyt : ∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) :
    ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O,
      (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  obtain ⟨d, hd, hd0⟩ := exists_d A
  have hdO : ∀ p, (A.loc p).ιE (d : E) ∈ (A.L p).O := (PlacesInt.integers_local A).1 _ |>.2 ⟨d, rfl⟩
  have hdi := (PlacesInt.integers_local A).2.1 (d : E)⁻¹
  have ht : sig t = t := by
    obtain ⟨p⟩ := exists_place F
    haveI := PlacesInt.nontrivial_Ep (A.loc p)
    apply (A.loc p).ιE.injective
    rw [← (A.loc p).cj_ιE, ← A.L_cj, ← hyt p, map_add, (A.L p).cj_cj, add_comm]
  choose a b hab hA hint using fun p => decomp A d hd hd0 p (y p)
  have hbad : ∀ p, p ∉ {p | y p ∉ (A.L p).O} ∪ {p | (A.loc p).ιE (d : E)⁻¹ ∉ (A.L p).O} ∪
      {p : HeightOneSpectrum (𝓞 F) | (A.loc p).ιF 2⁻¹ ∉ 𝒪[(A.loc p).Fp]} →
      a p ∈ 𝒪[(A.loc p).Fp] ∧ b p ∈ 𝒪[(A.loc p).Fp] := by
    intro p hp
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hp
    exact hint p hp.1.1 hp.1.2 hp.2
  have hfin := (hy.union hdi).union (fin_two A)
  obtain ⟨β, hβ⟩ := approxF A c hc b (hfin.subset fun p hp => by_contra fun h => hp (hbad p h).2)
  refine ⟨algebraMap F E 2⁻¹ * t + algebraMap F E β * d, ?_, fun p => ?_⟩
  · rw [map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, ht, hd, map_inv₀, map_ofNat]
    field_simp
    ring
  obtain ⟨o2, ho2⟩ := hβ p
  refine ⟨algebraMap _ _ (o2 : (A.loc p).Fp) * (A.loc p).ιE d, mul_mem (O_of_int A p o2) (hdO p), ?_⟩
  have e2 := congrArg (algebraMap (A.loc p).Fp (A.loc p).Ep) ho2
  rw [map_sub, map_mul] at e2
  rw [map_add, map_mul, map_mul, (A.loc p).compat β]
  linear_combination (A.loc p).ιE d * e2 - hab p - hA p - (A.loc p).ιE (algebraMap F E 2⁻¹) * hyt p

/- English proof (translation)
Introduce `F E _ _ _ _ _ sig A c hc`. Conclude with `⟨fun y hy => approxF A c hc y hy, fun y hy => approxE A c hc y hy, fun t y hy hyt => approxTr A c hc t y hy hyt⟩`.
-/
theorem strong_approx_additive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → (∀ y : ∀ p, (A.loc p).Fp, {p | y p ∉ 𝒪[(A.loc p).Fp]}.Finite → ∃ x : F, ∀ p, ∃ o : 𝒪[(A.loc p).Fp], (A.loc p).ιF x - y p = c p * o) ∧ (∀ y : ∀ p, (A.loc p).Ep, {p | y p ∉ (A.L p).O}.Finite → ∃ x : E, ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o) ∧ ∀ (t : E) (y : ∀ p, (A.loc p).Ep), {p | y p ∉ (A.L p).O}.Finite → (∀ p, y p + (A.L p).cj (y p) = (A.loc p).ιE t) → ∃ x : E, x + sig x = t ∧ ∀ p, ∃ o ∈ (A.L p).O, (A.loc p).ιE x - y p = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) * o := by
  intro F E _ _ _ _ _ sig A c hc
  exact ⟨fun y hy => approxF A c hc y hy, fun y hy => approxE A c hc y hy,
    fun t y hy hyt => approxTr A c hc t y hy hyt⟩

end GlobalTheory.HL.StrongApprox
