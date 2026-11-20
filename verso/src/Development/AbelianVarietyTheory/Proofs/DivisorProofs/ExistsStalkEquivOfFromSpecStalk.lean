import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanPairIsPrimeHeightTwoOfCotangentIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVaniStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncMeet

open IsLocalRing

/- English proof (translation)
Take `⟨e, he⟩` from `GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x p.asIdeal`. Establish `hs : X.fromSpecStalk x p ⤳ x`. Establish `: X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x)` using `⟨p, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Use `⟨hs, e, ?_⟩` and prove the remaining obligations.

Establish `hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal))`. Apply `TopCat.Presheaf.stalk_hom_ext` to reduce the goal to its premises. Introduce `U hxU`. Use extensionality with `s`. Establish `h3` using `congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3`. Express the relevant statement in the definitionally equal form `e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) = algebraMap _ (Localization.AtPrime p.asIdeal) ((X.presheaf.germ U _ hxU).hom s)`. Rewrite using `[h3]`. Conclude with `he U _ hxU s`. Introduce `g`.

Conclude with `congrArg (fun f => f.hom g) hcomp`.
-/
theorem exists_stalk_equiv_of_fromSpecStalk (X : Scheme.{0}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ (h : X.fromSpecStalk x p ⤳ x)
      (e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal),
      ∀ g, e ((X.presheaf.stalkSpecializes h).hom g) = algebraMap _ _ g := by
  obtain ⟨e, he⟩ := GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x p.asIdeal
  have hs : X.fromSpecStalk x p ⤳ x := by
    have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hs, e, ?_⟩
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime p.asIdeal) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  intro g
  exact congrArg (fun f => f.hom g) hcomp

/- English proof (translation)
Substitute `hp` using the available equality. Take `⟨h, e, he⟩` from `exists_stalk_equiv_of_fromSpecStalk X x p`. Establish `h1 : g ∈ p.asIdeal ↔ algebraMap _ (Localization.AtPrime p.asIdeal) g ∈ maximalIdeal (Localization.AtPrime p.asIdeal)`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal) p.asIdeal g).symm`. Rewrite using `[h1, ← he g, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, MulEquiv.isUnit_map]`.
-/
theorem mem_asIdeal_iff (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) (y : X)
    (hy : y ⤳ x) (hp : X.fromSpecStalk x p = y) (g : X.presheaf.stalk x) :
    g ∈ p.asIdeal ↔ (X.presheaf.stalkSpecializes hy).hom g ∈ maximalIdeal (X.presheaf.stalk y) := by
  subst hp
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 : g ∈ p.asIdeal ↔ algebraMap _ (Localization.AtPrime p.asIdeal) g ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal) p.asIdeal g).symm
  rw [h1, ← he g, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MulEquiv.isUnit_map]

/- English proof (translation)
Take `⟨h, e, he⟩` from `exists_stalk_equiv_of_fromSpecStalk X x p`. Establish `h1` using `ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)`. Rewrite `h1` using `[ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal]`. Conclude with `h1.symm` after adjusting the coercions.
-/
theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

/- English proof (translation)
Distinguish the cases in `hx : Order.coheight x = 1`. Establish `hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg.ne_zero`. Rewrite using `[Scheme.ord_eq_iff hx hne]`. Use `haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le`. Express the relevant statement in the definitionally equal form `Ring.ordFrac _ _ = _`.

Rewrite using `[Ring.ordFrac_of_isUnit hg]`. Both sides reduce to the same expression. Conclude with `Scheme.ord_eq_zero_of_coheight_neq_one hx _`.
-/
theorem ord_algebraMap_of_isUnit (x : X) (g : X.presheaf.stalk x) (hg : IsUnit g) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg.ne_zero
    rw [Scheme.ord_eq_iff hx hne]
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Ring.ordFrac _ _ = _
    rw [Ring.ordFrac_of_isUnit hg]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

/- English proof (translation)
Use `haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le`. Establish `hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg0`. Introduce `h0`. Rewrite `h0` using `[Scheme.ord_eq_iff hx hne]`. Express the relevant statement in the definitionally equal form `Ring.ordFrac _ _ = _ at h0`.

Rewrite `h0` using `[Ring.ordFrac_eq_ord _ hg0]`. Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0))`. Rewrite `h0` using `[Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0) hm.symm]`. Establish `hm0 : m = 0`. Establish `h4 : (m : ℤ) = 0` using `Multiplicative.ofAdd.injective (WithZero.coe_injective h0)`.

Conclude with `h4` after adjusting the coercions. Substitute `hm0` using the available equality. Establish `h2 : Ring.ord (X.presheaf.stalk x) g = 0` using `by rw [← hm]; rfl`. Rewrite `h2` using `[Ring.ord]`. Rewrite `h2` using `[Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]`.

Conclude with `(mem_maximalIdeal g).1 hg h2`.
-/
theorem ord_algebraMap_ne_zero (x : X) (hx : Order.coheight x = 1) (g : X.presheaf.stalk x)
    (hg0 : g ≠ 0) (hg : g ∈ maximalIdeal (X.presheaf.stalk x)) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x ≠ 0 := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg0
  intro h0
  rw [Scheme.ord_eq_iff hx hne] at h0
  change Ring.ordFrac _ _ = _ at h0
  rw [Ring.ordFrac_eq_ord _ hg0] at h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0))
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0) hm.symm] at h0
  have hm0 : m = 0 := by
    have h4 : (m : ℤ) = 0 := Multiplicative.ofAdd.injective (WithZero.coe_injective h0)
    exact_mod_cast h4
  subst hm0
  have h2 : Ring.ord (X.presheaf.stalk x) g = 0 := by rw [← hm]; rfl
  rw [Ring.ord] at h2
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h2
  exact (mem_maximalIdeal g).1 hg h2

open IsLocalRing in

/- English proof (translation)
Introduce `Y _ _ q n _ B hB v σ w hvB hσB hv hσ hvσ hvw hσw`. Take `⟨U, hwU, z, J, wf, uf, hc⟩` from `GlobalTheory.T.exists_snc_chart ℂ Y q n B hB w`. Take `⟨j', hj'J, rfl⟩` from `(hc.mem v hvw hv).1 hvB`. Take `⟨j, hjJ, rfl⟩` from `(hc.mem σ hσw hσ).1 hσB`. Establish `hjj : j ≠ j'` using `fun h => hvσ (by rw [h])`.

Use `haveI : IsRegularLocalRing (Y.presheaf.stalk w) := (hB w).1`. Establish `hUmem : ∀ y : Y, y ⤳ w → y ∈ U` using `fun y hy => hy.mem_open U.isOpen hwU`. Establish `hgerm : ∀ (y : Y) (hy : y ⤳ w) (i : Fin n), (Y.presheaf.stalkSpecializes hy).hom (Y.presheaf.germ U w hwU (z i)) = Y.presheaf.germ U y (hUmem y hy) (z i)` using `fun y hy i => by`. Rewrite using `[← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hwU hy]`. Both sides reduce to the same expression.

Establish `hfn : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (z i)) = (uf i : Y.functionField)` using `fun y hy i hi => by`. Rewrite using `[GlobalTheory.Cartier.algebraMap_germ hy, hc.val i hi]`. Establish `hgne : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → Y.presheaf.germ U y hy (z i) ≠ 0` using `fun y hy i hi h0 => (uf i).ne_zero (by rw [← hfn y hy i hi, h0, map_zero])`. Establish `hmy : ∀ i (hi : i ∈ J), Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i) ∈ maximalIdeal (Y.presheaf.stalk (wf i))`. Introduce `i hi`.

Assume the negation of the conclusion as `hnm`. Establish `hu : IsUnit (Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i))`. Assume the negation of the conclusion as `h'`. Conclude with `hnm ((mem_maximalIdeal _).2 h')`. Establish `h1` using `GlobalTheory.SncMeet.ord_algebraMap_of_isUnit _ _ hu`.

Rewrite `h1` using `[hfn _ _ i hi, hc.ord_self i hi]`. Conclude with `one_ne_zero h1`. Establish `hm : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ maximalIdeal (Y.presheaf.stalk w)`. Introduce `i hi`. Assume the negation of the conclusion as `hnm`.

Establish `hu : IsUnit (Y.presheaf.germ U w hwU (z i))`. Assume the negation of the conclusion as `h'`. Conclude with `hnm ((mem_maximalIdeal _).2 h')`. Establish `hu'` using `hu.map (Y.presheaf.stalkSpecializes (hc.spec i hi)).hom`. Rewrite `hu'` using `[hgerm]`.

Conclude with `(mem_maximalIdeal _).1 (hmy i hi) hu'`. Establish `hli` using `GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hc.frame w hwU J (fun i => hm i.1 i.2)`. Establish `hi2 : Function.Injective (![⟨j, hjJ⟩, ⟨j', hj'J⟩] : Fin 2 → J)`. Introduce `k l hkl`. Apply the tactic sequence `fin_cases k <;> fin_cases l`.

Both sides reduce to the same expression. Conclude with `(hjj (by simpa using congrArg Subtype.val hkl)).elim`. Conclude with `(hjj (by simpa using (congrArg Subtype.val hkl).symm)).elim`. Both sides reduce to the same expression. Establish `hli2` using `hli.comp _ hi2`.

Take `⟨hPp, hPh⟩` from `GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent (Y.presheaf.stalk w) (Y.presheaf.germ U w hwU (z j)) (Y.presheaf.germ U w hwU (z j')) (hm j hjJ) (hm j' hj'J) (by`. Use `hli2 using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext k; fin_cases k <;> rfl)`. Set `pt : PrimeSpectrum (Y.presheaf.stalk w)` to `⟨Ideal.span {Y.presheaf.germ U w hwU (z j), Y.presheaf.germ U w hwU (z j')}, hPp⟩`. Take `⟨hw', e, he⟩` from `GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pt`.

Establish `K1 : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal → wf i ⤳ Y.fromSpecStalk w pt`. Introduce `i hi hiP`. Take `⟨Q, hQmin, hQle⟩` from `Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).2 hiP)`. Establish `hQp : Q.IsPrime` using `hQmin.1.1`. Establish `hbQ : Y.presheaf.germ U w hwU (z i) ∈ Q` using `hQmin.1.2 (Ideal.mem_span_singleton_self _)`.

Establish `hQh1 : Q.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin`. Establish `hQ0 : Q ≠ ⊥` using `fun h => hgne w hwU i hi (by rw [h] at hbQ; exact Ideal.mem_bot.1 hbQ)`. Establish `hQh : Q.height = 1`. Use `le_antisymm hQh1 ?_` and prove the remaining obligations. Rewrite using `[ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]`.

Conclude with `hQ0`. Set `pQ : PrimeSpectrum (Y.presheaf.stalk w)` to `⟨Q, hQp⟩`. Take `⟨hQw, -, -⟩` from `GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pQ`. Establish `hcoh : Order.coheight (Y.fromSpecStalk w pQ) = 1`. Rewrite using `[GlobalTheory.SncMeet.coheight_fromSpecStalk]`.

Conclude with `hQh` after adjusting the coercions. Establish `hsp : Y.fromSpecStalk w pQ ⤳ Y.fromSpecStalk w pt` using `((PrimeSpectrum.le_iff_specializes pQ pt).1 hQle).map (Y.fromSpecStalk w).continuous`. Establish `hmem : Y.presheaf.germ U _ (hUmem _ hQw) (z i) ∈ maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk w pQ))`. Rewrite using `[← hgerm _ hQw i]`. Conclude with `(GlobalTheory.SncMeet.mem_asIdeal_iff Y w pQ _ hQw rfl _).1 hbQ`.

Establish `hord` using `GlobalTheory.SncMeet.ord_algebraMap_ne_zero _ hcoh _ (hgne _ _ i hi) hmem`. Rewrite `hord` using `[hfn _ _ i hi]`. Establish `heq : Y.fromSpecStalk w pQ = wf i`. Assume the negation of the conclusion as `hne`. Conclude with `hord (hc.ord_other i hi _ hQw hne)`.

Rewrite using `[← heq]`. Conclude with `hsp`. Establish `hPh' : pt.asIdeal.height = 2` using `hPh`. Establish `ht : ∀ g, (Y.presheaf.stalkSpecializes hw').hom g = e.symm (algebraMap _ (Localization.AtPrime pt.asIdeal) g)` using `fun g => by`. Rewrite using `[← he g, RingEquiv.symm_apply_apply]`.

Use `⟨Y.fromSpecStalk w pt, (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)), (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j')), hw', K1 j' hj'J (Ideal.subset_span (by simp)), K1 j hjJ (Ideal.subset_span (by simp)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ringKrullDim_eq_of_ringEquiv e, IsLocalization.AtPrime.ringKrullDim_eq_height pt.asIdeal, hPh']`. Both sides reduce to the same expression. Establish `h1 : Ideal.span {(Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)), (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j'))} = Ideal.map e.symm (Ideal.map (algebraMap _ (Localization.AtPrime pt.asIdeal)) pt.asIdeal)`. Rewrite using `[ht, ht]`.

Use `show _ = Ideal.map e.symm (Ideal.map _ (Ideal.span _))`. Simplify using `only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]`. Rewrite using `[h1, Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.symm)`. Rewrite using `[hgerm _ hw' j, hfn _ _ j hjJ]`.

Conclude with `hc.ord_self j hjJ`. Rewrite using `[hgerm _ hw' j', hfn _ _ j' hj'J]`. Conclude with `hc.ord_self j' hj'J`. Introduce `v' hv'B hv'1 hv'w'`. Establish `hv'w` using `hv'w'.trans hw'`.

Take `⟨i, hi, rfl⟩` from `(hc.mem v' hv'w hv'1).1 hv'B`. Assume the negation of the conclusion as `hcon`. Rewrite `hcon` using `[not_or]`. Establish `hij' : i ≠ j'` using `fun h => hcon.1 (by rw [h])`. Establish `hij : i ≠ j` using `fun h => hcon.2 (by rw [h])`.

Choose the witnesses or unpack the hypotheses as in `⟨pi, hpi⟩ : wf i ∈ Set.range (Y.fromSpecStalk w) := by`. Rewrite using `[Scheme.range_fromSpecStalk]`. Conclude with `hv'w`. Establish `hle : pi.asIdeal ≤ pt.asIdeal`. Establish `h1 : Y.fromSpecStalk w pi ⤳ Y.fromSpecStalk w pt` using `hpi ▸ hv'w'`.

Conclude with `(PrimeSpectrum.le_iff_specializes pi pt).2 ((IsPreimmersion.isEmbedding (Y.fromSpecStalk w)).specializes_iff.1 h1)`. Establish `hciP : Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal`. Apply `hle` to reduce the goal to its premises. Rewrite using `[GlobalTheory.SncMeet.mem_asIdeal_iff Y w pi (wf i) (hc.spec i hi) hpi, hgerm]`. Conclude with `hmy i hi`.

Take `⟨r, s, hrs⟩` from `Ideal.mem_span_pair.1 hciP`. Use `hli.notMem_span_image (s := {⟨j, hjJ⟩, ⟨j', hj'J⟩}) (x := ⟨i, hi⟩) ?_ ?_` and prove the remaining obligations. Simplify using `[Subtype.ext_iff, hij, hij']`. Establish `hsum : (⟨Y.presheaf.germ U w hwU (z i), hm i hi⟩ : maximalIdeal (Y.presheaf.stalk w)) = r • ⟨Y.presheaf.germ U w hwU (z j), hm j hjJ⟩ + s • ⟨Y.presheaf.germ U w hwU (z j'), hm j' hj'J⟩` using `by ext; simp [← hrs, smul_eq_mul] show (maximalIdeal _).toCotangent ⟨_, _⟩ ∈ _`. Rewrite using `[hsum, map_add, map_smul, map_smul]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_of_tower_mem _ r (Submodule.subset_span ⟨⟨j, hjJ⟩, by simp, rfl⟩)) (Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨⟨j', hj'J⟩, by simp, rfl⟩))`.
-/
theorem exists_meet_point : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ v σ w : Y, v ∈ B → σ ∈ B → Order.coheight v = 1 → Order.coheight σ = 1 → v ≠ σ → v ⤳ w → σ ⤳ w → ∃ (w' : Y) (t u : Y.presheaf.stalk w'), w' ⤳ w ∧ v ⤳ w' ∧ σ ⤳ w' ∧ ringKrullDim (Y.presheaf.stalk w') = 2 ∧ Ideal.span {t, u} = IsLocalRing.maximalIdeal (Y.presheaf.stalk w') ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField t) σ = 1 ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField u) v = 1 ∧ ∀ v' ∈ B, Order.coheight v' = 1 → v' ⤳ w' → v' = v ∨ v' = σ := by
  classical
  intro Y _ _ q n _ B hB v σ w hvB hσB hv hσ hvσ hvw hσw
  obtain ⟨U, hwU, z, J, wf, uf, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB w
  obtain ⟨j', hj'J, rfl⟩ := (hc.mem v hvw hv).1 hvB
  obtain ⟨j, hjJ, rfl⟩ := (hc.mem σ hσw hσ).1 hσB
  have hjj : j ≠ j' := fun h => hvσ (by rw [h])
  haveI : IsRegularLocalRing (Y.presheaf.stalk w) := (hB w).1
  have hUmem : ∀ y : Y, y ⤳ w → y ∈ U := fun y hy => hy.mem_open U.isOpen hwU
  have hgerm : ∀ (y : Y) (hy : y ⤳ w) (i : Fin n),
      (Y.presheaf.stalkSpecializes hy).hom (Y.presheaf.germ U w hwU (z i)) =
        Y.presheaf.germ U y (hUmem y hy) (z i) := fun y hy i => by
    rw [← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hwU hy]; rfl
  have hfn : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J →
      algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (z i)) =
        (uf i : Y.functionField) := fun y hy i hi => by
    rw [GlobalTheory.Cartier.algebraMap_germ hy, hc.val i hi]
  have hgne : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → Y.presheaf.germ U y hy (z i) ≠ 0 :=
    fun y hy i hi h0 => (uf i).ne_zero (by rw [← hfn y hy i hi, h0, map_zero])
  have hmy : ∀ i (hi : i ∈ J), Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i) ∈
      maximalIdeal (Y.presheaf.stalk (wf i)) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have h1 := GlobalTheory.SncMeet.ord_algebraMap_of_isUnit _ _ hu
    rw [hfn _ _ i hi, hc.ord_self i hi] at h1
    exact one_ne_zero h1
  have hm : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ maximalIdeal (Y.presheaf.stalk w) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U w hwU (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have hu' := hu.map (Y.presheaf.stalkSpecializes (hc.spec i hi)).hom
    rw [hgerm] at hu'
    exact (mem_maximalIdeal _).1 (hmy i hi) hu'
  have hli := GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hc.frame w hwU J (fun i => hm i.1 i.2)

  have hi2 : Function.Injective (![⟨j, hjJ⟩, ⟨j', hj'J⟩] : Fin 2 → J) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hjj (by simpa using congrArg Subtype.val hkl)).elim
    · exact (hjj (by simpa using (congrArg Subtype.val hkl).symm)).elim
    · rfl
  have hli2 := hli.comp _ hi2
  obtain ⟨hPp, hPh⟩ := GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent (Y.presheaf.stalk w) (Y.presheaf.germ U w hwU (z j))
    (Y.presheaf.germ U w hwU (z j')) (hm j hjJ) (hm j' hj'J) (by
      convert hli2 using 1
      funext k; fin_cases k <;> rfl)
  let pt : PrimeSpectrum (Y.presheaf.stalk w) :=
    ⟨Ideal.span {Y.presheaf.germ U w hwU (z j), Y.presheaf.germ U w hwU (z j')}, hPp⟩
  obtain ⟨hw', e, he⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pt
  have K1 : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal →
      wf i ⤳ Y.fromSpecStalk w pt := by
    intro i hi hiP
    obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).2 hiP)
    have hQp : Q.IsPrime := hQmin.1.1
    have hbQ : Y.presheaf.germ U w hwU (z i) ∈ Q := hQmin.1.2 (Ideal.mem_span_singleton_self _)
    have hQh1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin
    have hQ0 : Q ≠ ⊥ := fun h => hgne w hwU i hi (by rw [h] at hbQ; exact Ideal.mem_bot.1 hbQ)
    have hQh : Q.height = 1 := by
      refine le_antisymm hQh1 ?_
      rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hQ0
    let pQ : PrimeSpectrum (Y.presheaf.stalk w) := ⟨Q, hQp⟩
    obtain ⟨hQw, -, -⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pQ
    have hcoh : Order.coheight (Y.fromSpecStalk w pQ) = 1 := by
      rw [GlobalTheory.SncMeet.coheight_fromSpecStalk]; exact_mod_cast hQh
    have hsp : Y.fromSpecStalk w pQ ⤳ Y.fromSpecStalk w pt :=
      ((PrimeSpectrum.le_iff_specializes pQ pt).1 hQle).map (Y.fromSpecStalk w).continuous
    have hmem : Y.presheaf.germ U _ (hUmem _ hQw) (z i) ∈
        maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk w pQ)) := by
      rw [← hgerm _ hQw i]; exact (GlobalTheory.SncMeet.mem_asIdeal_iff Y w pQ _ hQw rfl _).1 hbQ
    have hord := GlobalTheory.SncMeet.ord_algebraMap_ne_zero _ hcoh _ (hgne _ _ i hi) hmem
    rw [hfn _ _ i hi] at hord
    have heq : Y.fromSpecStalk w pQ = wf i := by
      by_contra hne; exact hord (hc.ord_other i hi _ hQw hne)
    rw [← heq]; exact hsp
  have hPh' : pt.asIdeal.height = 2 := hPh
  have ht : ∀ g, (Y.presheaf.stalkSpecializes hw').hom g =
      e.symm (algebraMap _ (Localization.AtPrime pt.asIdeal) g) := fun g => by
    rw [← he g, RingEquiv.symm_apply_apply]
  refine ⟨Y.fromSpecStalk w pt, (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
    (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j')), hw',
    K1 j' hj'J (Ideal.subset_span (by simp)), K1 j hjJ (Ideal.subset_span (by simp)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height pt.asIdeal, hPh']
    rfl
  · have h1 : Ideal.span {(Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
        (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j'))} =
        Ideal.map e.symm (Ideal.map (algebraMap _ (Localization.AtPrime pt.asIdeal)) pt.asIdeal) := by
      rw [ht, ht]
      show _ = Ideal.map e.symm (Ideal.map _ (Ideal.span _))
      simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [h1, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.symm)
  · rw [hgerm _ hw' j, hfn _ _ j hjJ]; exact hc.ord_self j hjJ
  · rw [hgerm _ hw' j', hfn _ _ j' hj'J]; exact hc.ord_self j' hj'J
  · intro v' hv'B hv'1 hv'w'
    have hv'w := hv'w'.trans hw'
    obtain ⟨i, hi, rfl⟩ := (hc.mem v' hv'w hv'1).1 hv'B
    by_contra hcon
    rw [not_or] at hcon
    have hij' : i ≠ j' := fun h => hcon.1 (by rw [h])
    have hij : i ≠ j := fun h => hcon.2 (by rw [h])
    obtain ⟨pi, hpi⟩ : wf i ∈ Set.range (Y.fromSpecStalk w) := by
      rw [Scheme.range_fromSpecStalk]; exact hv'w
    have hle : pi.asIdeal ≤ pt.asIdeal := by
      have h1 : Y.fromSpecStalk w pi ⤳ Y.fromSpecStalk w pt := hpi ▸ hv'w'
      exact (PrimeSpectrum.le_iff_specializes pi pt).2
        ((IsPreimmersion.isEmbedding (Y.fromSpecStalk w)).specializes_iff.1 h1)
    have hciP : Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal := by
      apply hle
      rw [GlobalTheory.SncMeet.mem_asIdeal_iff Y w pi (wf i) (hc.spec i hi) hpi, hgerm]
      exact hmy i hi
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hciP
    refine hli.notMem_span_image (s := {⟨j, hjJ⟩, ⟨j', hj'J⟩}) (x := ⟨i, hi⟩) ?_ ?_
    · simp [Subtype.ext_iff, hij, hij']
    · have hsum : (⟨Y.presheaf.germ U w hwU (z i), hm i hi⟩ : maximalIdeal (Y.presheaf.stalk w)) =
          r • ⟨Y.presheaf.germ U w hwU (z j), hm j hjJ⟩ +
            s • ⟨Y.presheaf.germ U w hwU (z j'), hm j' hj'J⟩ := by
        ext; simp [← hrs, smul_eq_mul]
      show (maximalIdeal _).toCotangent ⟨_, _⟩ ∈ _
      rw [hsum, map_add, map_smul, map_smul]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ r (Submodule.subset_span ⟨⟨j, hjJ⟩, by simp, rfl⟩))
        (Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨⟨j', hj'J⟩, by simp, rfl⟩))

end GlobalTheory.SncMeet
