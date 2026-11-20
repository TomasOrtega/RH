import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace SemiampleNefAlt

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hI : (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)).IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) ≠ 0`. Introduce `h0`. Apply `h` to reduce the goal to its premises. Unfold `ReciprocityTheory.ChartRestriction.G.Geo.charOf`.

Rewrite using `[h0]`. Both sides reduce to the same expression. Rewrite `hI` using `[← Submodule.IsPrincipal.span_singleton_generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι))]`. Conclude with `Int.prime_iff_natAbs_prime.mp ((Ideal.span_singleton_prime hg).mp hI)`.
-/
theorem charOf_prime {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} [W.IsPrime]
    (h : ReciprocityTheory.ChartRestriction.G.Geo.charOf W ≠ 0) : (ReciprocityTheory.ChartRestriction.G.Geo.charOf W).Prime := by
  have hI : (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)).IsPrime := Ideal.comap_isPrime _ _
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) ≠ 0 := by
    intro h0
    apply h
    unfold ReciprocityTheory.ChartRestriction.G.Geo.charOf
    rw [h0]
    rfl
  rw [← Submodule.IsPrincipal.span_singleton_generator
    (W.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι))] at hI
  exact Int.prime_iff_natAbs_prime.mp ((Ideal.span_singleton_prime hg).mp hI)

/- English proof (translation)
Use extensionality with `d`. Simplify using `only [coeff_weightedHomogeneousComponent, coeff_map]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_weightedHomogeneousComponent [DecidableEq K] (p : ℕ) (c : K → ℕ)
    (f : MvPolynomial (Σ k, ι k) ℤ) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
        (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight ι) c
        (MvPolynomial.map (Int.castRingHom (ZMod p)) f) := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, coeff_map]
  split_ifs <;> simp

open GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum GroundTheory.Heights₂.Heights.NumbersDVR
  GroundTheory.Heights₂.Heights.FieldNumbers in

/- English proof (translation)
Use `set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf W with hp_def`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ W` using `Inter.C_charOf_mem W`. Establish `hker : RingHom.ker (red (ι` using `ι) p) ≤ W := by`. Rewrite using `[ker_red, Ideal.span_le, Set.singleton_subset_iff]`.

Conclude with `hpV`. Establish `hcm : (W.map (red p)).comap (red p) = W` using `comap_map_eq p hker`. Establish `: W.IsPrime` using `hW.1`. Establish `hQ : IsMultiProjPrime (W.map (red p))`. Use `⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[isMultiHomogIdeal_iff]`. Take `⟨S, hS, hVS⟩` from `hW.2.1`. Use `⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨c, hc⟩` from `hS f hf`.

Conclude with `⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩`. Rewrite using `[← isRelevant_comap_iff p, hcm]`. Conclude with `hW.2.2`. Establish `hd : relDim (W.map (red p)) = ((0 + 1 : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[CutRegular.relDim_eq_natCast_iff]`.

Use `ringKrullDim_eq_of_ringEquiv (quotEquiv p (W.map (red p)))` as an intermediate fact. Rewrite `this` using `[hcm, hdim]`. Rewrite using `[← this]`. Establish `htr : IsMultiHomog (red p t) b`. Rewrite using `[isMultiHomog_iff]`.

Conclude with `fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k`. Establish `htrV : red p t ∉ W.map (red p)`. Introduce `h`. Apply `htW` to reduce the goal to its premises. Rewrite using `[← hcm]`.

Conclude with `h`. Take `⟨hUmin, hUrel⟩` from `hU`. Establish `hJ : W ⊔ Ideal.span {t} = (W.map (red p) ⊔ Ideal.span {red p t}).comap (red p)`. Rewrite using `[← Set.image_singleton, ← comap_sup_span p (W.map (red p)) {t}, hcm]`. Rewrite `hUmin` using `[hJ, Ideal.comap_minimalPrimes_eq_of_surjective (red_surjective p)]`.

Take `⟨U', hU'min, rfl⟩` from `hUmin`. Establish `: U'.IsPrime` using `hU'min.1.1`. Establish `hU'rel : IsRelevant U'` using `(isRelevant_comap_iff p U').mp hUrel`. Establish `h0 : divCycle (W.map (red p)) (red p t) U' ≠ 0`. Unfold `divCycle`.

Rewrite using `[dif_pos ⟨hU'min, hU'rel⟩]`. Establish `hne_top` using `length_localizedQuot_ne_top _ U' hU'min`. Establish `hne_zero : NumbersDVR.multAt (W.map (red p) ⊔ Ideal.span {red p t}) U' ≠ 0`. Unfold `NumbersDVR.multAt`. Rewrite using `[Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]`.

Introduce `hall`. Take `⟨r, hr, hr0⟩` from `hall (Ideal.Quotient.mk _ 1)`. Rewrite `hr0` using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hr (hU'min.1.2 hr0)`. Introduce `hz`.

Rewrite `hz` using `[Nat.cast_eq_zero, ENat.toNat_eq_zero]`. Conclude with `hz.elim hne_zero hne_top`. Take `⟨hmp, hrd⟩` from `DivCycleSupport.full (ZMod p) K ι (W.map (red p)) hQ 0 hd b (red p t) htr htrV U' h0`. Use `⟨⟨Ideal.comap_isPrime _ _, ?_, (isRelevant_comap_iff p U').mpr hmp.relevant⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← isMultiHomogIdeal_iff]`.

Introduce `f hf c`. Rewrite `hf`, the goal using `[Ideal.mem_comap]`. Rewrite using `[map_weightedHomogeneousComponent]`. Conclude with `hmp.multiHomog _ hf c`. Rewrite using `[ringKrullDim_eq_of_ringEquiv (quotEquiv p U'), (CutRegular.relDim_eq_natCast_iff U' 0).mp hrd, zero_add]`.
-/
theorem isClosedPt_of_mem_divSupp {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)}
    (hW : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime W) (hp : (ReciprocityTheory.ChartRestriction.G.Geo.charOf W).Prime)
    (hdim : ringKrullDim (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {t : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {b : K → ℕ} (ht : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog t b)
    (htW : t ∉ W) {U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} (hU : U ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp W t) :
    GroundTheory.Heights₂.Heights.Inter.IsClosedPt U := by
  classical
  set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf W with hp_def
  have : Fact p.Prime := ⟨hp⟩
  have hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ W := Inter.C_charOf_mem W
  have hker : RingHom.ker (red (ι := ι) p) ≤ W := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (W.map (red p)).comap (red p) = W := comap_map_eq p hker
  have : W.IsPrime := hW.1
  have hQ : IsMultiProjPrime (W.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hW.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hS f hf
      exact ⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hW.2.2
  have hd : relDim (W.map (red p)) = ((0 + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (W.map (red p)))
    rw [hcm, hdim] at this
    rw [← this]
  have htr : IsMultiHomog (red p t) b := by
    rw [isMultiHomog_iff]
    exact fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k
  have htrV : red p t ∉ W.map (red p) := by
    intro h
    apply htW
    rw [← hcm]
    exact h
  obtain ⟨hUmin, hUrel⟩ := hU
  have hJ : W ⊔ Ideal.span {t} = (W.map (red p) ⊔ Ideal.span {red p t}).comap (red p) := by
    rw [← Set.image_singleton, ← comap_sup_span p (W.map (red p)) {t}, hcm]
  rw [hJ, Ideal.comap_minimalPrimes_eq_of_surjective (red_surjective p)] at hUmin
  obtain ⟨U', hU'min, rfl⟩ := hUmin
  have : U'.IsPrime := hU'min.1.1
  have hU'rel : IsRelevant U' := (isRelevant_comap_iff p U').mp hUrel
  have h0 : divCycle (W.map (red p)) (red p t) U' ≠ 0 := by
    unfold divCycle
    rw [dif_pos ⟨hU'min, hU'rel⟩]
    have hne_top := length_localizedQuot_ne_top _ U' hU'min
    have hne_zero : NumbersDVR.multAt (W.map (red p) ⊔ Ideal.span {red p t}) U' ≠ 0 := by
      unfold NumbersDVR.multAt
      rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
      intro hall
      obtain ⟨r, hr, hr0⟩ := hall (Ideal.Quotient.mk _ 1)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mul_one,
        Ideal.Quotient.eq_zero_iff_mem] at hr0
      exact hr (hU'min.1.2 hr0)
    intro hz
    rw [Nat.cast_eq_zero, ENat.toNat_eq_zero] at hz
    exact hz.elim hne_zero hne_top
  obtain ⟨hmp, hrd⟩ :=
    DivCycleSupport.full (ZMod p) K ι (W.map (red p)) hQ 0 hd b (red p t) htr htrV U' h0
  refine ⟨⟨Ideal.comap_isPrime _ _, ?_, (isRelevant_comap_iff p U').mpr hmp.relevant⟩, ?_⟩
  · rw [← isMultiHomogIdeal_iff]
    intro f hf c
    rw [Ideal.mem_comap] at hf ⊢
    rw [map_weightedHomogeneousComponent]
    exact hmp.multiHomog _ hf c
  · rw [ringKrullDim_eq_of_ringEquiv (quotEquiv p U'), (CutRegular.relDim_eq_natCast_iff U' 0).mp hrd,
      zero_add]

/- English proof (translation)
Unfold `NumbersDVR.divCycle`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem divCycle_nonneg (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)
    (U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) : 0 ≤ NumbersDVR.divCycle P f U := by
  unfold NumbersDVR.divCycle
  split_ifs <;> simp

/- English proof (translation)
Unfold `NumbersDVR.divCycle`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨hm, -⟩`. Conclude with `hf (hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))`.
-/
theorem divCycle_eq_zero_of_not_mem {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)}
    {f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} (hf : f ∉ U) :
    NumbersDVR.divCycle P f U = 0 := by
  unfold NumbersDVR.divCycle
  rw [dif_neg]
  rintro ⟨hm, -⟩
  exact hf (hm.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)))

/- English proof (translation)
Unfold `NumbersDVR.divCycle`. Conclude with `dif_neg hU`.
-/
theorem divCycle_eq_zero_of_not_mem_divSupp {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)}
    {f : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {U : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)}
    (hU : U ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P f) : NumbersDVR.divCycle P f U = 0 := by
  unfold NumbersDVR.divCycle
  exact dif_neg hU

/- English proof (translation)
Use function extensionality and compare the values at `U`. Unfold `NumbersDVR.divCycle`. Use `split_ifs with h1 h2 h2`. Simplify using `only [h]`. Conclude with `absurd (h ▸ h1) h2`.

Conclude with `absurd (h.symm ▸ h2) h1`. Both sides reduce to the same expression.
-/
theorem divCycle_congr {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {f f' : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : P ⊔ Ideal.span {f} = P ⊔ Ideal.span {f'}) :
    NumbersDVR.divCycle P f = NumbersDVR.divCycle P f' := by
  funext U
  unfold NumbersDVR.divCycle
  split_ifs with h1 h2 h2
  · simp only [h]
  · exact absurd (h ▸ h1) h2
  · exact absurd (h.symm ▸ h2) h1
  · rfl

/- English proof (translation)
Establish `key : ∀ x y : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, x - y ∈ W → W ⊔ Ideal.span {x} ≤ W ⊔ Ideal.span {y}`. Introduce `x y hxy`. Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Establish `: x = (x - y) + y` using `by ring`. Rewrite using `[this]`.

Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left hxy) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))`. Use `le_antisymm (key x y h) (key y x ?_)` and prove the remaining obligations. Establish `: y - x = -(x - y)` using `by ring`. Rewrite using `[this]`. Conclude with `W.neg_mem h`.
-/
theorem sup_span_eq_of_sub_mem {W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {x y : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι}
    (h : x - y ∈ W) : W ⊔ Ideal.span {x} = W ⊔ Ideal.span {y} := by
  have key : ∀ x y : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι, x - y ∈ W → W ⊔ Ideal.span {x} ≤ W ⊔ Ideal.span {y} := by
    intro x y hxy
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have : x = (x - y) + y := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hxy) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self y))
  refine le_antisymm (key x y h) (key y x ?_)
  have : y - x = -(x - y) := by ring
  rw [this]
  exact W.neg_mem h

/- English proof (translation)
Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.geoNum]`. Use `split_ifs with h`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]`. Simplify using the standard rewrite rules.
-/
theorem geoNum_one_add (W : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (a b : K → ℤ) (q : ℤ) :
    ReciprocityTheory.ChartRestriction.G.Geo.geoNum 1 W (fun _ => q • a + b) =
      q * ReciprocityTheory.ChartRestriction.G.Geo.geoNum 1 W (fun _ => a) + ReciprocityTheory.ChartRestriction.G.Geo.geoNum 1 W (fun _ => b) := by
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum,
      mul_assoc]
  · simp

/- English proof (translation)
Unfold `ReciprocityTheory.ChartRestriction.G.Geo.geoNum`. Use `split_ifs`. Conclude with `Int.natCast_nonneg _`. Conclude with `le_rfl`.
-/
theorem geoNum_zero_nonneg (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) (a : Fin 0 → K → ℤ) :
    0 ≤ ReciprocityTheory.ChartRestriction.G.Geo.geoNum 0 V a := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.geoNum
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

end SemiampleNefAlt

open ReciprocityTheory.ChartRestriction.G.Geo SemiampleNefAlt in

/- English proof (translation)
Introduce `K _ ι _ P a hsa W hW hPW hch hdim`. Establish `: W.IsPrime` using `hW.1`. Establish `hp : (charOf W).Prime` using `charOf_prime hch`. Take `⟨j, hj, hsec⟩` from `hsa W hW hPW hch`. Distinguish the cases in `hex : ∃ Q, GroundTheory.Heights₂.Heights.Inter.IsClosedPt Q ∧ W ≤ Q`.

Use `swap`. Use `le_of_eq ?_` and prove the remaining obligations. Simplify using `only [geoNum]`. Use `split_ifs with hrel`. Use `(Finset.sum_eq_zero fun k _ => ?_).symm` and prove the remaining obligations.

Establish `hemp : divSupp W (X ⟨k, (hrel k).choose⟩) = ∅`. Use extensionality with `U`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hU`. Conclude with `hex ⟨U, isClosedPt_of_mem_divSupp hW hp hdim (isMultiHomog_X _) (hrel k).choose_spec hU, le_sup_left.trans hU.1.1.2⟩`.

Rewrite using `[hemp, finsum_mem_empty, mul_zero]`. Both sides reduce to the same expression. Take `⟨Q, hQ, hWQ⟩` from `hex`. Take `⟨g, h, dg, dh, hg, hh, hdeg, hhW, hgQ, -, hglue⟩` from `hsec Q hQ hWQ`. Establish `hgW : g ∉ W` using `fun hm => hgQ (hWQ hm)`.

Establish `he0 : ∀ U : Ideal (MRing ι), 0 ≤ geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)` using `fun U => geoNum_zero_nonneg U _`. Establish `hD : ∀ (d : K → ℕ) (s : MRing ι), IsMultiHomog s d → s ∉ W → geoNum 1 W (fun _ => fun k => (d k : ℤ)) = ∑ᶠ U, NumbersDVR.divCycle W s U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)`. Introduce `d s hs hsW`. Establish `hcut` using `GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K ι W 0 Fin.elim0 d s hW hp (by rw [hdim]) hs hsW`. Establish `hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) = fun _ => fun k => (d k : ℤ)`.

Use function extensionality and compare the values at `i`. Rewrite using `[Fin.fin_one_eq_zero i]`. Simplify using `[Fin.snoc]`. Rewrite `hcut` using `[hsn]`. Rewrite using `[hcut, finsum_mem_def]`.

Use `finsum_congr fun U => ?_` and prove the remaining obligations. Distinguish the cases in `hU : U ∈ divSupp W s`. Rewrite using `[Set.indicator_of_mem hU, ← NumbersDVR.VocabDivCycle.proof ℤ K ι W s U]`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, if_pos hU]`. Rewrite using `[Set.indicator_of_notMem hU, divCycle_eq_zero_of_not_mem_divSupp hU, zero_mul]`.

Establish `hfin : ∀ s : MRing ι, (Function.support fun U => NumbersDVR.divCycle W s U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)).Finite` using `fun s => (divSupp_finite W s).subset fun U hU => by`. Assume the negation of the conclusion as `hn`. Conclude with `hU (by simp only [divCycle_eq_zero_of_not_mem_divSupp hn, zero_mul])`. Establish `hle : ∀ U, NumbersDVR.divCycle W h U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) ≤ NumbersDVR.divCycle W g U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)`. Introduce `U`.

Distinguish the cases in `hU : U ∈ divSupp W h`. Establish `hUc` using `isClosedPt_of_mem_divSupp hW hp hdim hh hhW hU`. Establish `hWU : W ≤ U` using `le_sup_left.trans hU.1.1.2`. Take `⟨g', h', dg', dh', -, -, -, hh'U, hmem⟩` from `hglue U hUc hWU`. Establish `hh'W : h' ∉ W` using `fun hm => hh'U (hWU hm)`.

Establish `hg'W : g' ∉ W`. Introduce `hm`. Establish `hgh : g * h' ∈ W`. Use `W.add_mem hmem (W.mul_mem_right h hm)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Break down `Ideal.IsPrime.mem_or_mem ‹_› hgh with h1 | h1` into its components or cases. Use `exacts [hgW h1, hh'W h1]`. Establish `hcyc` using `divCycle_congr (sup_span_eq_of_sub_mem hmem)`. Rewrite `hcyc` using `[NumbersDVR.DivCycleMul.proof ℤ K ι W g h' ‹_› hgW hh'W, NumbersDVR.DivCycleMul.proof ℤ K ι W g' h ‹_› hg'W hhW]`. Establish `hU'` using `congrFun hcyc U`.

Simplify using `only [Pi.add_apply] at hU'`. Establish `hz : NumbersDVR.divCycle W h' U = 0` using `divCycle_eq_zero_of_not_mem hh'U`. Establish `hnn : 0 ≤ NumbersDVR.divCycle W g' U` using `divCycle_nonneg W g' U`. Conclude with `mul_le_mul_of_nonneg_right (by linarith) (he0 U)`. Rewrite using `[divCycle_eq_zero_of_not_mem_divSupp hU, zero_mul]`.

Conclude with `mul_nonneg (divCycle_nonneg W g U) (he0 U)`. Establish `hsum` using `finsum_le_finsum' (hfin h) (hfin g) hle`. Establish `hv : (fun k => (dg k : ℤ)) = (j : ℤ) • a + fun k => (dh k : ℤ)`. Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdeg k]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlin` using `geoNum_one_add W a (fun k => (dh k : ℤ)) (j : ℤ)`. Rewrite `hlin` using `[← hv, hD dg g hg hgW, hD dh h hh hhW]`. Establish `hjpos : (0 : ℤ) < j` using `by exact_mod_cast hj`. Assume the negation of the conclusion as `hneg`.

Establish `hlt` using `lt_of_not_ge hneg`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem SemiampleNef.proof : SemiampleNef.Statement := by
  intro K _ ι _ P a hsa W hW hPW hch hdim
  classical
  have : W.IsPrime := hW.1
  have hp : (charOf W).Prime := charOf_prime hch
  obtain ⟨j, hj, hsec⟩ := hsa W hW hPW hch
  by_cases hex : ∃ Q, GroundTheory.Heights₂.Heights.Inter.IsClosedPt Q ∧ W ≤ Q
  swap
  ·
    refine le_of_eq ?_
    simp only [geoNum]
    split_ifs with hrel
    · refine (Finset.sum_eq_zero fun k _ => ?_).symm
      have hemp : divSupp W (X ⟨k, (hrel k).choose⟩) = ∅ := by
        ext U
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hU
        exact hex ⟨U, isClosedPt_of_mem_divSupp hW hp hdim (isMultiHomog_X _) (hrel k).choose_spec hU,
          le_sup_left.trans hU.1.1.2⟩
      rw [hemp, finsum_mem_empty, mul_zero]
    · rfl
  obtain ⟨Q, hQ, hWQ⟩ := hex
  obtain ⟨g, h, dg, dh, hg, hh, hdeg, hhW, hgQ, -, hglue⟩ := hsec Q hQ hWQ
  have hgW : g ∉ W := fun hm => hgQ (hWQ hm)
  have he0 : ∀ U : Ideal (MRing ι), 0 ≤ geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := fun U => geoNum_zero_nonneg U _

  have hD : ∀ (d : K → ℕ) (s : MRing ι), IsMultiHomog s d → s ∉ W →
      geoNum 1 W (fun _ => fun k => (d k : ℤ)) =
        ∑ᶠ U, NumbersDVR.divCycle W s U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := by
    intro d s hs hsW
    have hcut := GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K ι W 0 Fin.elim0 d s hW hp
      (by rw [hdim]) hs hsW
    have hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) =
        fun _ => fun k => (d k : ℤ) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [Fin.snoc]
    rw [hsn] at hcut
    rw [hcut, finsum_mem_def]
    refine finsum_congr fun U => ?_
    by_cases hU : U ∈ divSupp W s
    · rw [Set.indicator_of_mem hU, ← NumbersDVR.VocabDivCycle.proof ℤ K ι W s U]
      simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe, if_pos hU]
    · rw [Set.indicator_of_notMem hU, divCycle_eq_zero_of_not_mem_divSupp hU, zero_mul]
  have hfin : ∀ s : MRing ι, (Function.support fun U =>
      NumbersDVR.divCycle W s U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ)).Finite := fun s =>
    (divSupp_finite W s).subset fun U hU => by
      by_contra hn
      exact hU (by simp only [divCycle_eq_zero_of_not_mem_divSupp hn, zero_mul])

  have hle : ∀ U, NumbersDVR.divCycle W h U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) ≤
      NumbersDVR.divCycle W g U * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := by
    intro U
    by_cases hU : U ∈ divSupp W h
    · have hUc := isClosedPt_of_mem_divSupp hW hp hdim hh hhW hU
      have hWU : W ≤ U := le_sup_left.trans hU.1.1.2
      obtain ⟨g', h', dg', dh', -, -, -, hh'U, hmem⟩ := hglue U hUc hWU
      have hh'W : h' ∉ W := fun hm => hh'U (hWU hm)
      have hg'W : g' ∉ W := by
        intro hm
        have hgh : g * h' ∈ W := by
          have := W.add_mem hmem (W.mul_mem_right h hm)
          rwa [sub_add_cancel] at this
        rcases Ideal.IsPrime.mem_or_mem ‹_› hgh with h1 | h1
        exacts [hgW h1, hh'W h1]
      have hcyc := divCycle_congr (sup_span_eq_of_sub_mem hmem)
      rw [NumbersDVR.DivCycleMul.proof ℤ K ι W g h' ‹_› hgW hh'W,
        NumbersDVR.DivCycleMul.proof ℤ K ι W g' h ‹_› hg'W hhW] at hcyc
      have hU' := congrFun hcyc U
      simp only [Pi.add_apply] at hU'
      have hz : NumbersDVR.divCycle W h' U = 0 := divCycle_eq_zero_of_not_mem hh'U
      have hnn : 0 ≤ NumbersDVR.divCycle W g' U := divCycle_nonneg W g' U
      exact mul_le_mul_of_nonneg_right (by linarith) (he0 U)
    · rw [divCycle_eq_zero_of_not_mem_divSupp hU, zero_mul]
      exact mul_nonneg (divCycle_nonneg W g U) (he0 U)
  have hsum := finsum_le_finsum' (hfin h) (hfin g) hle
  have hv : (fun k => (dg k : ℤ)) = (j : ℤ) • a + fun k => (dh k : ℤ) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hdeg k]
    ring
  have hlin := geoNum_one_add W a (fun k => (dh k : ℤ)) (j : ℤ)
  rw [← hv, hD dg g hg hgW, hD dh h hh hhW] at hlin
  have hjpos : (0 : ℤ) < j := by exact_mod_cast hj
  by_contra hneg
  have hlt := lt_of_not_ge hneg
  nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
