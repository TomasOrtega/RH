import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsSwap
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.GeoNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial GroundTheory.Heights₂.Heights.Bridge GroundTheory.Heights₂.Heights.Bridge.GeoNum
  GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

/- English proof (translation)
Establish `h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈ V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)`. Rewrite using `[← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]`. Conclude with `Int.dvd_natAbs.mpr dvd_rfl`. Conclude with `h`.
-/
theorem C_charOf_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (V : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)) :
    (C ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := by
  have h : ((ReciprocityTheory.ChartRestriction.G.Geo.charOf V : ℕ) : ℤ) ∈
      V.comap (C : ℤ →+* ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) := by
    rw [← Submodule.IsPrincipal.span_singleton_generator (V.comap C), Ideal.mem_span_singleton]
    exact Int.dvd_natAbs.mpr dvd_rfl
  exact h

/- English proof (translation)
Introduce `K _ ι _ V n a b t hV hp hdim ht htV`. Use `set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf V with hp_def`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V` using `C_charOf_mem V`. Establish `hker : RingHom.ker (red (ι` using `ι) p) ≤ V := by`.

Rewrite using `[ker_red, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hpV`. Establish `hcm : (V.map (red p)).comap (red p) = V` using `comap_map_eq p hker`. Establish `: V.IsPrime` using `hV.1`. Establish `hQ : IsMultiProjPrime (V.map (red p))`.

Use `⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[isMultiHomogIdeal_iff]`. Take `⟨S, hS, hVS⟩` from `hV.2.1`. Use `⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`.

Take `⟨c, hc⟩` from `hS f hf`. Conclude with `⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩`. Rewrite using `[← isRelevant_comap_iff p, hcm]`. Conclude with `hV.2.2`. Establish `hd : relDim (V.map (red p)) = ((n + 1 : ℕ) : WithBot (WithTop ℤ))`.

Rewrite using `[CutRegular.relDim_eq_natCast_iff, ← hdim]`. Use `ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))` as an intermediate fact. Rewrite `this` using `[hcm]`. Conclude with `this.symm`. Establish `htr : IsMultiHomog (red p t) b`.

Rewrite using `[isMultiHomog_iff]`. Conclude with `fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k`. Establish `htrV : red p t ∉ V.map (red p)`. Introduce `h`. Apply `htV` to reduce the goal to its premises.

Rewrite using `[← hcm]`. Conclude with `h`. Rewrite using `[← intNum_map_eq_geoNum p (n + 1) V hV hpV hdim, CutRegular.full (ZMod p) K ι (V.map (red p)) hQ n hd b (red p t) htr htrV a]`. Establish `hcut` using `cycEval_divCycle_eq p (V.map (red p)) t (fun W => intNum (ZMod p) W a) (fun W => ReciprocityTheory.ChartRestriction.G.Geo.geoNum n W a) (fun W' hW' => by`. Take `⟨hW'm, hW'd⟩` from `DivCycleSupport.full (ZMod p) K ι (V.map (red p)) hQ n hd b _ htr htrV W' hW'`.

Conclude with `intNum_eq_geoNum_comap p n W' hW'm hW'd a)`. Rewrite `hcut` using `[hcm]`. Conclude with `hcut`.
-/
theorem GeoNumCut.full : GeoNumCut.Statement := by
  intro K _ ι _ V n a b t hV hp hdim ht htV
  classical
  set p := ReciprocityTheory.ChartRestriction.G.Geo.charOf V with hp_def
  have : Fact p.Prime := ⟨hp⟩
  have hpV : (C (p : ℤ) : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∈ V := C_charOf_mem V
  have hker : RingHom.ker (red (ι := ι) p) ≤ V := by
    rw [ker_red, Ideal.span_le, Set.singleton_subset_iff]
    exact hpV
  have hcm : (V.map (red p)).comap (red p) = V := comap_map_eq p hker
  have : V.IsPrime := hV.1

  have hQ : IsMultiProjPrime (V.map (red p)) := by
    refine ⟨Ideal.map_isPrime_of_surjective (red_surjective p) hker, ?_, ?_⟩
    · rw [isMultiHomogIdeal_iff]
      obtain ⟨S, hS, hVS⟩ := hV.2.1
      refine ⟨red p '' S, ?_, by rw [hVS, Ideal.map_span]⟩
      rintro _ ⟨f, hf, rfl⟩
      obtain ⟨c, hc⟩ := hS f hf
      exact ⟨c, fun m hm k => hc m (MvPolynomial.support_map_subset _ _ hm) k⟩
    · rw [← isRelevant_comap_iff p, hcm]
      exact hV.2.2
  have hd : relDim (V.map (red p)) = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [CutRegular.relDim_eq_natCast_iff, ← hdim]
    have := ringKrullDim_eq_of_ringEquiv (quotEquiv p (V.map (red p)))
    rw [hcm] at this
    exact this.symm

  have htr : IsMultiHomog (red p t) b := by
    rw [isMultiHomog_iff]
    exact fun m hm k => ht m (MvPolynomial.support_map_subset _ _ hm) k
  have htrV : red p t ∉ V.map (red p) := by
    intro h
    apply htV
    rw [← hcm]
    exact h

  rw [← intNum_map_eq_geoNum p (n + 1) V hV hpV hdim,
    CutRegular.full (ZMod p) K ι (V.map (red p)) hQ n hd b (red p t) htr htrV a]
  have hcut := cycEval_divCycle_eq p (V.map (red p)) t
    (fun W => intNum (ZMod p) W a) (fun W => ReciprocityTheory.ChartRestriction.G.Geo.geoNum n W a)
    (fun W' hW' => by
      obtain ⟨hW'm, hW'd⟩ :=
        DivCycleSupport.full (ZMod p) K ι (V.map (red p)) hQ n hd b _ htr htrV W' hW'
      exact intNum_eq_geoNum_comap p n W' hW'm hW'd a)
  rw [hcm] at hcut
  exact hcut

end

end GroundTheory.Heights₂.Heights.Inter
