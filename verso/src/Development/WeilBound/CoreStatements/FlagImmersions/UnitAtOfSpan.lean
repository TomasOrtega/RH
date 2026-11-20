import Development.WeilBound.CoreStatements.FlagImmersions.FibSandwich
import Development.WeilBound.CoreStatements.FlagImmersions.ExistsUnitMetric
import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFormNotInCoordIdeal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointOverNumberFieldValue

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
  GlobalTheory.CompanionTheory.Ar.Flat.UnitChart

namespace RootFieldNumerics.RF

namespace Smooth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Introduce `o ho`. Establish `h1 : ValAt ξ z (o : Ω) (o : ℂ)` using `LiesOver.valAt_int hc o`. Establish `h2` using `CxVal.inv h1 (by exact_mod_cast ho)`. Establish `h3` using `CxVal.mul h1 h2`. Establish `h0 : (o : Ω) ≠ 0`.

Introduce `h`. Establish `h4 : ValAt ξ z (0 : Ω) (0 : ℂ)` using `by simpa using LiesOver.valAt_int hc 0`. Rewrite `h1` using `[h]`. Conclude with `ho (by exact_mod_cast CxVal.unique h1 h4)`. Take `⟨_, s, e, -⟩` from `h1`.

Take `⟨_, s', e', -⟩` from `h2`. Conclude with `⟨by simpa using h0, ⟨s, by simpa using e⟩, ⟨s', by simpa using e'⟩⟩`.
-/
theorem mem_genFibre (z : Spec (CommRingCat.of ℂ) ⟶ X) (hc : genPt ξ ⤳ centre z) :
    (⟨centre z, hc⟩ : Cpt ξ) ∈ genFibre ℤ ξ := by
  intro o ho
  have h1 : ValAt ξ z (o : Ω) (o : ℂ) := LiesOver.valAt_int hc o
  have h2 := CxVal.inv h1 (by exact_mod_cast ho)
  have h3 := CxVal.mul h1 h2
  have h0 : (o : Ω) ≠ 0 := by
    intro h
    have h4 : ValAt ξ z (0 : Ω) (0 : ℂ) := by simpa using LiesOver.valAt_int hc 0
    rw [h] at h1
    exact ho (by exact_mod_cast CxVal.unique h1 h4)
  obtain ⟨_, s, e, -⟩ := h1
  obtain ⟨_, s', e', -⟩ := h2
  exact ⟨by simpa using h0, ⟨s, by simpa using e⟩, ⟨s', by simpa using e'⟩⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `hu.2.2`. Establish `h1` using `CxVal.mul hr (⟨hc, s, hs, rfl⟩ : ValAt ξ z u⁻¹ _)`. Rewrite `h1` using `[mul_inv_cancel₀ hu.1]`. Conclude with `left_ne_zero_of_mul_eq_one (CxVal.unique h1 (CxVal.one hc))`.
-/
theorem val_ne_zero {z : Spec (CommRingCat.of ℂ) ⟶ X} {hc : genPt ξ ⤳ centre z} {u : Ω} {r : ℂ}
    (hu : unitAt ξ ⟨centre z, hc⟩ u) (hr : ValAt ξ z u r) : r ≠ 0 := by
  obtain ⟨s, hs⟩ := hu.2.2
  have h1 := CxVal.mul hr (⟨hc, s, hs, rfl⟩ : ValAt ξ z u⁻¹ _)
  rw [mul_inv_cancel₀ hu.1] at h1
  exact left_ne_zero_of_mul_eq_one (CxVal.unique h1 (CxVal.one hc))

/- English proof (translation)
Establish `key : ∀ {s t : Ω}, t ≠ 0 → s ∈ Submodule.span (regAt ξ p) {t} → s / t ∈ regAt ξ p`. Introduce `s t ht hm`. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 hm`. Establish `: s / t = r`. Rewrite using `[← hr]`.

Conclude with `mul_div_cancel_right₀ _ ht`. Rewrite using `[this]`. Conclude with `r.2`. Use `⟨div_ne_zero hs ht, key ht (h ▸ Submodule.mem_span_singleton_self s), ?_⟩` and prove the remaining obligations. Rewrite using `[inv_div]`.

Conclude with `key hs (h ▸ Submodule.mem_span_singleton_self t)`.
-/
theorem unitAt_of_span {p : Cpt ξ} {s t : Ω} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : Submodule.span (regAt ξ p) {s} = Submodule.span (regAt ξ p) {t}) : unitAt ξ p (s / t) := by
  have key : ∀ {s t : Ω}, t ≠ 0 → s ∈ Submodule.span (regAt ξ p) {t} → s / t ∈ regAt ξ p := by
    intro s t ht hm
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hm
    have : s / t = r := by
      rw [← hr]
      exact mul_div_cancel_right₀ _ ht
    rw [this]
    exact r.2
  refine ⟨div_ne_zero hs ht, key ht (h ▸ Submodule.mem_span_singleton_self s), ?_⟩
  rw [inv_div]
  exact key hs (h ▸ Submodule.mem_span_singleton_self t)

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

/- English proof (translation)
Take `⟨z, hz, hco⟩` from `SheetDecomposition.ChartForm.exists_point hT w (fun k => (hw.1 k).imp fun _ h => IsUnit.mk0 _ h) (fun g hg => by rw [← evC_eq]; exact hw.2 g hg)`. Use `choose c hc using hco.1`. Establish `hy : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hco.2 k _ (hc k)).1`. Establish `hY : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0` using `fun m => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)`. Establish `hW : ∀ m : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ m k) ≠ 0` using `fun m => Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero`.

Establish `hxc : (∏ k, y ⟨k, c k⟩) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => hy k`. Set `p : Cpt ξ` to `⟨centre z, hz⟩`. Establish `hch : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p`. Use `⟨hxc, fun c' => ?_⟩` and prove the remaining obligations. Use `show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _`.

Rewrite using `[← Finset.prod_div_distrib]`. Use `Subring.prod_mem _ fun k _ => ?_` and prove the remaining obligations. Take `⟨r, ⟨_, s, e, -⟩, -⟩` from `(hco.2 k _ (hc k)).2 (c' k)`. Conclude with `⟨s, e⟩`. Establish `hYa : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)`.

Establish `hgen` using `hg p (mem_genFibre z hz)`. Establish `hu : unitAt ξ p (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k)`. Use `unitAt_of_span hgen.1 (mul_ne_zero hYa hD.1) (hgen.2.symm.trans (hD.2 p trivial c hch))` as an intermediate fact. Rewrite `this` using `[mul_div_mul_right _ _ hD.1]`. Then use the resulting hypothesis. Take `⟨U, hU, hmem⟩` from `hT.affine c hxc`.

Establish `hpU : p.1 ∈ U` using `(hmem _).2 ⟨hz, hch⟩`. Establish `hgU : genPt ξ ∈ U` using `(hmem _).2 ⟨specializes_rfl, CoordBase.inChart_gen hT hxc⟩`. Take `⟨s, hs⟩` from `hu.2.1`. Use `letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hpU⟩ : U)`. Establish `hloc` using `hU.isLocalization_stalk ⟨p.1, hpU⟩`.

Take `⟨⟨t, f⟩, e⟩` from `IsLocalization.surj (hU.primeIdealOf ⟨p.1, hpU⟩).asIdeal.primeCompl s`. Establish `e' : s * X.presheaf.germ U p.1 hpU f.1 = X.presheaf.germ U p.1 hpU t` using `e`. Establish `hfu : IsUnit (X.presheaf.germ U p.1 hpU f.1)` using `IsLocalization.map_units (X.presheaf.stalk p.1) f`. Establish `h2` using `congrArg (genMap ξ p) e'`. Rewrite `h2` using `[map_mul, hs, CoordBase.genMap_germ_val U hgU p hpU, CoordBase.genMap_germ_val U hgU p hpU]`.

Establish `hfu' : unitAt ξ p (CoordBase.val U hgU f.1)`. Rewrite using `[← CoordBase.genMap_germ_val U hgU p hpU]`. Take `⟨v, hv⟩` from `hfu`. Rewrite using `[← hv]`. Conclude with `⟨(v.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨v⁻¹.val, map_units_inv _ v⟩⟩`.

Establish `htu : unitAt ξ p (CoordBase.val U hgU t)` using `h2 ▸ ZUnit.mul hu hfu'`. Establish `hin : ∀ b : Γ(X, U), CoordBase.val U hgU b ∈ chartRingZ y c` using `fun b => by`. Rewrite using `[← CptIn.Intr.segre_chart y c hy]`. Conclude with `(CoordBase.mem_adjoin_iff hT hxc hU hmem hgU _).2 ⟨b, rfl⟩`. Take `⟨δt, Gt, ht1, ht2, ht3⟩` from `LiesOver.exists_form_valAt hz hco c hy hc (hin t)`.

Take `⟨δf, Gf, hf1, hf2, hf3⟩` from `LiesOver.exists_form_valAt hz hco c hy hc (hin f.1)`. Establish `nt : evC w Gt ≠ 0` using `fun h => val_ne_zero htu ht3 (by rw [h, zero_div])`. Establish `nf : evC w Gf ≠ 0` using `fun h => val_ne_zero hfu' hf3 (by rw [h, zero_div])`. Establish `hm : ∀ m : K → ℕ, evC w (cMon c m) ≠ 0` using `fun m => by`. Rewrite using `[evC_eq, aeval_cMon]`.

Conclude with `hW m`. Use `⟨Gt * cMon c δf * cMon c fun k => (a k).toNat, Gf * cMon c δt * cMon c fun k => (-a k).toNat, _, _, ⟨homog_mul (homog_mul ht1 (homog_cMon _ _)) (homog_cMon _ _), homog_mul (homog_mul hf1 (homog_cMon _ _)) (homog_cMon _ _), fun k => ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply]`. Use linear arithmetic over natural numbers and integers. Establish `ea : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [map_mul, aeval_cMon, ht2, hf2]`. Rewrite using `[ea, ← h2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[evC_mul, evC_mul]`. Conclude with `mul_ne_zero (mul_ne_zero nt (hm _)) (hm _)`.

Rewrite using `[evC_mul, evC_mul]`. Conclude with `mul_ne_zero (mul_ne_zero nf (hm _)) (hm _)`.
-/
theorem pres_on (hT : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) {L : Lat ξ Ω} {a : K → ℤ} {e₀ c₀ : Ω}
    (hD : L.IsDegOn Set.univ y a e₀) (hg : ∀ p ∈ genFibre ℤ ξ, L.IsGenAt p (c₀ * e₀))
    {w : (Σ k, J k) → ℂ} (hw : w ∈ mcPts (mCoordIdeal y)) :
    ∃ g h dg dh, Pres y a c₀ g h dg dh ∧ evC w g ≠ 0 ∧ evC w h ≠ 0 := by
  classical
  obtain ⟨z, hz, hco⟩ := SheetDecomposition.ChartForm.exists_point hT w
    (fun k => (hw.1 k).imp fun _ h => IsUnit.mk0 _ h) (fun g hg => by rw [← evC_eq]; exact hw.2 g hg)
  choose c hc using hco.1
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hco.2 k _ (hc k)).1
  have hY : ∀ m : K → ℕ, (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
  have hW : ∀ m : K → ℕ, (∏ k, w ⟨k, c k⟩ ^ m k) ≠ 0 := fun m =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k).ne_zero
  have hxc : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  let p : Cpt ξ := ⟨centre z, hz⟩
  have hch : InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c p := by
    refine ⟨hxc, fun c' => ?_⟩
    show (∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    refine Subring.prod_mem _ fun k _ => ?_
    obtain ⟨r, ⟨_, s, e, -⟩, -⟩ := (hco.2 k _ (hc k)).2 (c' k)
    exact ⟨s, e⟩
  have hYa : (∏ k, y ⟨k, c k⟩ ^ a k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hy k)
  have hgen := hg p (mem_genFibre z hz)
  have hu : unitAt ξ p (c₀ / ∏ k, y ⟨k, c k⟩ ^ a k) := by
    have := unitAt_of_span hgen.1 (mul_ne_zero hYa hD.1) (hgen.2.symm.trans (hD.2 p trivial c hch))
    rwa [mul_div_mul_right _ _ hD.1] at this
  obtain ⟨U, hU, hmem⟩ := hT.affine c hxc
  have hpU : p.1 ∈ U := (hmem _).2 ⟨hz, hch⟩
  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordBase.inChart_gen hT hxc⟩
  obtain ⟨s, hs⟩ := hu.2.1
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨p.1, hpU⟩ : U)
  have hloc := hU.isLocalization_stalk ⟨p.1, hpU⟩
  obtain ⟨⟨t, f⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨p.1, hpU⟩).asIdeal.primeCompl s
  have e' : s * X.presheaf.germ U p.1 hpU f.1 = X.presheaf.germ U p.1 hpU t := e
  have hfu : IsUnit (X.presheaf.germ U p.1 hpU f.1) := IsLocalization.map_units (X.presheaf.stalk p.1) f
  have h2 := congrArg (genMap ξ p) e'
  rw [map_mul, hs, CoordBase.genMap_germ_val U hgU p hpU, CoordBase.genMap_germ_val U hgU p hpU] at h2
  have hfu' : unitAt ξ p (CoordBase.val U hgU f.1) := by
    rw [← CoordBase.genMap_germ_val U hgU p hpU]
    obtain ⟨v, hv⟩ := hfu
    rw [← hv]
    exact ⟨(v.isUnit.map _).ne_zero, ⟨_, rfl⟩, ⟨v⁻¹.val, map_units_inv _ v⟩⟩
  have htu : unitAt ξ p (CoordBase.val U hgU t) := h2 ▸ ZUnit.mul hu hfu'
  have hin : ∀ b : Γ(X, U), CoordBase.val U hgU b ∈ chartRingZ y c := fun b => by
    rw [← CptIn.Intr.segre_chart y c hy]
    exact (CoordBase.mem_adjoin_iff hT hxc hU hmem hgU _).2 ⟨b, rfl⟩
  obtain ⟨δt, Gt, ht1, ht2, ht3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin t)
  obtain ⟨δf, Gf, hf1, hf2, hf3⟩ := LiesOver.exists_form_valAt hz hco c hy hc (hin f.1)
  have nt : evC w Gt ≠ 0 := fun h => val_ne_zero htu ht3 (by rw [h, zero_div])
  have nf : evC w Gf ≠ 0 := fun h => val_ne_zero hfu' hf3 (by rw [h, zero_div])
  have hm : ∀ m : K → ℕ, evC w (cMon c m) ≠ 0 := fun m => by
    rw [evC_eq, aeval_cMon]
    exact hW m
  refine ⟨Gt * cMon c δf * cMon c fun k => (a k).toNat, Gf * cMon c δt * cMon c fun k => (-a k).toNat, _, _,
    ⟨homog_mul (homog_mul ht1 (homog_cMon _ _)) (homog_cMon _ _),
      homog_mul (homog_mul hf1 (homog_cMon _ _)) (homog_cMon _ _), fun k => ?_, ?_⟩, ?_, ?_⟩
  · simp only [Pi.add_apply]
    omega
  · have ea : (∏ k, y ⟨k, c k⟩ ^ (a k).toNat) = (∏ k, y ⟨k, c k⟩ ^ a k) * ∏ k, y ⟨k, c k⟩ ^ (-a k).toNat := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
      congr 1
      omega
    simp only [map_mul, aeval_cMon, ht2, hf2]
    rw [ea, ← h2]
    field_simp
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nt (hm _)) (hm _)
  · rw [evC_mul, evC_mul]; exact mul_ne_zero (mul_ne_zero nf (hm _)) (hm _)

end Smooth

open Smooth in
/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y F' _ _ ψ L a e₀ c₀ cinf n _ hT _ hO _ hvar hD hg hpos hconj`. Take `⟨A₀, ha, hsm, hcj, hn⟩` from `exists_unit_metric y a c₀ fun w hw => by`. Distinguish the cases in `h : w ∈ mcPts (mCoordIdeal y)`. Conclude with `pres_on hT hD hg h`. Conclude with `pres_off hvar.2.1.2.1 a c₀ hw h`.

Take `⟨u, hu, huc⟩` from `GlobalTheory.T.exists_place_weight_conj_invariant K J Ω F' y ψ (fun σ => Real.log (cinf σ)) hO`. Establish `huc'` using `huc fun σ => by simp only [hconj]`. Use `⟨hu.shift A₀, ?_, ?_, fun z => ?_, ?_, fun w hw => ?_⟩` and prove the remaining obligations. Use `show A₀.a + 0 = a`. Rewrite using `[add_zero, ha]`.

Conclude with `ContDiffOn.mul hsm hu.smooth.neg.exp`. Use `show A₀.h _ * Real.exp (-u _) = A₀.h z * Real.exp (-u z)`. Rewrite using `[hcj z, huc' z]`. Introduce `σ z g h dg dh hz h1 h2 h3 h4`. Establish `h3' : ∀ k, (dg k : ℤ) - dh k = a k` using `fun k => by`.

Rewrite using `[h3 k]`. Use `show (A₀.a + 0) k = a k`. Rewrite using `[add_zero, ha]`. Rewrite using `[hn z hz.1 g h dg dh ⟨h1, h2, h3', h4⟩]`. Use `show _ = cinf σ * (A₀.h z * Real.exp (-u z)) * _`.

Rewrite using `[(hu.near σ z hz).self_of_nhds, Real.exp_neg, Real.exp_log (hpos σ)]`. Use `(hpos σ).ne'` as an intermediate fact. Clear the denominators using the available nonvanishing facts. Take `⟨g, h, dg, dh, hP, -, hh⟩` from `pres_on hT hD hg hw`. Conclude with `⟨g, h, dg, dh, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hh⟩`.
-/
theorem smoothLine : SmoothLine := by
  intro X Ω _ ξ K _ J _ y F' _ _ ψ L a e₀ c₀ cinf n _ hT _ hO _ hvar hD hg hpos hconj
  obtain ⟨A₀, ha, hsm, hcj, hn⟩ := exists_unit_metric y a c₀ fun w hw => by
    by_cases h : w ∈ mcPts (mCoordIdeal y)
    · exact pres_on hT hD hg h
    · exact pres_off hvar.2.1.2.1 a c₀ hw h
  obtain ⟨u, hu, huc⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K J Ω F' y ψ (fun σ => Real.log (cinf σ)) hO
  have huc' := huc fun σ => by simp only [hconj]
  refine ⟨hu.shift A₀, ?_, ?_, fun z => ?_, ?_, fun w hw => ?_⟩
  · show A₀.a + 0 = a
    rw [add_zero, ha]
  · exact ContDiffOn.mul hsm hu.smooth.neg.exp
  · show A₀.h _ * Real.exp (-u _) = A₀.h z * Real.exp (-u z)
    rw [hcj z, huc' z]
  · intro σ z g h dg dh hz h1 h2 h3 h4
    have h3' : ∀ k, (dg k : ℤ) - dh k = a k := fun k => by
      rw [h3 k]
      show (A₀.a + 0) k = a k
      rw [add_zero, ha]
    rw [hn z hz.1 g h dg dh ⟨h1, h2, h3', h4⟩]
    show _ = cinf σ * (A₀.h z * Real.exp (-u z)) * _
    rw [(hu.near σ z hz).self_of_nhds, Real.exp_neg, Real.exp_log (hpos σ)]
    have := (hpos σ).ne'
    field_simp
  · obtain ⟨g, h, dg, dh, hP, -, hh⟩ := pres_on hT hD hg hw
    exact ⟨g, h, dg, dh, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2, hh⟩

end RootFieldNumerics.RF
