import Formalism.SuccessiveMinima.DefsMink

open MeasureTheory Module Metric Set
open scoped Pointwise ENNReal

noncomputable section

namespace Formalism.FN

/- English proof (translation)
Use `set B := b.ofZLatticeBasis ℝ L with hB`. Set `f : E ≃ᵐ (ι → ℝ)` to `B.equivFunL.toHomeomorph.toMeasurableEquiv`. Establish `hf : (f : E → ι → ℝ) = B.equivFun` using `rfl`. Establish `: (μ.map f).IsAddHaarMeasure` using `B.equivFunL.isAddHaarMeasure_map μ`. Establish `huniq` using `MeasureTheory.Measure.isAddLeftInvariant_eq_smul (μ.map f) volume`.

Take `⟨c, hc⟩ : ∃ c, c = MeasureTheory.Measure.addHaarScalarFactor (μ.map f) volume` from `⟨_, rfl⟩`. Rewrite `huniq` using `[← hc]`. Establish `himg : ∀ T : Set E, μ T = c * volume (B.equivFun '' T)`. Introduce `T`. Establish `h1 : μ T = μ.map f (f '' T)`.

Rewrite using `[MeasurableEquiv.map_apply, Set.preimage_image_eq T f.injective]`. Rewrite using `[h1, huniq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hf]`. Establish `hD : (B.equivFun : E → ι → ℝ) '' ZSpan.fundamentalDomain B = Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1`. Establish `h : ZSpan.fundamentalDomain B = (B.equivFun : E → ι → ℝ) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1)`. Use extensionality with `x`.

Simplify using `[ZSpan.mem_fundamentalDomain, Set.mem_pi]`. Rewrite using `[h, Set.image_preimage_eq _ B.equivFun.surjective]`. Establish `hvol : volume (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) = 1`. Rewrite using `[volume_pi_pi]`. Simplify using the standard rewrite rules.

Establish `hcov : c = ENNReal.ofReal (ZLattice.covolume L μ)`. Establish `h` using `himg (ZSpan.fundamentalDomain B)`. Rewrite `h` using `[hD, hvol, mul_one]`. Rewrite using `[← h, ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ), measureReal_def, ENNReal.ofReal_toReal]`. Conclude with `(Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded B)).ne`.

Rewrite using `[himg S, hcov]`.
-/
theorem measure_eq_covolume_mul_volume_image {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type} [Fintype ι] (b : Basis ι ℤ L) (S : Set E) :
    μ S = ENNReal.ofReal (ZLattice.covolume L μ) *
      volume ((b.ofZLatticeBasis ℝ L).equivFun '' S) := by
  set B := b.ofZLatticeBasis ℝ L with hB
  let f : E ≃ᵐ (ι → ℝ) := B.equivFunL.toHomeomorph.toMeasurableEquiv
  have hf : (f : E → ι → ℝ) = B.equivFun := rfl
  have : (μ.map f).IsAddHaarMeasure := B.equivFunL.isAddHaarMeasure_map μ
  have huniq := MeasureTheory.Measure.isAddLeftInvariant_eq_smul (μ.map f) volume
  obtain ⟨c, hc⟩ : ∃ c, c = MeasureTheory.Measure.addHaarScalarFactor (μ.map f) volume := ⟨_, rfl⟩
  rw [← hc] at huniq
  have himg : ∀ T : Set E, μ T = c * volume (B.equivFun '' T) := by
    intro T
    have h1 : μ T = μ.map f (f '' T) := by
      rw [MeasurableEquiv.map_apply, Set.preimage_image_eq T f.injective]
    rw [h1, huniq, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, hf]
  have hD : (B.equivFun : E → ι → ℝ) '' ZSpan.fundamentalDomain B =
      Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1 := by
    have h : ZSpan.fundamentalDomain B =
        (B.equivFun : E → ι → ℝ) ⁻¹' (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) := by
      ext x
      simp [ZSpan.mem_fundamentalDomain, Set.mem_pi]
    rw [h, Set.image_preimage_eq _ B.equivFun.surjective]
  have hvol : volume (Set.univ.pi fun _ : ι => Set.Ico (0 : ℝ) 1) = 1 := by
    rw [volume_pi_pi]
    simp
  have hcov : c = ENNReal.ofReal (ZLattice.covolume L μ) := by
    have h := himg (ZSpan.fundamentalDomain B)
    rw [hD, hvol, mul_one] at h
    rw [← h, ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ),
      measureReal_def, ENNReal.ofReal_toReal]
    exact (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded B)).ne
  rw [himg S, hcov]

/- English proof (translation)
Introduce `E _ _ _ _ _ μ _ L _ _ K hKc hKconv hKsymm hK0`. Take `⟨v, hvli, hvL, hvK, hpos, hmono, hspan⟩` from `hs L K hKc hKconv hKsymm hK0`. Take `⟨b, hb⟩` from `ha L v hvli hvL`. Use `set B := b.ofZLatticeBasis ℝ L with hB`. Establish `hBfun : ∀ i, B i = (b i : E)` using `fun i => by simp [hB]`.

Use `set lam : Fin (finrank ℝ E) → ℝ := fun i => succMin L K ((i : ℕ) + 1) with hlam`. Establish `hneg : ∀ a ∈ interior K, -a ∈ interior K`. Introduce `a ha'`. Establish `hU : IsOpen ((fun x : E => -x) ⁻¹' interior K)` using `isOpen_interior.preimage continuous_neg`. Establish `hsub : (fun x : E => -x) ⁻¹' interior K ⊆ K` using `fun x hx => by`.

Simplify using `using hKsymm _ (interior_subset hx)`. Conclude with `interior_maximal hsub hU (by simpa using ha')`. Establish `hCo : IsOpen (B.equivFun '' ((1 / 2 : ℝ) • interior K))` using `B.equivFunL.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))`. Establish `hCc : Convex ℝ (B.equivFun '' ((1 / 2 : ℝ) • interior K))` using `(hKconv.interior.smul (1 / 2 : ℝ)).linear_image B.equivFun.toLinearMap`. Establish `hCs : ∀ x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K), -x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K)`.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Rewrite `hw` using `[Set.mem_smul_set]`. Take `⟨a, ha', rfl⟩` from `hw`. Conclude with `⟨(1 / 2 : ℝ) • -a, Set.smul_mem_smul_set (hneg a ha'), by rw [smul_neg, map_neg]⟩`. Establish `hCb : Bornology.IsBounded (B.equivFun '' ((1 / 2 : ℝ) • interior K))` using `B.equivFunL.lipschitz.isBounded_image ((hKc.isBounded.subset interior_subset).smul₀ _)`.

Establish `key` using `hc (finrank ℝ E) (B.equivFun '' ((1 / 2 : ℝ) • interior K)) lam hCo hCc hCs hCb hpos hmono (by`. Introduce `j x hx y hy hint i hji`. Rewrite `hx`, `hy` using `[Set.mem_smul_set]`. Take `⟨_, ⟨w, hw, rfl⟩, rfl⟩` from `hx`. Take `⟨_, ⟨w', hw', rfl⟩, rfl⟩` from `hy`.

Rewrite `hw`, `hw'` using `[Set.mem_smul_set]`. Take `⟨a, ha', rfl⟩` from `hw`. Take `⟨a', ha'', rfl⟩` from `hw'`. Take `⟨u, hu⟩ : ∃ u, u = lam j • ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a')` from `⟨_, rfl⟩`. Establish `heu : B.equivFun u = lam j • B.equivFun ((1 / 2 : ℝ) • a) - lam j • B.equivFun ((1 / 2 : ℝ) • a')`.

Rewrite using `[hu, map_smul B.equivFun (lam j), map_sub, smul_sub]`. Establish `hrepr : ∀ i, B.repr u i = (lam j • B.equivFun ((1 / 2 : ℝ) • a)) i - (lam j • B.equivFun ((1 / 2 : ℝ) • a')) i`. Introduce `i`. Establish `h` using `congrFun heu i`. Rewrite `h` using `[B.equivFun_apply]`.

Conclude with `h`. Establish `huL : u ∈ L`. Rewrite using `[← B.sum_repr u]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `hint i`.

Rewrite using `[hrepr i, hm, hBfun i]`. Rewrite using `[Int.cast_smul_eq_zsmul ℝ m]`. Conclude with `L.smul_mem m (b i).2`. Establish `hmid : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a' ∈ interior K`. Rewrite using `[sub_eq_add_neg, ← smul_neg]`.

Conclude with `hKconv.interior ha' (hneg a' ha'') (by norm_num) (by norm_num) (by norm_num)`. Establish `hmem : u ∈ Submodule.span ℝ (v '' {k | k < j})` using `hspan j u huL (by rw [hu]; exact Set.smul_mem_smul_set hmid)`. Establish `hsub : Submodule.span ℝ (v '' {k | k < j}) ≤ Submodule.span ℝ (B '' {k | k < j})`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, hk, rfl⟩`.

Establish `h1 : v k ∈ Submodule.span ℝ (v '' {k' | k' ≤ k})` using `Submodule.subset_span ⟨k, le_refl k, rfl⟩`. Rewrite `h1` using `[← hb k]`. Use `Submodule.span_mono ?_ h1` and prove the remaining obligations. Introduce and unpack `_ ⟨k', hk', rfl⟩`. Conclude with `⟨k', show k' < j from lt_of_le_of_lt hk' hk, hBfun k'⟩`.

Establish `hsupp` using `(B.mem_span_image).mp (hsub hmem)`. Establish `hz : B.repr u i = 0`. Assume the negation of the conclusion as `h`. Conclude with `absurd (hsupp (Finsupp.mem_support_iff.mpr h)) (not_lt.mpr hji)`. Establish `h0` using `hrepr i`.

Rewrite `h0` using `[hz]`. Conclude with `sub_eq_zero.mp h0.symm)`. Establish `hthm` using `measure_eq_covolume_mul_volume_image μ L b ((1 / 2 : ℝ) • interior K)`. Rewrite `hthm` using `[← hB]`. Establish `hhalf : μ ((1 / 2 : ℝ) • interior K) = ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) * μ (interior K)`.

Rewrite using `[Measure.addHaar_smul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ finrank ℝ E)]`. Establish `hKfin : μ K < ⊤` using `hKc.measure_lt_top`. Establish `hIfin : μ (interior K) < ⊤` using `lt_of_le_of_lt (measure_mono interior_subset) hKfin`. Establish `hKle : μ K ≤ μ (interior K)`. Combine the equalities or inequalities in the displayed calculation.

Apply `measure_mono` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[← closure_eq_interior_union_frontier]`. Conclude with `subset_closure hx`. Use `_ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _`.

Use `_ = μ (interior K) := by rw [hKconv.addHaar_frontier μ, add_zero]`. Establish `hP : 0 ≤ ∏ i, lam i` using `Finset.prod_nonneg fun i _ => (hpos i).le`. Establish `hc0 : 0 ≤ ZLattice.covolume L μ` using `(ZLattice.covolume_pos L μ).le`. Establish `e1 : (μ ((1 / 2 : ℝ) • interior K)).toReal = ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal`. Rewrite using `[hthm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]`.

Establish `e2 : (μ ((1 / 2 : ℝ) • interior K)).toReal = (1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal`. Rewrite using `[hhalf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]`. Establish `e3 : (μ (interior K)).toReal = 2 ^ finrank ℝ E * (ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal)`. Establish `h2 : (2 : ℝ) ^ finrank ℝ E * (1 / 2 : ℝ) ^ finrank ℝ E = 1`. Rewrite using `[← mul_pow]`.

Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, h2, one_mul]`. Use `_ = _ := by rw [← e2, e1]`. Establish `hK' : μ.real K ≤ (μ (interior K)).toReal` using `ENNReal.toReal_mono hIfin.ne hKle`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ * 1 := mul_le_mul_of_nonneg_left key (mul_nonneg (by positivity) hc0)`. Use `_ = _ := mul_one _`.
-/
theorem minkowskiIIUpper_of (hc : MinkCore) (hs : SuccMinFacts) (ha : AdaptedBasis) :
    MinkowskiIIUpper := by
  intro E _ _ _ _ _ μ _ L _ _ K hKc hKconv hKsymm hK0
  obtain ⟨v, hvli, hvL, hvK, hpos, hmono, hspan⟩ := hs L K hKc hKconv hKsymm hK0
  obtain ⟨b, hb⟩ := ha L v hvli hvL
  set B := b.ofZLatticeBasis ℝ L with hB
  have hBfun : ∀ i, B i = (b i : E) := fun i => by simp [hB]
  set lam : Fin (finrank ℝ E) → ℝ := fun i => succMin L K ((i : ℕ) + 1) with hlam
  have hneg : ∀ a ∈ interior K, -a ∈ interior K := by
    intro a ha'
    have hU : IsOpen ((fun x : E => -x) ⁻¹' interior K) := isOpen_interior.preimage continuous_neg
    have hsub : (fun x : E => -x) ⁻¹' interior K ⊆ K := fun x hx => by
      simpa using hKsymm _ (interior_subset hx)
    exact interior_maximal hsub hU (by simpa using ha')
  have hCo : IsOpen (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.toHomeomorph.isOpenMap _ (isOpen_interior.smul₀ (by norm_num))
  have hCc : Convex ℝ (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    (hKconv.interior.smul (1 / 2 : ℝ)).linear_image B.equivFun.toLinearMap
  have hCs : ∀ x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K),
      -x ∈ B.equivFun '' ((1 / 2 : ℝ) • interior K) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Set.mem_smul_set] at hw
    obtain ⟨a, ha', rfl⟩ := hw
    exact ⟨(1 / 2 : ℝ) • -a, Set.smul_mem_smul_set (hneg a ha'), by rw [smul_neg, map_neg]⟩
  have hCb : Bornology.IsBounded (B.equivFun '' ((1 / 2 : ℝ) • interior K)) :=
    B.equivFunL.lipschitz.isBounded_image ((hKc.isBounded.subset interior_subset).smul₀ _)
  have key := hc (finrank ℝ E) (B.equivFun '' ((1 / 2 : ℝ) • interior K)) lam hCo hCc hCs hCb
    hpos hmono (by
      intro j x hx y hy hint i hji
      rw [Set.mem_smul_set] at hx hy
      obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hx
      obtain ⟨_, ⟨w', hw', rfl⟩, rfl⟩ := hy
      rw [Set.mem_smul_set] at hw hw'
      obtain ⟨a, ha', rfl⟩ := hw
      obtain ⟨a', ha'', rfl⟩ := hw'
      obtain ⟨u, hu⟩ : ∃ u, u = lam j • ((1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a') := ⟨_, rfl⟩
      have heu : B.equivFun u =
          lam j • B.equivFun ((1 / 2 : ℝ) • a) - lam j • B.equivFun ((1 / 2 : ℝ) • a') := by
        rw [hu, map_smul B.equivFun (lam j), map_sub, smul_sub]
      have hrepr : ∀ i, B.repr u i =
          (lam j • B.equivFun ((1 / 2 : ℝ) • a)) i - (lam j • B.equivFun ((1 / 2 : ℝ) • a')) i := by
        intro i
        have h := congrFun heu i
        rw [B.equivFun_apply] at h
        exact h
      have huL : u ∈ L := by
        rw [← B.sum_repr u]
        refine sum_mem fun i _ => ?_
        obtain ⟨m, hm⟩ := hint i
        rw [hrepr i, hm, hBfun i]
        rw [Int.cast_smul_eq_zsmul ℝ m]
        exact L.smul_mem m (b i).2
      have hmid : (1 / 2 : ℝ) • a - (1 / 2 : ℝ) • a' ∈ interior K := by
        rw [sub_eq_add_neg, ← smul_neg]
        exact hKconv.interior ha' (hneg a' ha'') (by norm_num) (by norm_num) (by norm_num)
      have hmem : u ∈ Submodule.span ℝ (v '' {k | k < j}) :=
        hspan j u huL (by rw [hu]; exact Set.smul_mem_smul_set hmid)
      have hsub : Submodule.span ℝ (v '' {k | k < j}) ≤ Submodule.span ℝ (B '' {k | k < j}) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        have h1 : v k ∈ Submodule.span ℝ (v '' {k' | k' ≤ k}) :=
          Submodule.subset_span ⟨k, le_refl k, rfl⟩
        rw [← hb k] at h1
        refine Submodule.span_mono ?_ h1
        rintro _ ⟨k', hk', rfl⟩
        exact ⟨k', show k' < j from lt_of_le_of_lt hk' hk, hBfun k'⟩
      have hsupp := (B.mem_span_image).mp (hsub hmem)
      have hz : B.repr u i = 0 := by
        by_contra h
        exact absurd (hsupp (Finsupp.mem_support_iff.mpr h)) (not_lt.mpr hji)
      have h0 := hrepr i
      rw [hz] at h0
      exact sub_eq_zero.mp h0.symm)
  have hthm := measure_eq_covolume_mul_volume_image μ L b ((1 / 2 : ℝ) • interior K)
  rw [← hB] at hthm
  have hhalf : μ ((1 / 2 : ℝ) • interior K) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ finrank ℝ E) * μ (interior K) := by
    rw [Measure.addHaar_smul, abs_of_pos (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ finrank ℝ E)]
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hIfin : μ (interior K) < ⊤ := lt_of_le_of_lt (measure_mono interior_subset) hKfin
  have hKle : μ K ≤ μ (interior K) := by
    calc μ K ≤ μ (interior K ∪ frontier K) := by
          apply measure_mono
          intro x hx
          rw [← closure_eq_interior_union_frontier]
          exact subset_closure hx
      _ ≤ μ (interior K) + μ (frontier K) := measure_union_le _ _
      _ = μ (interior K) := by rw [hKconv.addHaar_frontier μ, add_zero]
  have hP : 0 ≤ ∏ i, lam i := Finset.prod_nonneg fun i _ => (hpos i).le
  have hc0 : 0 ≤ ZLattice.covolume L μ := (ZLattice.covolume_pos L μ).le
  have e1 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      ZLattice.covolume L μ * (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal := by
    rw [hthm, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0]
  have e2 : (μ ((1 / 2 : ℝ) • interior K)).toReal =
      (1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal := by
    rw [hhalf, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have e3 : (μ (interior K)).toReal = 2 ^ finrank ℝ E * (ZLattice.covolume L μ *
      (volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal) := by
    have h2 : (2 : ℝ) ^ finrank ℝ E * (1 / 2 : ℝ) ^ finrank ℝ E = 1 := by
      rw [← mul_pow]
      norm_num
    calc (μ (interior K)).toReal
        = 2 ^ finrank ℝ E * ((1 / 2 : ℝ) ^ finrank ℝ E * (μ (interior K)).toReal) := by
          rw [← mul_assoc, h2, one_mul]
      _ = _ := by rw [← e2, e1]
  have hK' : μ.real K ≤ (μ (interior K)).toReal := ENNReal.toReal_mono hIfin.ne hKle
  calc μ.real K * ∏ i, lam i ≤ (μ (interior K)).toReal * ∏ i, lam i :=
        mul_le_mul_of_nonneg_right hK' hP
    _ = 2 ^ finrank ℝ E * ZLattice.covolume L μ *
        ((volume (B.equivFun '' ((1 / 2 : ℝ) • interior K))).toReal * ∏ i, lam i) := by
          rw [e3]
          ring
    _ ≤ 2 ^ finrank ℝ E * ZLattice.covolume L μ * 1 :=
        mul_le_mul_of_nonneg_left key (mul_nonneg (by positivity) hc0)
    _ = _ := mul_one _

end Formalism.FN
