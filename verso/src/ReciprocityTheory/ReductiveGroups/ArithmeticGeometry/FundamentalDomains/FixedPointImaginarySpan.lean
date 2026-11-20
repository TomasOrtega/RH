import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientLattice

namespace ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices
  ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)

/- English proof (translation)
The claim follows from `map_mul (IsCMField.complexConj E) x y`.
-/
lemma cc_mul'' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y

/- English proof (translation)
Establish `h : conj (τ a) = τ a`. Rewrite using `[← NumberField.IsCMField.complexEmbedding_complexConj E τ a]`. Conclude with `congrArg τ ha`. Conclude with `Complex.conj_eq_iff_im.mp h`.
-/
lemma im_of_fixed {a : E} (ha : cc a = a) (τ : E →+* ℂ) : (τ a).im = 0 := by
  have h : conj (τ a) = τ a := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj E τ a]
    exact congrArg τ ha
  exact Complex.conj_eq_iff_im.mp h

/- English proof (translation)
Use `set Sp := Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) with hSp`. Establish `hsub : ∀ b ∈ X.LZ g, kap b ∈ Sp` using `fun b hb => Submodule.subset_span ((mem_Lc X g).2 ⟨b, hb, rfl⟩)`. Establish `hcr` using `cr_pos (E := E) g hg`. Establish `hposition : ∀ (i0 k0 : Fin 2), (∀ a : E, cc a = a → IsIntegral ℤ a → intersection_update_fsHerm_neg_one i0 k0 (cr (E` using `E) g • fun τ : X.Ψ => (τ.1 a).re) ∈ Sp) → ∀ p, intersection_update_fsHerm_neg_one i0 k0 p ∈ Sp := by`. Introduce `i0 k0 h p`.

Use `span_gen X g ((intersection_update_fsHerm_neg_one i0 k0).comp (cr (E := E) g • LinearMap.id)) (fun a ha hai => by` as an intermediate fact. Simplify using `using h a ha hai) ((cr (E := E) g)⁻¹ • p)`. Simplify `this` using `[smul_smul, inv_mul_cancel₀ hcr.ne']`. Establish `h00 : ∀ p, intersection_update_fsHerm_neg_one 0 0 p ∈ Sp` using `hposition 0 0 fun a ha hai => by`. Apply the tactic sequence `have hm := mem_LZ_of X g !![a, 0; 0, 0] (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero']) (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])`.

Use `hsub _ hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]`. Establish `h11 : ∀ p, intersection_update_fsHerm_neg_one 1 1 p ∈ Sp` using `hposition 1 1 fun a ha hai => by`. Apply the tactic sequence `have hm := mem_LZ_of X g !![0, 0; 0, a] (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero']) (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])`.

Use `hsub _ hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]`. Establish `h01 : ∀ p, intersection_update_fsHerm_neg_one 0 1 p ∈ Sp` using `hposition 0 1 fun a ha hai => by`. Apply the tactic sequence `have hm := mem_LZ_of X g !![0, a; a, 0] (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero']) (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])`.

Use `hsub _ hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ i k`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE, im_of_fixed ha]`. Choose the witnesses or unpack the hypotheses as in `⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by`. Establish `halg : IsAlgebraic ℤ X.ξ0` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)`.

Take `⟨k, hk, hki⟩` from `halg.exists_integral_multiple`. Use `⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩` and prove the remaining obligations. Rewrite using `[show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]`. Establish `hre : ∀ τ : E →+* ℂ, (τ η).re = 0` using `fun τ => by`. Establish `h` using `emb_cc' τ η`.

Rewrite `h` using `[hηcc, map_neg]`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0` using `fun τ h => by`.

Establish `: τ η = 0` using `Complex.ext (hre τ) h`. Conclude with `hηne ((map_eq_zero τ).1 this)`. Establish `h10 : ∀ p, intersection_update_fsHerm_neg_one 1 0 p ∈ Sp` using `by set D : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → ℝ) := LinearMap.pi fun τ : X.Ψ => (cr (E := E) g * (τ.1 η).im) • LinearMap.proj τ with hD`. Establish `hDapp : ∀ q τ, D q τ = cr (E` using `E) g * (τ.1 η).im * q τ := fun q τ => by simp [hD]`. Establish `key : ∀ q, (intersection_update_fsHerm_neg_one 1 0).comp D q ∈ Sp` using `span_gen X g _ fun a ha hai => by`.

Apply the tactic sequence `have hm := mem_LZ_of X g !![0, η * a; -(η * a), 0] (fun i k => by fin_cases i <;> fin_cases k <;>`. Simplify using `[ha, RealEmbeddingCharacters.cc_zero', cc_mul'', hηcc, RealEmbeddingCharacters.cc_neg'])`. Apply the tactic sequence `(fun i k => by fin_cases i <;> fin_cases k <;> simp [(hηi.mul hai), (hηi.mul hai).neg, isIntegral_zero])`. Use `hsub _ hm using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ i k`.

Rewrite using `[LinearMap.comp_apply]`. Apply the tactic sequence `fin_cases i <;> fin_cases k <;>`. Simplify using `[kap, position_apply, Data.embH, emb_cE, hDapp, Complex.mul_re, Complex.mul_im, hre, im_of_fixed ha]`. Expand and normalize the polynomial expressions, which then agree. Introduce `p`.

Establish `e : D (fun τ => p τ / (cr (E` using `E) g * (τ.1 η).im)) = p := by`. Use function extensionality and compare the values at `τ`. Rewrite using `[hDapp]`. Establish `: cr (E` using `E) g * (τ.1 η).im ≠ 0 := mul_ne_zero hcr.ne' (him τ.1)`. Clear denominators, using `[him τ.1]` for the nonvanishing conditions.

Use `key (fun τ => p τ / (cr (E := E) g * (τ.1 η).im))` as an intermediate fact. Rewrite `this` using `[LinearMap.comp_apply, e]`. Then use the resulting hypothesis. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Rewrite using `[sum_position y]`. Use `Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun k0 _ => ?_` and prove the remaining obligations.

Apply the tactic sequence `fin_cases i0 <;> fin_cases k0`. Use `exacts [h00 _, h01 _, h10 _, h11 _]`.
-/
lemma span_Lc (hg : 0 < g) :
    Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) = ⊤ := by
  set Sp := Submodule.span ℝ (Lc X g : Set (X.Ψ → Fin 2 → Fin 2 → ℝ)) with hSp
  have hsub : ∀ b ∈ X.LZ g, kap b ∈ Sp := fun b hb =>
    Submodule.subset_span ((mem_Lc X g).2 ⟨b, hb, rfl⟩)
  have hcr := cr_pos (E := E) g hg
  have hposition : ∀ (i0 k0 : Fin 2), (∀ a : E, cc a = a → IsIntegral ℤ a →
      intersection_update_fsHerm_neg_one i0 k0 (cr (E := E) g • fun τ : X.Ψ => (τ.1 a).re) ∈ Sp) → ∀ p, intersection_update_fsHerm_neg_one i0 k0 p ∈ Sp := by
    intro i0 k0 h p
    have := span_gen X g ((intersection_update_fsHerm_neg_one i0 k0).comp (cr (E := E) g • LinearMap.id)) (fun a ha hai => by
      simpa using h a ha hai) ((cr (E := E) g)⁻¹ • p)
    simpa [smul_smul, inv_mul_cancel₀ hcr.ne'] using this
  have h00 : ∀ p, intersection_update_fsHerm_neg_one 0 0 p ∈ Sp := hposition 0 0 fun a ha hai => by
    have hm := mem_LZ_of X g !![a, 0; 0, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h11 : ∀ p, intersection_update_fsHerm_neg_one 1 1 p ∈ Sp := hposition 1 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, 0; 0, a]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE]
  have h01 : ∀ p, intersection_update_fsHerm_neg_one 0 1 p ∈ Sp := hposition 0 1 fun a ha hai => by
    have hm := mem_LZ_of X g !![0, a; a, 0]
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [ha, RealEmbeddingCharacters.cc_zero'])
      (fun i k => by fin_cases i <;> fin_cases k <;> simp [hai, isIntegral_zero])
    convert hsub _ hm using 1
    funext τ i k
    fin_cases i <;> fin_cases k <;> simp [kap, position_apply, Data.embH, emb_cE, im_of_fixed ha]
  obtain ⟨η, hηcc, hηi, hηne⟩ : ∃ η : E, cc η = -η ∧ IsIntegral ℤ η ∧ η ≠ 0 := by
    have halg : IsAlgebraic ℤ X.ξ0 :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic X.ξ0)
    obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
    refine ⟨k • X.ξ0, ?_, hki, smul_ne_zero hk X.ξ0_ne⟩
    rw [show cc (k • X.ξ0) = k • cc X.ξ0 from map_zsmul _ k _, X.ξ0_im, smul_neg]
  have hre : ∀ τ : E →+* ℂ, (τ η).re = 0 := fun τ => by
    have h := emb_cc' τ η
    rw [hηcc, map_neg] at h
    have := congrArg Complex.re h
    simp at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ η).im ≠ 0 := fun τ h => by
    have : τ η = 0 := Complex.ext (hre τ) h
    exact hηne ((map_eq_zero τ).1 this)
  have h10 : ∀ p, intersection_update_fsHerm_neg_one 1 0 p ∈ Sp := by
    set D : (X.Ψ → ℝ) →ₗ[ℝ] (X.Ψ → ℝ) :=
      LinearMap.pi fun τ : X.Ψ => (cr (E := E) g * (τ.1 η).im) • LinearMap.proj τ with hD
    have hDapp : ∀ q τ, D q τ = cr (E := E) g * (τ.1 η).im * q τ := fun q τ => by simp [hD]
    have key : ∀ q, (intersection_update_fsHerm_neg_one 1 0).comp D q ∈ Sp := span_gen X g _ fun a ha hai => by
      have hm := mem_LZ_of X g !![0, η * a; -(η * a), 0]
        (fun i k => by
          fin_cases i <;> fin_cases k <;>
            simp [ha, RealEmbeddingCharacters.cc_zero', cc_mul'', hηcc, RealEmbeddingCharacters.cc_neg'])
        (fun i k => by fin_cases i <;> fin_cases k <;> simp [(hηi.mul hai), (hηi.mul hai).neg, isIntegral_zero])
      convert hsub _ hm using 1
      funext τ i k
      rw [LinearMap.comp_apply]
      fin_cases i <;> fin_cases k <;>
        simp [kap, position_apply, Data.embH, emb_cE, hDapp, Complex.mul_re, Complex.mul_im, hre,
          im_of_fixed ha]
      ring
    intro p
    have e : D (fun τ => p τ / (cr (E := E) g * (τ.1 η).im)) = p := by
      funext τ
      rw [hDapp]
      have : cr (E := E) g * (τ.1 η).im ≠ 0 := mul_ne_zero hcr.ne' (him τ.1)
      field_simp [him τ.1]
    have := key (fun τ => p τ / (cr (E := E) g * (τ.1 η).im))
    rwa [LinearMap.comp_apply, e] at this
  refine eq_top_iff.2 fun y _ => ?_
  rw [sum_position y]
  refine Submodule.sum_mem _ fun i0 _ => Submodule.sum_mem _ fun k0 _ => ?_
  fin_cases i0 <;> fin_cases k0
  exacts [h00 _, h01 _, h10 _, h11 _]

/- English proof (translation)
Establish `: Fact (0 < g)` using `⟨hg⟩`. Establish `: IsZLattice ℝ (Lc X g)` using `⟨span_Lc X g hg⟩`. Use `ZLattice.module_free ℝ (Lc X g)` as an intermediate fact. Use `ZLattice.module_finite ℝ (Lc X g)` as an intermediate fact. Establish `hrank : Module.finrank ℤ (Lc X g) = 4 * Fintype.card X.Ψ`.

Rewrite using `[ZLattice.rank ℝ (Lc X g), finrank_rfam]`. Use `set bZ := Module.finBasisOfFinrankEq ℤ (Lc X g) hrank`. Use `set eR := bZ.ofZLatticeBasis ℝ (Lc X g)`. Establish `heR : ∀ j, eR j = (bZ j : X.Ψ → Fin 2 → Fin 2 → ℝ)` using `fun j => bZ.ofZLatticeBasis_apply ℝ (Lc X g) j`. Establish `hthinj : LinearMap.ker (thL : (X.Ψ → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] _) = ⊥`.

Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `z z' h`. Rewrite using `[← kap_th z, ← kap_th z']`. Conclude with `congrArg kap h`. Establish `hli : LinearIndependent ℝ (fun j => th (eR j))` using `eR.linearIndependent.map' thL hthinj`.

Establish `hc : ∀ (m : ℤ) (v : X.Ψ → Fin 2 → Fin 2 → ℂ), (m : ℂ) • v = (m : ℝ) • v` using `fun m v => by`. Rewrite using `[← Complex.ofReal_intCast, Complex.coe_smul]`. Use `⟨fun j => th (eR j), fun j => ?_, fun b hb => ?_, hli⟩` and prove the remaining obligations. Take `⟨b, hb, hkb⟩` from `(mem_Lc X g).1 (show eR j ∈ Lc X g by rw [heR]; exact (bZ j).2) show th (eR j) ∈ X.LZ g`. Rewrite using `[← hkb, th_kap (herm_of_LZ X g hb)]`.

Conclude with `hb`. Establish `hmem : kap b ∈ Lc X g` using `(mem_Lc X g).2 ⟨b, hb, rfl⟩ set n := bZ.repr ⟨kap b, hmem⟩`. Establish `h1` using `congrArg Subtype.val (bZ.sum_repr ⟨kap b, hmem⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1`. Establish `hb' : b = ∑ j, (n j : ℂ) • th (eR j)`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[heR, Int.cast_smul_eq_zsmul]`.

Use `_ = ∑ j, (n j : ℂ) • th (eR j) := by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hc]`. Both sides reduce to the same expression.

Use `⟨n, hb', fun n' hn' => ?_⟩` and prove the remaining obligations. Establish `e : ∑ j, (n' j : ℝ) • th (eR j) = ∑ j, (n j : ℝ) • th (eR j)`. Use `hn'.symm.trans hb'` as an intermediate fact. Simplify `this` using `only [hc]`. Establish `hz` using `Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by`.

Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Rewrite using `[e, sub_self])`. Use function extensionality and compare the values at `j`. Use `sub_eq_zero.1 (hz j)` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem exists_basis (hg : 0 < g) : ∃ ω, X.IsLZBasis g ω := by
  have : Fact (0 < g) := ⟨hg⟩
  have : IsZLattice ℝ (Lc X g) := ⟨span_Lc X g hg⟩
  have := ZLattice.module_free ℝ (Lc X g)
  have := ZLattice.module_finite ℝ (Lc X g)
  have hrank : Module.finrank ℤ (Lc X g) = 4 * Fintype.card X.Ψ := by
    rw [ZLattice.rank ℝ (Lc X g), finrank_rfam]
  set bZ := Module.finBasisOfFinrankEq ℤ (Lc X g) hrank
  set eR := bZ.ofZLatticeBasis ℝ (Lc X g)
  have heR : ∀ j, eR j = (bZ j : X.Ψ → Fin 2 → Fin 2 → ℝ) := fun j =>
    bZ.ofZLatticeBasis_apply ℝ (Lc X g) j
  have hthinj : LinearMap.ker (thL : (X.Ψ → Fin 2 → Fin 2 → ℝ) →ₗ[ℝ] _) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro z z' h
    rw [← kap_th z, ← kap_th z']
    exact congrArg kap h
  have hli : LinearIndependent ℝ (fun j => th (eR j)) := eR.linearIndependent.map' thL hthinj
  have hc : ∀ (m : ℤ) (v : X.Ψ → Fin 2 → Fin 2 → ℂ), (m : ℂ) • v = (m : ℝ) • v := fun m v => by
    rw [← Complex.ofReal_intCast, Complex.coe_smul]
  refine ⟨fun j => th (eR j), fun j => ?_, fun b hb => ?_, hli⟩
  · obtain ⟨b, hb, hkb⟩ := (mem_Lc X g).1 (show eR j ∈ Lc X g by rw [heR]; exact (bZ j).2)
    show th (eR j) ∈ X.LZ g
    rw [← hkb, th_kap (herm_of_LZ X g hb)]
    exact hb
  · have hmem : kap b ∈ Lc X g := (mem_Lc X g).2 ⟨b, hb, rfl⟩
    set n := bZ.repr ⟨kap b, hmem⟩
    have h1 := congrArg Subtype.val (bZ.sum_repr ⟨kap b, hmem⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower] at h1
    have hb' : b = ∑ j, (n j : ℂ) • th (eR j) := by
      calc b = thL (kap b) := (th_kap (herm_of_LZ X g hb)).symm
        _ = thL (∑ j, ((n j : ℝ)) • eR j) := by
            congr 1
            rw [← h1]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [heR, Int.cast_smul_eq_zsmul]
        _ = ∑ j, (n j : ℂ) • th (eR j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, hc]
            rfl
    refine ⟨n, hb', fun n' hn' => ?_⟩
    have e : ∑ j, (n' j : ℝ) • th (eR j) = ∑ j, (n j : ℝ) • th (eR j) := by
      have := hn'.symm.trans hb'
      simpa only [hc] using this
    have hz := Fintype.linearIndependent_iff.1 hli (fun j => (n' j : ℝ) - n j) (by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [e, sub_self])
    funext j
    have := sub_eq_zero.1 (hz j)
    exact_mod_cast this

end

end ReciprocityTheory.ChartRestriction.G.FD.FixedPointImaginarySpan
