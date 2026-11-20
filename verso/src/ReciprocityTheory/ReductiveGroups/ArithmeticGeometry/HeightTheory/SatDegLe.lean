import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Qdist
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ExistsIntMultiple

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors

/- English proof (translation)
Take `⟨c, G₀, hc, hG₀⟩` from `exists_int_multiple F`. Establish `hG : MvPolynomial.map (algebraMap (𝓞 K) K) G₀ ≠ 0`. Rewrite using `[hG₀]`. Conclude with `mul_ne_zero (by simpa using hc) hF`. Establish `hG₀ne : G₀ ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hG (map_zero _)`. Establish `hSTG : ∀ m ∈ S, (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T`. Introduce `m hm s hs`. Apply `hST m hm` to reduce the goal to its premises.

Rewrite `hs`, the goal using `[MvPolynomial.mem_support_iff]`. Rewrite `hs` using `[hG₀, mul_assoc, MvPolynomial.coeff_C_mul]`. Conclude with `right_ne_zero_of_mul hs`. Use `⟨bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e, ?_, linInd_bG _ hG S T e hSTG, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Use `show _ ∈ Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)`. Rewrite using `[Submodule.mem_pi]`. Introduce `i _`. Rewrite using `[Submodule.mem_one]`. Use `⟨(G₀ * MvPolynomial.monomial (mS S j) 1).coeff (e.symm i : κ →₀ ℕ), ?_⟩` and prove the remaining obligations.

Use `show _ = (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial (mS S j) 1).coeff (e.symm i : κ →₀ ℕ)`. Rewrite using `[← MvPolynomial.coeff_map, map_mul, MvPolynomial.map_monomial, map_one]`. Establish `key : ∀ j, bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e j = c • fun i => (F * MvPolynomial.monomial (S.equivFin.symm j : κ →₀ ℕ) 1).coeff (e.symm i : κ →₀ ℕ)`. Introduce `j`. Use function extensionality and compare the values at `i`.

Simplify using `only [bG, coordVec, mS, hG₀, mul_assoc, MvPolynomial.coeff_C_mul, Pi.smul_apply, smul_eq_mul]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `j`. Simplify using `only [SetLike.mem_coe]`.

Rewrite using `[key j]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨S.equivFin.symm j, rfl⟩)`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `m`. Simplify using `only [SetLike.mem_coe]`.

Establish `h1` using `key (S.equivFin m)`. Rewrite `h1` using `[Equiv.symm_apply_apply]`. Establish `h2 : (fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff (e.symm i : κ →₀ ℕ)) = c⁻¹ • bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e (S.equivFin m)`. Rewrite using `[h1, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Rewrite using `[h2]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ)`. Conclude with `(Module.finrank_pos : 0 < Module.finrank ℚ K)` after adjusting the coercions. Establish `hd' : (Module.finrank ℚ K : ℝ) ≠ 0` using `hd.ne'`. Establish `hTeq : hT F = hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)`.

Rewrite using `[hG₀, hT_C_mul F hF c hc]`. Establish `hTG : (Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) = (∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))) + ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (Mv …`. Rewrite using `[hT]`. Clear the denominators using the available nonvanishing facts. Establish `hnorm : Real.log (Ideal.absNorm (contId G₀) : ℝ) = -∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))`.

Establish `hprod` using `absNorm_mul_gauss G₀ hG₀ne`. Establish `hN` using `left_ne_zero_of_mul_eq_one hprod`. Establish `hP` using `right_ne_zero_of_mul_eq_one hprod`. Establish `hsum` using `finsum_log_eq (fun w : FinitePlace K => ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) (fun w => ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w _ hG) (gaussAbs_mulSupport_finite _ hG)`. Establish `hlog : Real.log (Ideal.absNorm (contId G₀) : ℝ) + Real.log (∏ᶠ w : FinitePlace K, ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) = 0`.

Rewrite using `[← Real.log_mul hN hP, hprod, Real.log_one]`. Rewrite using `[hsum]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `log_relIndex_le G₀ hG₀ne S T e hSTG`. Rewrite `h1` using `[hnorm]`.

Establish `h3 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) ≤ ∑ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ (bG (MvPolynomial.map …` using `Finset.sum_le_sum fun σ _ => gram_le _ hG S T e hSTG σ`. Establish `e1 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) = 2 * (S.card : ℝ) * ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ (MvPolynomial.map (al …`. Rewrite using `[Finset.mul_sum]`. Establish `e2 : (S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F = (S.card : ℝ) * ((Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))`. Rewrite using `[hTeq]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [ReciprocityTheory.MultiplicativeHeights.latDeg]`. Rewrite using `[e2, hTG]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem satDeg_le (K : Type) [Field K] [NumberField K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (F : MvPolynomial κ K) (hF : F ≠ 0) (T S : Finset (κ →₀ ℕ)) {r : ℕ} (e : T ≃ Fin r)
    (hST : ∀ m ∈ S, (F * MvPolynomial.monomial m 1).support ⊆ T) :
    ∃ b : Fin S.card → Fin r → K, (∀ j, b j ∈ stdLat K r) ∧ LinearIndependent K b ∧
      Submodule.span K (Set.range b) =
        Submodule.span K (Set.range fun m : S => fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff
          (e.symm i : κ →₀ ℕ)) ∧
      ReciprocityTheory.MultiplicativeHeights.latDeg (fun _ => 1) (ReciprocityTheory.MultiplicativeHeights.satSub (stdLat K r) b) b ≤
        -((S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F) := by
  obtain ⟨c, G₀, hc, hG₀⟩ := exists_int_multiple F
  have hG : MvPolynomial.map (algebraMap (𝓞 K) K) G₀ ≠ 0 := by
    rw [hG₀]
    exact mul_ne_zero (by simpa using hc) hF
  have hG₀ne : G₀ ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  have hSTG : ∀ m ∈ S,
      (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial m 1).support ⊆ T := by
    intro m hm s hs
    apply hST m hm
    rw [MvPolynomial.mem_support_iff] at hs ⊢
    rw [hG₀, mul_assoc, MvPolynomial.coeff_C_mul] at hs
    exact right_ne_zero_of_mul hs
  refine ⟨bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e, ?_, linInd_bG _ hG S T e hSTG, ?_, ?_⟩
  ·
    intro j
    show _ ∈ Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)
    rw [Submodule.mem_pi]
    intro i _
    rw [Submodule.mem_one]
    refine ⟨(G₀ * MvPolynomial.monomial (mS S j) 1).coeff (e.symm i : κ →₀ ℕ), ?_⟩
    show _ = (MvPolynomial.map (algebraMap (𝓞 K) K) G₀ * MvPolynomial.monomial (mS S j) 1).coeff
      (e.symm i : κ →₀ ℕ)
    rw [← MvPolynomial.coeff_map, map_mul, MvPolynomial.map_monomial, map_one]
  ·
    have key : ∀ j, bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e j =
        c • fun i => (F * MvPolynomial.monomial (S.equivFin.symm j : κ →₀ ℕ) 1).coeff
          (e.symm i : κ →₀ ℕ) := by
      intro j
      funext i
      simp only [bG, coordVec, mS, hG₀, mul_assoc, MvPolynomial.coeff_C_mul, Pi.smul_apply,
        smul_eq_mul]
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      simp only [SetLike.mem_coe]
      rw [key j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨S.equivFin.symm j, rfl⟩)
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro m
      simp only [SetLike.mem_coe]
      have h1 := key (S.equivFin m)
      rw [Equiv.symm_apply_apply] at h1
      have h2 : (fun i => (F * MvPolynomial.monomial (m : κ →₀ ℕ) 1).coeff (e.symm i : κ →₀ ℕ)) =
          c⁻¹ • bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e (S.equivFin m) := by
        rw [h1, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  ·
    have hd : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
    have hd' : (Module.finrank ℚ K : ℝ) ≠ 0 := hd.ne'
    have hTeq : hT F = hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) := by
      rw [hG₀, hT_C_mul F hF c hc]
    have hTG : (Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) =
        (∑ᶠ w : FinitePlace K,
          Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))) +
        ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [hT]
      field_simp
    have hnorm : Real.log (Ideal.absNorm (contId G₀) : ℝ) =
        -∑ᶠ w : FinitePlace K,
          Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      have hprod := absNorm_mul_gauss G₀ hG₀ne
      have hN := left_ne_zero_of_mul_eq_one hprod
      have hP := right_ne_zero_of_mul_eq_one hprod
      have hsum := finsum_log_eq
        (fun w : FinitePlace K => ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀))
        (fun w => ReciprocityTheory.MultiplicativeHeights.gauss_abs_pos_of_ne_zero w _ hG) (gaussAbs_mulSupport_finite _ hG)
      have hlog : Real.log (Ideal.absNorm (contId G₀) : ℝ) + Real.log (∏ᶠ w : FinitePlace K,
          ReciprocityTheory.MultiplicativeHeights.gaussAbs w (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) = 0 := by
        rw [← Real.log_mul hN hP, hprod, Real.log_one]
      rw [hsum]
      linarith
    have h1 := log_relIndex_le G₀ hG₀ne S T e hSTG
    rw [hnorm] at h1
    have h3 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) ≤
        ∑ σ : K →+* ℂ, Real.log (ReciprocityTheory.MultiplicativeHeights.gramC (1 : Matrix (Fin r) (Fin r) ℂ) σ
          (bG (MvPolynomial.map (algebraMap (𝓞 K) K) G₀) S e)).det.re :=
      Finset.sum_le_sum fun σ _ => gram_le _ hG S T e hSTG σ
    have e1 : ∑ σ : K →+* ℂ, 2 * (S.card : ℝ) * ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) =
        2 * (S.card : ℝ) * ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean
          (MvPolynomial.map σ (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [Finset.mul_sum]
    have e2 : (S.card : ℝ) * (Module.finrank ℚ K : ℝ) * hT F =
        (S.card : ℝ) * ((Module.finrank ℚ K : ℝ) * hT (MvPolynomial.map (algebraMap (𝓞 K) K) G₀)) := by
      rw [hTeq]
      ring
    simp only [ReciprocityTheory.MultiplicativeHeights.latDeg]
    rw [e2, hTG]
    linarith

end ReciprocityTheory.ChartRestriction.G.T0
