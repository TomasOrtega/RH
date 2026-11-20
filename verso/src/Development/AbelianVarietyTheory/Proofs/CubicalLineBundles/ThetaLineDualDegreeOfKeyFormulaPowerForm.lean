import Mathlib
import Formalism.LocalToGlobal.CMDeterminantIdeals.LambdaLowerBound
import ReciprocityTheory.SemistableReduction.LemmaH
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula

noncomputable section

open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

/- English proof (translation)
Use `⟨div_ne_zero (pow_ne_zero _ ha.1) (pow_ne_zero _ hb.1), ?_⟩` and prove the remaining obligations. Establish `hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ≠ 0`. Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `ha.1`. Establish `hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ≠ 0`.

Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `hb.1`. Establish `hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ca ^ m / cd ^ n) = FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ^ m * (FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ^ n)⁻¹`. Rewrite using `[FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv]`. Rewrite using `[hs, FractionalIdeal.count_mul K p (pow_ne_zero _ hsa) (inv_ne_zero (pow_ne_zero _ hsb)), FractionalIdeal.count_mul K p (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)), FractionalIdeal.count_inv, FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow, …`.
-/
theorem isLocGen_pow_div_pow {K : Type} [Field K] [NumberField K] {p : HeightOneSpectrum (𝓞 K)} {ca cd : K}
    {A B : FractionalIdeal (𝓞 K)⁰ K} (m n : ℕ) (hA : A ≠ 0) (hB : B ≠ 0) (ha : IsLocGen p ca A) (hb : IsLocGen p cd B) :
    IsLocGen p (ca ^ m / cd ^ n) (A ^ m * (B ^ n)⁻¹) := by
  refine ⟨div_ne_zero (pow_ne_zero _ ha.1) (pow_ne_zero _ hb.1), ?_⟩
  have hsa : FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact ha.1
  have hsb : FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hb.1
  have hs : FractionalIdeal.spanSingleton (𝓞 K)⁰ (ca ^ m / cd ^ n) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ ca ^ m * (FractionalIdeal.spanSingleton (𝓞 K)⁰ cd ^ n)⁻¹ := by
    rw [FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_pow, FractionalIdeal.spanSingleton_inv,
      FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_mul_inv]
  rw [hs, FractionalIdeal.count_mul K p (pow_ne_zero _ hsa) (inv_ne_zero (pow_ne_zero _ hsb)),
    FractionalIdeal.count_mul K p (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, FractionalIdeal.count_pow, FractionalIdeal.count_pow,
    FractionalIdeal.count_pow, FractionalIdeal.count_pow, ha.2, hb.2]

/- English proof (translation)
Introduce `hKF K _ _ x T abelian₂ hT hL hloc harch`. Take `⟨N, hN, κ, hH, hF, hU1, -, hU2⟩` from `hKF`. Take `⟨n, hn⟩ : ∃ n, n = N x.P.g` from `⟨_, rfl⟩`. Establish `hn1 : 1 ≤ n` using `hn ▸ hN _`. Establish `hn' : (n : ℝ) ≠ 0` using `by exact_mod_cast (by omega : n ≠ 0)`.

Use `set k : K := (κ K x : K) with hkdef`. Establish `hk : k ≠ 0` using `(κ K x).ne_zero`. Establish `hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧ p.valuation K k ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n)) ∧ p.valuation K k⁻¹ ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n))⁻¹`. Introduce `p`. Take `⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩` from `hloc p`.

Take `⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩` from `hInt`. Establish `hFx : (κ K' x' : K') = f k` using `hF K K' f x x' hPB`. Establish `hg : x'.P.g = x.P.g` using `by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg`. Establish `hn2 : N x'.P.g = n` using `by rw [hg, hn]`. Establish `hHx : a ^ (8 * N x'.P.g) * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') = M.det ^ (4 * N x'.P.g) * (κ K' x' : K')` using `hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq`.

Take `⟨u, hu, -⟩` from `hU1 R K' xR _ hPBR`. Rewrite `hHx` using `[hn2, hu, hFx, hMdet, ha, hd]`. Generalize the expression as in `8 * n = r at hHx ⊢`. Generalize the expression as in `4 * n = s at hHx ⊢`. Establish `hfa : f ca ≠ 0` using `(map_ne_zero f).2 hca.1`.

Establish `hfd : f cd ≠ 0` using `(map_ne_zero f).2 hcd.1`. Establish `hD : algebraMap R K' (ud : R) ≠ 0` using `(ud.isUnit.map (algebraMap R K')).ne_zero`. Establish `hc : ca ^ r / cd ^ s ≠ 0` using `div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)`. Establish `hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ r * algebraMap R K' (u : R) / (f cd * algebraMap R K' (ud : R)) ^ s`. Rewrite using `[eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hw : f (k / (ca ^ r / cd ^ s)) = algebraMap R K' ((ua ^ r * u * ud⁻¹ ^ s : Rˣ) : R)`. Rewrite using `[Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul, map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk, mul_pow, mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hw' : f (k⁻¹ / (ca ^ r / cd ^ s)⁻¹) = algebraMap R K' (((ua ^ r * u * ud⁻¹ ^ s)⁻¹ : Rˣ) : R)`.

Rewrite using `[inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]`. Conclude with `⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw, valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩`. Establish `hJ : T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ ≠ 0` using `mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))`. Establish `hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹`. Establish `hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0`.

Rewrite using `[Ne, FractionalIdeal.spanSingleton_eq_zero_iff]`. Conclude with `hk`. Use `eq_of_count_eq hsk hJ (fun p => ?_)` and prove the remaining obligations. Take `⟨ca, cd, h1, h2, h3, h4⟩` from `hloc' p`. Establish `h5` using `isLocGen_pow_div_pow (8 * n) (4 * n) hT.1 hL.1 h1 h2`.

Rewrite using `[count_eq_of_valuation_le p hk h5.1 h3 h4, h5.2]`. Establish `hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0`. Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)` after adjusting the coercions. Establish `hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0`. Conclude with `(FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)` after adjusting the coercions.

Establish `hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) = n * (8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) - 4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ))`. Rewrite using `[hspan, map_mul, map_inv₀, map_pow, map_pow]`. Use `push_cast`. Rewrite using `[Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow, Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * n * Real.log (T.n σ) - 4 * n * Real.log (abelian₂.n σ) = 2 * (x.P.g : ℝ) * n * Real.log (2 * Real.pi)`. Introduce `σ`. Take `⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩` from `harch σ`. Establish `hFσ : (κ ℂ xσ : ℂ) = σ k` using `hF K ℂ σ x xσ hPB`.

Take `⟨_, _, _, hg, _⟩` from `hPB`. Establish `he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹`. Rewrite using `[hLn, inv_div]`. Establish `hU` using `hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl`. Rewrite `hU` using `[he, hFσ, hg, ← hn]`.

Establish `hsk0 : 0 < ‖σ k‖` using `norm_pos_iff.2 ((map_ne_zero σ).2 hk)`. Establish `ht` using `hT.2 σ`. Establish `hl` using `hL.2 σ`. Use `congrArg Real.log hU` as an intermediate fact. Rewrite `this` using `[Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]`.

Simplify using `only [Real.log_pow, Real.log_inv] at this`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)`. Rewrite `hsum` using `[Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, sum_log_norm_embeddings hk, hNk]`.

Simplify using `only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]`. Use `mul_left_cancel₀ hn' ?_` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thetaLine_dual_deg_of_keyFormulaPow : GlobalTheory.KeyFormulaPow → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K)
    (T abelian₂ : MLine K), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) →
    T.dual.deg = (1 / 2) * abelian₂.dual.deg + (x.P.g : ℝ) / 4 * (Module.finrank ℚ K : ℝ) * Real.log (2 * Real.pi) := by
  intro hKF K _ _ x T abelian₂ hT hL hloc harch
  obtain ⟨N, hN, κ, hH, hF, hU1, -, hU2⟩ := hKF
  obtain ⟨n, hn⟩ : ∃ n, n = N x.P.g := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := hn ▸ hN _
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  set k : K := (κ K x : K) with hkdef
  have hk : k ≠ 0 := (κ K x).ne_zero
  have hloc' : ∀ p : HeightOneSpectrum (𝓞 K), ∃ ca cd : K, IsLocGen p ca T.I ∧ IsLocGen p cd abelian₂.I ∧
      p.valuation K k ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n)) ∧
      p.valuation K k⁻¹ ≤ p.valuation K (ca ^ (8 * n) / cd ^ (4 * n))⁻¹ := by
    intro p
    obtain ⟨K', _, _, R, _, _, _, _, _, f, x', a, d, ca, cd, ua, ud, hPB, hInt, hval, ha, hd, hca, hcd⟩ := hloc p
    obtain ⟨th', hth', v', hv', M, xR, hth'eq, hv'eq, hMdet, hPBR⟩ := hInt
    have hFx : (κ K' x' : K') = f k := hF K K' f x x' hPB
    have hg : x'.P.g = x.P.g := by obtain ⟨-, -, -, hg, -⟩ := hPB; exact hg
    have hn2 : N x'.P.g = n := by rw [hg, hn]
    have hHx : a ^ (8 * N x'.P.g) * (κ K' ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th', hth', v', hv'⟩ : K') =
        M.det ^ (4 * N x'.P.g) * (κ K' x' : K') :=
      hH K' x'.P x'.g_pos x'.rig x'.rig_gen x'.th x'.th_ne x'.v x'.basis th' hth' v' hv' a M hth'eq hv'eq
    obtain ⟨u, hu, -⟩ := hU1 R K' xR _ hPBR
    rw [hn2, hu, hFx, hMdet, ha, hd] at hHx
    generalize 8 * n = r at hHx ⊢
    generalize 4 * n = s at hHx ⊢
    have hfa : f ca ≠ 0 := (map_ne_zero f).2 hca.1
    have hfd : f cd ≠ 0 := (map_ne_zero f).2 hcd.1
    have hD : algebraMap R K' (ud : R) ≠ 0 := (ud.isUnit.map (algebraMap R K')).ne_zero
    have hc : ca ^ r / cd ^ s ≠ 0 := div_ne_zero (pow_ne_zero _ hca.1) (pow_ne_zero _ hcd.1)
    have hfk : f k = (f ca * algebraMap R K' (ua : R)) ^ r * algebraMap R K' (u : R) /
        (f cd * algebraMap R K' (ud : R)) ^ s := by
      rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero hfd hD)), hHx]; ring
    have hw : f (k / (ca ^ r / cd ^ s)) = algebraMap R K' ((ua ^ r * u * ud⁻¹ ^ s : Rˣ) : R) := by
      rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_mul,
        map_pow, map_pow, map_units_inv, map_div₀, map_div₀, map_pow, map_pow, hfk, mul_pow, mul_pow, inv_pow]
      field_simp
    have hw' : f (k⁻¹ / (ca ^ r / cd ^ s)⁻¹) = algebraMap R K' (((ua ^ r * u * ud⁻¹ ^ s)⁻¹ : Rˣ) : R) := by
      rw [inv_div_inv, ← inv_div, map_inv₀, hw, map_units_inv]
    exact ⟨ca, cd, hca, hcd, valuation_le_of_eq_algebraMap p f hval hc _ hw,
      valuation_le_of_eq_algebraMap p f hval (inv_ne_zero hc) _ hw'⟩
  have hJ : T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hT.1) (inv_ne_zero (pow_ne_zero _ hL.1))
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ k = T.I ^ (8 * n) * (abelian₂.I ^ (4 * n))⁻¹ := by
    have hsk : FractionalIdeal.spanSingleton (𝓞 K)⁰ k ≠ 0 := by
      rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hk
    refine eq_of_count_eq hsk hJ (fun p => ?_)
    obtain ⟨ca, cd, h1, h2, h3, h4⟩ := hloc' p
    have h5 := isLocGen_pow_div_pow (8 * n) (4 * n) hT.1 hL.1 h1 h2
    rw [count_eq_of_valuation_le p hk h5.1 h3 h4, h5.2]
  have hNT : ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hT.1)
  have hNL : ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ) ≠ 0 := by
    exact_mod_cast (FractionalIdeal.absNorm_eq_zero_iff.not.2 hL.1)
  have hNk : Real.log ((FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ k) : ℚ) : ℝ) =
      n * (8 * Real.log ((FractionalIdeal.absNorm T.I : ℚ) : ℝ) -
        4 * Real.log ((FractionalIdeal.absNorm abelian₂.I : ℚ) : ℝ)) := by
    rw [hspan, map_mul, map_inv₀, map_pow, map_pow]
    push_cast
    rw [Real.log_mul (pow_ne_zero _ hNT) (inv_ne_zero (pow_ne_zero _ hNL)), Real.log_inv, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have harch' : ∀ σ : K →+* ℂ, Real.log ‖σ k‖ + 8 * n * Real.log (T.n σ) - 4 * n * Real.log (abelian₂.n σ) =
      2 * (x.P.g : ℝ) * n * Real.log (2 * Real.pi) := by
    intro σ
    obtain ⟨xσ, u, Hm, W, χ, θ, Fd, hPB, hAH, hRig, hFn, hDiff, hFD, hTn, hLn⟩ := harch σ
    have hFσ : (κ ℂ xσ : ℂ) = σ k := hF K ℂ σ x xσ hPB
    obtain ⟨_, _, _, hg, _⟩ := hPB
    have he : (volume Fd).toReal / (Real.pi ^ xσ.P.g * ‖W.det‖ ^ 2) = (abelian₂.n σ ^ 2)⁻¹ := by
      rw [hLn, inv_div]
    have hU := hU2 xσ u Hm W χ θ Fd _ _ hAH hRig hFn hDiff hFD hTn rfl
    rw [he, hFσ, hg, ← hn] at hU
    have hsk0 : 0 < ‖σ k‖ := norm_pos_iff.2 ((map_ne_zero σ).2 hk)
    have ht := hT.2 σ
    have hl := hL.2 σ
    have := congrArg Real.log hU
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)] at this
    simp only [Real.log_pow, Real.log_inv] at this
    push_cast at this
    linarith
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (K →+* ℂ))) rfl (fun σ _ => harch' σ)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, NumberField.Embeddings.card K ℂ, nsmul_eq_mul, sum_log_norm_embeddings hk, hNk] at hsum
  simp only [MLine.deg, MLine.dual, map_inv₀, Rat.cast_inv, Real.log_inv, Finset.sum_neg_distrib]
  refine mul_left_cancel₀ hn' ?_
  linarith

end GlobalTheory
