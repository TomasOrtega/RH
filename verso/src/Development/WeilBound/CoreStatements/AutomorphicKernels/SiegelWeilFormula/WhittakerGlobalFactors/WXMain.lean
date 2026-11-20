import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.ExistsFinsetOfCofinite
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.W

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix

/- English proof (translation)
Introduce `hLoc hUnr hReal hFac hSDL F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok hrange _ ht μH 𝓕 hμH h𝓕`. Establish `hlt : n < M` using `hok`. Establish `hra : n + 2 ≤ M ∨ PositivityTheory.PfSWUS.HMass.IsAnisoH σ J`. Break down `hrange with h | h` into its components or cases. Conclude with `Or.inl h`.

Conclude with `Or.inr fun x hx hx0 => hx (h x hx0)`. Rewrite using `[one_mul]`. Take `⟨t, ht⟩` from `ht`. Establish `hT` using `hD.hT`. Establish `h0` using `hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs 0 0 Φf Φv isSchwartzInf_zero hD.pure (fun X => by simp)`.

Establish `h1` using `((h0.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr`. Take `⟨μi, hμi⟩` from `h1.1`. Take `⟨νi, hνi⟩` from `(h1.2 μi hμi).1`. Take `⟨μv, hμv⟩` from `((h1.2 μi hμi).2 νi hνi).1`. Take `⟨νv, hνv⟩` from `(((h1.2 μi hμi).2 νi hνi).2 μv hμv).1`.

Establish `hR` using `hReal F E σ hD.cm M J hD.herm n hlt ψ hD.chr ι θ l hD.places ε fr hD.frames g P μi νi hμi hνi`. Establish `h2` using `hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs Φ (phiInf θ l fr g P) Φf Φv hR.1 hD.pure hD.prod`. Take `⟨ginf, gv, hdinf, hdv, hmult, hmean⟩` from `(((((h2.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr).2 μi hμi).2 νi hνi).2 μv hμv |>.2 νv hνv`. Take `⟨Wi, hWi, hWi0, ti, hti⟩` from `hR.2 ginf hdinf (hermOf (Ainf F) σ T hT) (hermOf_unit σ T hT hD.det _)`. Establish `hL` using `fun v => hLoc F E σ hD.cm M J hD.herm n hlt ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v) (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) (gv v) (hdv v) (hermOf (Fv F v) σ T hT) (hermOf_unit σ T hT hD.det _)`.

Use `choose Wv hWv hWv0 tv htv using hL`. Take `⟨tu, hU⟩` from `hUnr F E σ hD.cm M J hD.herm n hlt T hT hD.det d bs ψ hD.chr`. Establish `hev` using `(hU.and hD.std).and hD.pure.2.1`. Take `⟨S, hSout⟩` from `exists_finset_of_cofinite hev`. Use `choose! e he using fun v (hv : v ∉ S) => (hSout v hv).1.1`.

Establish `hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re → Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z) (νv v) ∧ ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) = unr …`. Introduce `v hv z hz`. Take `⟨⟨-, hs1, hs2⟩, hpv⟩` from `hSout v hv`. Establish `hL12 : L₂ v = L₁ v` using `SetLike.coe_injective (hs2.trans hs1.symm)`. Rewrite using `[hL12, hpv]`.

Conclude with `he v hv (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz`. Establish `hgv : ∀ v, v ∉ S → gv v (hermOf (Fv F v) σ T hT) = unrP n M (e v) (Ideal.absNorm v.asIdeal) (((M : ℂ) - n) / 2)`. Introduce `v hv`. Establish `hq : Ideal.absNorm v.asIdeal ≠ 0`. Use `NumberField.HeightOneSpectrum.one_lt_absNorm v` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `heq` using `eq_of_eqOn_right (hWv v) (unramifiedPart_differentiable n M (e v) _ hq) (max (tv v) tu) fun z hz => ((htv v z (lt_of_le_of_lt (le_max_left _ _) hz)).2).trans ((hPv v hv z (lt_of_le_of_lt (le_max_right _ _) hz)).2)`. Rewrite using `[← hWv0 v, heq]`. Take `⟨D, hDd, hDp⟩` from `unr_prod (F := F) n M (↑S : Set (HeightOneSpectrum (𝓞 F))) e`. Establish `hs0 : (0 : ℝ) < (((M : ℂ) - n) / 2).re`.

Establish `: (n : ℝ) < M` using `by exact_mod_cast hlt`. Establish `h : (((M : ℂ) - n) / 2) = ((((M : ℝ) - n) / 2 : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[h, Complex.ofReal_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `U : Set ℂ` to `{z | 0 < z.re}`.

Establish `hUo : IsOpen U` using `isOpen_lt continuous_const Complex.continuous_re`. Set `G : ℂ → ℂ` to `fun z => Wi z * ((∏ v ∈ S, Wv v z) * D z)`. Establish `hGd : DifferentiableOn ℂ G U` using `hWi.differentiableOn.mul ((DifferentiableOn.fun_finsetProd fun v _ => (hWv v).differentiableOn).mul hDd)`. Establish `hGs0 : G (((M : ℂ) - n) / 2) = meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T})`. Establish `hp` using `hasProd_split (fun v => gv v (hermOf (Fv F v) σ T hT)) S (D (((M : ℂ) - n) / 2)) (by`.

Use `hDp _ hs0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Conclude with `hgv v.1 v.2)`. Use `show Wi _ * ((∏ v ∈ S, Wv v _) * D _) = _`. Rewrite using `[hmean, hp.tprod_eq, hWi0, Finset.prod_congr rfl fun v _ => hWv0 v]`.

Establish `hright : Set.EqOn G (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν) (rightOf (|t| + |ti| + |tu| + ∑ v ∈ S, |tv v|))`. Introduce `z hz`. Establish `hz' : |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| < z.re` using `hz`. Establish `hsum : 0 ≤ ∑ v ∈ S, |tv v|` using `Finset.sum_nonneg fun v _ => abs_nonneg _`. Establish `zt : t < z.re` using `by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]`.

Establish `zti : ti < z.re` using `by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]`. Establish `ztu : tu < z.re` using `by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]`. Establish `z0 : 0 < z.re` using `by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]`. Establish `ztv : ∀ v ∈ S, tv v < z.re` using `fun v hv => by`. Use `Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv` as an intermediate fact.

Combine the linear relations using `[le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]`. Establish `hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z) (νv v)`. Introduce `v`. Distinguish the cases in `hv : v ∈ S`. Conclude with `(htv v z (ztv v hv)).1`.

Conclude with `(hPv v hv z ztu).1`. Establish `hF` using `hFac F E σ M n d J T bs ψ ι θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z (ht z zt) (hti z zti).1 hint`. Establish `hp` using `hasProd_split (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) S (D z) (by`. Use `hDp z z0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`.

Conclude with `(hPv v.1 v.2 z ztu).2)`. Establish `hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ …` using `hp`. Establish `hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi = Wi z` using `(hti z zti).2.symm`. Rewrite `hF` using `[hIi]`. Establish `hu` using `tendsto_nhds_unique hF (hlim.const_mul (Wi z))`.

Use `show Wi z * ((∏ v ∈ S, Wv v z) * D z) = _`. Rewrite using `[Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]`. Conclude with `hu.symm`. Use `⟨G, ⟨U, hs0, ⟨⟨0, fun z hz => hz⟩, fun s hs r hr => ?_⟩, (hGd.analyticOnNhd hUo).meromorphicOn, ⟨_, hright⟩⟩, hGd.analyticOnNhd hUo _ hs0, hGs0⟩` and prove the remaining obligations. Establish `hs' : 0 < s.re` using `hs`.

Use `show 0 < (s + r).re`. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem whitGenLtOf : LocFin2 → UnrWhit → RealWhit → FactorX → PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA → WhitGenLt := by
  intro hLoc hUnr hReal hFac hSDL F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok hrange _ ht
    μH 𝓕 hμH h𝓕
  have hlt : n < M := hok
  have hra : n + 2 ≤ M ∨ PositivityTheory.PfSWUS.HMass.IsAnisoH σ J := by
    rcases hrange with h | h
    · exact Or.inl h
    · exact Or.inr fun x hx hx0 => hx (h x hx0)
  rw [one_mul]
  obtain ⟨t, ht⟩ := ht
  have hT := hD.hT

  have h0 := hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs 0 0 Φf Φv isSchwartzInf_zero hD.pure
    (fun X => by simp)
  have h1 := ((h0.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr
  obtain ⟨μi, hμi⟩ := h1.1
  obtain ⟨νi, hνi⟩ := (h1.2 μi hμi).1
  obtain ⟨μv, hμv⟩ := ((h1.2 μi hμi).2 νi hνi).1
  obtain ⟨νv, hνv⟩ := (((h1.2 μi hμi).2 νi hνi).2 μv hμv).1

  have hR := hReal F E σ hD.cm M J hD.herm n hlt ψ hD.chr ι θ l hD.places ε fr hD.frames g P μi νi hμi hνi

  have h2 := hSDL F E σ hD.cm M J hD.herm n hlt hra T hT hD.det d bs Φ (phiInf θ l fr g P) Φf Φv hR.1 hD.pure hD.prod
  obtain ⟨ginf, gv, hdinf, hdv, hmult, hmean⟩ :=
    (((((h2.2 μH hμH).2 𝓕 h𝓕).2 ψ hD.chr).2 μi hμi).2 νi hνi).2 μv hμv |>.2 νv hνv
  obtain ⟨Wi, hWi, hWi0, ti, hti⟩ := hR.2 ginf hdinf (hermOf (Ainf F) σ T hT) (hermOf_unit σ T hT hD.det _)

  have hL := fun v => hLoc F E σ hD.cm M J hD.herm n hlt ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v)
    (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) (gv v) (hdv v) (hermOf (Fv F v) σ T hT)
    (hermOf_unit σ T hT hD.det _)
  choose Wv hWv hWv0 tv htv using hL

  obtain ⟨tu, hU⟩ := hUnr F E σ hD.cm M J hD.herm n hlt T hT hD.det d bs ψ hD.chr
  have hev := (hU.and hD.std).and hD.pure.2.1
  obtain ⟨S, hSout⟩ := exists_finset_of_cofinite hev
  choose! e he using fun v (hv : v ∉ S) => (hSout v hv).1.1
  have hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) ∧
      ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) =
        unrP n M (e v) (Ideal.absNorm v.asIdeal) z := by
    intro v hv z hz
    obtain ⟨⟨-, hs1, hs2⟩, hpv⟩ := hSout v hv
    have hL12 : L₂ v = L₁ v := SetLike.coe_injective (hs2.trans hs1.symm)
    rw [hL12, hpv]
    exact he v hv (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz

  have hgv : ∀ v, v ∉ S →
      gv v (hermOf (Fv F v) σ T hT) = unrP n M (e v) (Ideal.absNorm v.asIdeal) (((M : ℂ) - n) / 2) := by
    intro v hv
    have hq : Ideal.absNorm v.asIdeal ≠ 0 := by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v
      omega
    have heq := eq_of_eqOn_right (hWv v) (unramifiedPart_differentiable n M (e v) _ hq) (max (tv v) tu) fun z hz =>
      ((htv v z (lt_of_le_of_lt (le_max_left _ _) hz)).2).trans
        ((hPv v hv z (lt_of_le_of_lt (le_max_right _ _) hz)).2)
    rw [← hWv0 v, heq]
  obtain ⟨D, hDd, hDp⟩ := unr_prod (F := F) n M (↑S : Set (HeightOneSpectrum (𝓞 F))) e
  have hs0 : (0 : ℝ) < (((M : ℂ) - n) / 2).re := by
    have : (n : ℝ) < M := by exact_mod_cast hlt
    have h : (((M : ℂ) - n) / 2) = ((((M : ℝ) - n) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h, Complex.ofReal_re]
    linarith
  let U : Set ℂ := {z | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  let G : ℂ → ℂ := fun z => Wi z * ((∏ v ∈ S, Wv v z) * D z)
  have hGd : DifferentiableOn ℂ G U :=
    hWi.differentiableOn.mul ((DifferentiableOn.fun_finsetProd fun v _ => (hWv v).differentiableOn).mul hDd)

  have hGs0 : G (((M : ℂ) - n) / 2) = meanC μH 𝓕 (thetaS F E σ M J Φ {X | gramE σ J X = T}) := by
    have hp := hasProd_split (fun v => gv v (hermOf (Fv F v) σ T hT)) S (D (((M : ℂ) - n) / 2)) (by
      convert hDp _ hs0 using 1
      funext v
      exact hgv v.1 v.2)
    show Wi _ * ((∏ v ∈ S, Wv v _) * D _) = _
    rw [hmean, hp.tprod_eq, hWi0, Finset.prod_congr rfl fun v _ => hWv0 v]

  have hright : Set.EqOn G
      (fun z => ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν)
      (rightOf (|t| + |ti| + |tu| + ∑ v ∈ S, |tv v|)) := by
    intro z hz
    have hz' : |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| < z.re := hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    have zt : t < z.re := by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]
    have zti : ti < z.re := by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]
    have ztu : tu < z.re := by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]
    have z0 : 0 < z.re := by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have ztv : ∀ v ∈ S, tv v < z.re := fun v hv => by
      have := Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv
      linarith [le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
    have hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) := by
      intro v
      by_cases hv : v ∈ S
      · exact (htv v z (ztv v hv)).1
      · exact (hPv v hv z ztu).1
    have hF := hFac F E σ M n d J T bs ψ ι θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z
      (ht z zt) (hti z zti).1 hint
    have hp := hasProd_split (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z b ∂(νv v)) S (D z) (by
      convert hDp z z0 using 1
      funext v
      exact (hPv v.1 v.2 z ztu).2)
    have hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v)
        (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop
        (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
          (T.map (inclR (Fv F v))) z b ∂(νv v)) * D z)) := hp
    have hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g P) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi =
        Wi z := (hti z zti).2.symm
    rw [hIi] at hF
    have hu := tendsto_nhds_unique hF (hlim.const_mul (Wi z))
    show Wi z * ((∏ v ∈ S, Wv v z) * D z) = _
    rw [Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]
    exact hu.symm
  refine ⟨G, ⟨U, hs0, ⟨⟨0, fun z hz => hz⟩, fun s hs r hr => ?_⟩, (hGd.analyticOnNhd hUo).meromorphicOn,
    ⟨_, hright⟩⟩, hGd.analyticOnNhd hUo _ hs0, hGs0⟩
  have hs' : 0 < s.re := hs
  show 0 < (s + r).re
  simp
  linarith

end PositivityTheory.SiegelWeilFormula.Gen.W

/- English proof (translation)
The claim follows from `PositivityTheory.SiegelWeilFormula.Gen.W.whitGenLtOf`.
-/
theorem PositivityTheory.SiegelWeilFormula.Gen.whitGenLtOf : PositivityTheory.SiegelWeilFormula.Gen.LocFin2 → PositivityTheory.SiegelWeilFormula.Gen.UnrWhit →
    PositivityTheory.SiegelWeilFormula.Gen.RealWhit → PositivityTheory.SiegelWeilFormula.Gen.FactorX → PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA →
    PositivityTheory.SiegelWeilFormula.Gen.WhitGenLt :=
  PositivityTheory.SiegelWeilFormula.Gen.W.whitGenLtOf

end
