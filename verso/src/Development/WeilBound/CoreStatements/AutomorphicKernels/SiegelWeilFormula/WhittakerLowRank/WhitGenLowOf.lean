import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerLowRank.AnalyticAtUpdateZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.ExistsFinsetOfCofinite
import Development.AutomorphicSpectrum.Proofs.HermitianForms.ExistsSdWSdHerm
import Development.AutomorphicSpectrum.Proofs.HermitianForms.HasCoordOfFiniteDimensional

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WL

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix Topology

/- English proof (translation)
Introduce `hLoc hUnr hReal hFac hLOrd F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok _ hvac ht μH 𝓕 _ _`. Rewrite using `[zero_mul]`. Take `⟨hlt, -⟩` from `hok`. Take `⟨hP, e, rfl⟩` from `hvac trivial`. Establish `hP' : P = fun _ => 1` using `funext hP`.

Substitute `hP'` using the available equality. Take `⟨t, ht⟩` from `ht`. Establish `hT` using `hD.hT`. Take `⟨⟨μi, hμi⟩, ⟨νi, hνi⟩⟩` from `GlobalTheory.CompanionTheory.SelfDualInf.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr`. Use `choose μv hμv using fun v => (GlobalTheory.CompanionTheory.SdFin.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr v).1`.

Use `choose νv hνv using fun v => (GlobalTheory.CompanionTheory.SdFin.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr v).2`. Take `⟨Wi, hWi, ti, hti⟩` from `hReal F E σ hD.cm M J hD.herm n hlt ψ hD.chr ι θ l hD.places e fr hD.frames g μi νi hμi hνi (hermOf (Ainf F) σ T hT) (W.hermOf_unit σ T hT hD.det _)`. Establish `hL` using `fun v => hLoc F E σ hD.cm M J hD.herm n ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v) (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) 0 (densZero σ J hlt v (μv v) (νv v) (Φv v)) (hermOf (Fv F v) σ T hT) (W.hermOf_unit σ T hT hD.det _)`. Use `choose Wv hWv hWv0 tv htv using hL`. Take `⟨tu, hU⟩` from `hUnr F E σ hD.cm M J hD.herm n T hT hD.det d bs ψ hD.chr`.

Establish `hev` using `(hU.and hD.std).and hD.pure.2.1`. Take `⟨S, hSout⟩` from `W.exists_finset_of_cofinite hev`. Establish `hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re → Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z) (νv v) ∧ ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) = ∏ i …`. Introduce `v hv z hz`. Take `⟨⟨hu, hs1, hs2⟩, hpv⟩` from `hSout v hv`.

Establish `hL12 : L₂ v = L₁ v` using `SetLike.coe_injective (hs2.trans hs1.symm)`. Rewrite using `[hL12, hpv]`. Conclude with `hu (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz`. Use `choose Z hZm hZp H hHa hHe using fun i : Fin n => hLOrd F E σ hD.cm S ((M : ℤ) - (i : ℕ))`. Use `set s₀ : ℂ := ((M : ℂ) - n) / 2 with hs₀`.

Use `set a : ℕ := Module.finrank ℚ F * (n - M) with ha`. Establish `hWv0' : ∀ v, Wv v s₀ = 0` using `fun v => hWv0 v`. Set `G : ℂ → ℂ` to `fun z => ((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))`. Use `set σ₀ : ℝ := |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| + |s₀.re| + 1 with hσ₀`. Establish `hne : ∀ z : ℂ, σ₀ < z.re → z ≠ s₀` using `fun z hz h => by`.

Rewrite `hz` using `[h]`. Establish `hsum : 0 ≤ ∑ v ∈ S, |tv v|` using `Finset.sum_nonneg fun v _ => abs_nonneg _`. Combine the linear relations using `[le_abs_self s₀.re, abs_nonneg t, abs_nonneg ti, abs_nonneg tu]`. Establish `hright : ∀ z : ℂ, σ₀ < z.re → G z = ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν`. Introduce `z hz`.

Establish `hsum : 0 ≤ ∑ v ∈ S, |tv v|` using `Finset.sum_nonneg fun v _ => abs_nonneg _`. Establish `hs0a` using `abs_nonneg s₀.re`. Establish `zt : t < z.re` using `by linarith [le_abs_self t, abs_nonneg ti, abs_nonneg tu]`. Establish `zti : ti < z.re` using `by linarith [le_abs_self ti, abs_nonneg t, abs_nonneg tu]`. Establish `ztu : tu < z.re` using `by linarith [le_abs_self tu, abs_nonneg t, abs_nonneg ti]`.

Establish `z0 : 0 < z.re` using `by linarith [abs_nonneg t, abs_nonneg ti, abs_nonneg tu]`. Establish `ztv : ∀ v ∈ S, tv v < z.re` using `fun v hv => by`. Use `Finset.single_le_sum (f := fun v => |tv v|) (fun v _ => abs_nonneg _) hv` as an intermediate fact. Combine the linear relations using `[le_abs_self (tv v), abs_nonneg t, abs_nonneg ti, abs_nonneg tu]`. Establish `hint : ∀ v, Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z) (νv v)`.

Introduce `v`. Distinguish the cases in `hv : v ∈ S`. Conclude with `(htv v z (ztv v hv)).1`. Conclude with `(hPv v hv z ztu).1`. Establish `hF` using `hFac F E σ M n d J T bs ψ ι θ l (fun i _ => e i) fr g (fun _ => 1) lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv hμi hνi hμv hνv z (ht z zt) (hti z zti).1 hint`.

Establish `hcompl : HasProd (fun v : {v // v ∉ S} => ∫ b, whI (Fv F v.1) σ J (psiV F ψ v.1) (μv v.1) (Φv v.1) (nu2 (lam v.1) (L₁ v.1) (L₂ v.1)) (T.map (inclR (Fv F v.1))) z b ∂(νv v.1)) (∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))`. Establish `hp` using `hasProd_prod (s := (Finset.univ : Finset (Fin n))) fun i _ => hZp i (2 * z + n - (i : ℕ)) (by`. Establish `hi : ((i : ℕ) : ℝ) + 1 ≤ n` using `by exact_mod_cast i.2`. Simplify using `only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.re_ofNat, Complex.im_ofNat]`. Use the proof step `linarith)`.

Use `hp using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `v`. Rewrite using `[(hPv v.1 v.2 z ztu).2]`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [eSp_pow]`. Establish `hp` using `hasProd_split' (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) S _ hcompl`.

Establish `hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ …` using `hp`. Establish `hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g fun _ => 1) (nuInf θ g) (T.map (inclR (Ainf F))) z b ∂νi = (z - s₀) ^ a * Wi z` using `(hti z zti).2.symm`. Rewrite `hF` using `[hIi]`. Establish `hu` using `tendsto_nhds_unique hF (hlim.const_mul ((z - s₀) ^ a * Wi z))`. Use `show ((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ))) = _`.

Rewrite using `[Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]`. Conclude with `hu.symm`. Establish `hd1 : 1 ≤ Module.finrank ℚ F` using `Module.finrank_pos`. Establish `hcount` using `count S.card (Module.finrank ℚ F) M n hd1 hlt`. Use `set K : ℕ := ∑ i : Fin n, (if 1 ≤ (M : ℤ) - ((i : ℕ) : ℤ) then 0 else if (M : ℤ) - ((i : ℕ) : ℤ) = 0 then S.card + Module.finrank ℚ F - 1 else Module.finrank ℚ F) with hK`.

Establish `hKN : K < a + S.card` using `by omega`. Establish `hdsl : ∀ v, AnalyticAt ℂ (dslope (Wv v) s₀) s₀` using `fun v => (differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 (hWv v).differentiableOn)).analyticAt s₀`. Establish `haff : ∀ i : Fin n, ∀ z : ℂ, 2 * z + n - (i : ℕ) - (((M : ℤ) - (i : ℕ) : ℤ) : ℂ) = 2 * (z - s₀)` using `fun i z => by`. Rewrite using `[hs₀]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hHan : ∀ i : Fin n, AnalyticAt ℂ (fun z => H i (2 * z + n - (i : ℕ))) s₀` using `fun i => AnalyticAt.comp_of_eq (g := H i) (f := fun z : ℂ => 2 * z + n - (i : ℕ)) (hHa i) (by fun_prop) (by`. Use `haff i s₀` as an intermediate fact. Rewrite `this` using `[sub_self, mul_zero, sub_eq_zero]`. Conclude with `this)`.

Establish `hA : AnalyticAt ℂ (fun z => Wi z * (∏ v ∈ S, dslope (Wv v) s₀ z) * ∏ i : Fin n, H i (2 * z + n - (i : ℕ))) s₀` using `((hWi.analyticAt s₀).mul (Finset.analyticAt_fun_prod _ fun v _ => hdsl v)).mul (Finset.analyticAt_fun_prod _ fun i _ => hHan i)`. Establish `htend : ∀ i : Fin n, Tendsto (fun z : ℂ => 2 * z + n - (i : ℕ)) (𝓝[≠] s₀) (𝓝[≠] (((M : ℤ) - (i : ℕ) : ℤ) : ℂ))` using `fun i => by`. Use `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_` and prove the remaining obligations. Establish `hc : Continuous (fun z : ℂ => 2 * z + n - (i : ℕ))` using `by fun_prop`. Use `haff i s₀` as an intermediate fact.

Rewrite `this` using `[sub_self, mul_zero, sub_eq_zero]`. Rewrite using `[← this]`. Conclude with `(hc.tendsto s₀).mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with z hz`. Introduce `h`.

Use `haff i z` as an intermediate fact. Rewrite `this` using `[show 2 * z + n - (i : ℕ) = (((M : ℤ) - (i : ℕ) : ℤ) : ℂ) from h, sub_self]`. Conclude with `hz (sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left two_ne_zero))`. Establish `hpunct : ∀ᶠ z in 𝓝[≠] s₀, (2 : ℂ) ^ K * (z - s₀) ^ K * G z = (z - s₀) ^ (a + S.card) * (Wi z * (∏ v ∈ S, dslope (Wv v) s₀ z) * ∏ i : Fin n, H i (2 * z + n - (i : ℕ)))` using `by filter_upwards [Filter.eventually_all.2 fun i => (htend i).eventually (hHe i)] with z hz`. Establish `hH : ∏ i : Fin n, H i (2 * z + n - (i : ℕ)) = (2 * (z - s₀)) ^ K * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ))`.

Rewrite using `[Finset.prod_congr rfl fun i _ => hz i, Finset.prod_mul_distrib, hK, ← Finset.prod_pow_eq_pow_sum]`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun i _ => by rw [haff]`. Establish `hW : ∏ v ∈ S, Wv v z = (z - s₀) ^ S.card * ∏ v ∈ S, dslope (Wv v) s₀ z`. Rewrite using `[← Finset.prod_const, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `sub_smul_dslope (Wv v) s₀ z` as an intermediate fact. Rewrite `this` using `[hWv0' v, sub_zero, smul_eq_mul]`. Conclude with `this.symm`. Use `show (2 : ℂ) ^ K * (z - s₀) ^ K * (((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))) = _`.

Rewrite using `[hH, hW, mul_pow]`. Use `clear * -`. Use `clear_value a K s₀`. Expand and normalize the polynomial expressions, which then agree. Establish `hHol` using `analyticAt_update_zero (c := (2 : ℂ) ^ K) (pow_ne_zero _ two_ne_zero) hKN hA hpunct`.

Establish `hGm : ∀ x : ℂ, MeromorphicAt G x` using `fun x => ((((by fun_prop : AnalyticAt ℂ (fun z : ℂ => (z - s₀) ^ a) x)).meromorphicAt.mul (hWi.analyticAt x).meromorphicAt).mul ((MeromorphicAt.fun_prod fun v _ => ((hWv v).analyticAt x).meromorphicAt).mul (MeromorphicAt.fun_prod fun i _ => (hZm i (2 * x + n - (i : ℕ)) trivial).c …`. Use `⟨fun z => if z = s₀ then 0 else G z, ⟨Set.univ, Set.mem_univ _, isRightDomain_univ, fun x _ => ?_, σ₀, fun z hz => ?_⟩, hHol, by simp⟩` and prove the remaining obligations. Use `(hGm x).congr ?_` and prove the remaining obligations. Distinguish the cases in `hx : x = s₀`. Substitute `hx filter_upwards [self_mem_nhdsWithin] with z hz` using the available equality.

Conclude with `(if_neg hz).symm`. Use `filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hx)] with z hz`. Conclude with `(if_neg hz).symm`. Use `show (if z = s₀ then 0 else G z) = _`. Rewrite using `[if_neg (hne z hz)]`.

Conclude with `hright z hz`.
-/
theorem whitGenLowOf : WhitGenLowOf := by
  intro hLoc hUnr hReal hFac hLOrd F E _ _ _ _ _ σ M n d J T bs ψ ι _ θ l ε fr g P lam L₁ L₂ Φ Φf Φv μ ν hD hok _ hvac ht
    μH 𝓕 _ _
  rw [zero_mul]
  obtain ⟨hlt, -⟩ := hok
  obtain ⟨hP, e, rfl⟩ := hvac trivial
  have hP' : P = fun _ => 1 := funext hP
  subst hP'
  obtain ⟨t, ht⟩ := ht
  have hT := hD.hT

  obtain ⟨⟨μi, hμi⟩, ⟨νi, hνi⟩⟩ := GlobalTheory.CompanionTheory.SelfDualInf.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr
  choose μv hμv using fun v => (GlobalTheory.CompanionTheory.SdFin.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr v).1
  choose νv hνv using fun v => (GlobalTheory.CompanionTheory.SdFin.exists_sdW_sdHerm F E σ hD.cm M J hD.herm n ψ hD.chr v).2

  obtain ⟨Wi, hWi, ti, hti⟩ := hReal F E σ hD.cm M J hD.herm n hlt ψ hD.chr ι θ l hD.places e fr hD.frames g μi νi
    hμi hνi (hermOf (Ainf F) σ T hT) (W.hermOf_unit σ T hT hD.det _)

  have hL := fun v => hLoc F E σ hD.cm M J hD.herm n ψ hD.chr v (μv v) (νv v) (lam v) (L₁ v) (L₂ v) (hμv v)
    (hνv v) (hD.haar v) (hD.co v).1 (hD.co v).2 (Φv v) (hD.pure.1 v) 0 (densZero σ J hlt v (μv v) (νv v) (Φv v))
    (hermOf (Fv F v) σ T hT) (W.hermOf_unit σ T hT hD.det _)
  choose Wv hWv hWv0 tv htv using hL

  obtain ⟨tu, hU⟩ := hUnr F E σ hD.cm M J hD.herm n T hT hD.det d bs ψ hD.chr
  have hev := (hU.and hD.std).and hD.pure.2.1
  obtain ⟨S, hSout⟩ := W.exists_finset_of_cofinite hev
  have hPv : ∀ v, v ∉ S → ∀ z : ℂ, tu < z.re →
      Integrable (whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z) (νv v) ∧
      ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v) =
        ∏ i : Fin n, (1 - eSp E v ^ (M + (i : ℕ)) * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(2 * z + n - (i : ℕ)))) := by
    intro v hv z hz
    obtain ⟨⟨hu, hs1, hs2⟩, hpv⟩ := hSout v hv
    have hL12 : L₂ v = L₁ v := SetLike.coe_injective (hs2.trans hs1.symm)
    rw [hL12, hpv]
    exact hu (μv v) (νv v) (lam v) (L₁ v) (hμv v) (hνv v) (hD.haar v) hs1 z hz

  choose Z hZm hZp H hHa hHe using fun i : Fin n => hLOrd F E σ hD.cm S ((M : ℤ) - (i : ℕ))
  set s₀ : ℂ := ((M : ℂ) - n) / 2 with hs₀
  set a : ℕ := Module.finrank ℚ F * (n - M) with ha
  have hWv0' : ∀ v, Wv v s₀ = 0 := fun v => hWv0 v
  let G : ℂ → ℂ := fun z => ((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))

  set σ₀ : ℝ := |t| + |ti| + |tu| + ∑ v ∈ S, |tv v| + |s₀.re| + 1 with hσ₀
  have hne : ∀ z : ℂ, σ₀ < z.re → z ≠ s₀ := fun z hz h => by
    rw [h] at hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    linarith [le_abs_self s₀.re, abs_nonneg t, abs_nonneg ti, abs_nonneg tu]
  have hright : ∀ z : ℂ, σ₀ < z.re →
      G z = ∫ b, whI (AF F) σ J ψ μ Φ (nuA θ g lam L₁ L₂) (T.map (inclR (AF F))) z b ∂ν := by
    intro z hz
    have hsum : 0 ≤ ∑ v ∈ S, |tv v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    have hs0a := abs_nonneg s₀.re
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
    have hF := hFac F E σ M n d J T bs ψ ι θ l (fun i _ => e i) fr g (fun _ => 1) lam L₁ L₂ Φ Φf Φv μ ν hD μi νi μv νv
      hμi hνi hμv hνv z (ht z zt) (hti z zti).1 hint
    have hcompl : HasProd (fun v : {v // v ∉ S} => ∫ b, whI (Fv F v.1) σ J (psiV F ψ v.1) (μv v.1) (Φv v.1)
        (nu2 (lam v.1) (L₁ v.1) (L₂ v.1)) (T.map (inclR (Fv F v.1))) z b ∂(νv v.1))
        (∏ i : Fin n, Z i (2 * z + n - (i : ℕ))) := by
      have hp := hasProd_prod (s := (Finset.univ : Finset (Fin n))) fun i _ =>
        hZp i (2 * z + n - (i : ℕ)) (by
          have hi : ((i : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast i.2
          simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re,
            Complex.re_ofNat, Complex.im_ofNat]
          linarith)
      convert hp using 1
      funext v
      rw [(hPv v.1 v.2 z ztu).2]
      exact Finset.prod_congr rfl fun i _ => by rw [eSp_pow]
    have hp := hasProd_split' (fun v => ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
        (T.map (inclR (Fv F v))) z b ∂(νv v)) S _ hcompl
    have hlim : Tendsto (fun s : Finset (HeightOneSpectrum (𝓞 F)) => ∏ v ∈ s, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v)
        (Φv v) (nu2 (lam v) (L₁ v) (L₂ v)) (T.map (inclR (Fv F v))) z b ∂(νv v)) atTop
        (nhds ((∏ v ∈ S, ∫ b, whI (Fv F v) σ J (psiV F ψ v) (μv v) (Φv v) (nu2 (lam v) (L₁ v) (L₂ v))
          (T.map (inclR (Fv F v))) z b ∂(νv v)) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))) := hp
    have hIi : ∫ b, whI (Ainf F) σ J (psiInf F ψ) μi (phiInf θ l fr g fun _ => 1) (nuInf θ g) (T.map (inclR (Ainf F)))
        z b ∂νi = (z - s₀) ^ a * Wi z := (hti z zti).2.symm
    rw [hIi] at hF
    have hu := tendsto_nhds_unique hF (hlim.const_mul ((z - s₀) ^ a * Wi z))
    show ((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ))) = _
    rw [Finset.prod_congr rfl fun v hv => (htv v z (ztv v hv)).2]
    exact hu.symm

  have hd1 : 1 ≤ Module.finrank ℚ F := Module.finrank_pos
  have hcount := count S.card (Module.finrank ℚ F) M n hd1 hlt
  set K : ℕ := ∑ i : Fin n, (if 1 ≤ (M : ℤ) - ((i : ℕ) : ℤ) then 0 else
    if (M : ℤ) - ((i : ℕ) : ℤ) = 0 then S.card + Module.finrank ℚ F - 1 else Module.finrank ℚ F) with hK
  have hKN : K < a + S.card := by omega
  have hdsl : ∀ v, AnalyticAt ℂ (dslope (Wv v) s₀) s₀ := fun v =>
    (differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 (hWv v).differentiableOn)).analyticAt s₀
  have haff : ∀ i : Fin n, ∀ z : ℂ, 2 * z + n - (i : ℕ) - (((M : ℤ) - (i : ℕ) : ℤ) : ℂ) = 2 * (z - s₀) := fun i z => by
    rw [hs₀]; push_cast; ring
  have hHan : ∀ i : Fin n, AnalyticAt ℂ (fun z => H i (2 * z + n - (i : ℕ))) s₀ := fun i =>
    AnalyticAt.comp_of_eq (g := H i) (f := fun z : ℂ => 2 * z + n - (i : ℕ)) (hHa i) (by fun_prop) (by
      have := haff i s₀
      rw [sub_self, mul_zero, sub_eq_zero] at this
      exact this)
  have hA : AnalyticAt ℂ (fun z => Wi z * (∏ v ∈ S, dslope (Wv v) s₀ z) * ∏ i : Fin n, H i (2 * z + n - (i : ℕ))) s₀ :=
    ((hWi.analyticAt s₀).mul (Finset.analyticAt_fun_prod _ fun v _ => hdsl v)).mul
      (Finset.analyticAt_fun_prod _ fun i _ => hHan i)
  have htend : ∀ i : Fin n, Tendsto (fun z : ℂ => 2 * z + n - (i : ℕ)) (𝓝[≠] s₀) (𝓝[≠] (((M : ℤ) - (i : ℕ) : ℤ) : ℂ)) :=
    fun i => by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hc : Continuous (fun z : ℂ => 2 * z + n - (i : ℕ)) := by fun_prop
        have := haff i s₀
        rw [sub_self, mul_zero, sub_eq_zero] at this
        rw [← this]
        exact (hc.tendsto s₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        intro h
        have := haff i z
        rw [show 2 * z + n - (i : ℕ) = (((M : ℤ) - (i : ℕ) : ℤ) : ℂ) from h, sub_self] at this
        exact hz (sub_eq_zero.1 ((mul_eq_zero.1 this.symm).resolve_left two_ne_zero))
  have hpunct : ∀ᶠ z in 𝓝[≠] s₀, (2 : ℂ) ^ K * (z - s₀) ^ K * G z = (z - s₀) ^ (a + S.card) *
      (Wi z * (∏ v ∈ S, dslope (Wv v) s₀ z) * ∏ i : Fin n, H i (2 * z + n - (i : ℕ))) := by
    filter_upwards [Filter.eventually_all.2 fun i => (htend i).eventually (hHe i)] with z hz
    have hH : ∏ i : Fin n, H i (2 * z + n - (i : ℕ)) = (2 * (z - s₀)) ^ K * ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)) := by
      rw [Finset.prod_congr rfl fun i _ => hz i, Finset.prod_mul_distrib, hK, ← Finset.prod_pow_eq_pow_sum]
      congr 1
      exact Finset.prod_congr rfl fun i _ => by rw [haff]
    have hW : ∏ v ∈ S, Wv v z = (z - s₀) ^ S.card * ∏ v ∈ S, dslope (Wv v) s₀ z := by
      rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      have := sub_smul_dslope (Wv v) s₀ z
      rw [hWv0' v, sub_zero, smul_eq_mul] at this
      exact this.symm
    show (2 : ℂ) ^ K * (z - s₀) ^ K * (((z - s₀) ^ a * Wi z) * ((∏ v ∈ S, Wv v z) *
      ∏ i : Fin n, Z i (2 * z + n - (i : ℕ)))) = _
    rw [hH, hW, mul_pow]
    clear * -
    clear_value a K s₀
    ring
  have hHol := analyticAt_update_zero (c := (2 : ℂ) ^ K) (pow_ne_zero _ two_ne_zero) hKN hA hpunct

  have hGm : ∀ x : ℂ, MeromorphicAt G x := fun x =>
    ((((by fun_prop : AnalyticAt ℂ (fun z : ℂ => (z - s₀) ^ a) x)).meromorphicAt.mul
      (hWi.analyticAt x).meromorphicAt).mul
      ((MeromorphicAt.fun_prod fun v _ => ((hWv v).analyticAt x).meromorphicAt).mul
        (MeromorphicAt.fun_prod fun i _ =>
          (hZm i (2 * x + n - (i : ℕ)) trivial).comp_analyticAt (g := fun z : ℂ => 2 * z + n - (i : ℕ)) (by fun_prop))))
  refine ⟨fun z => if z = s₀ then 0 else G z, ⟨Set.univ, Set.mem_univ _, isRightDomain_univ, fun x _ => ?_,
    σ₀, fun z hz => ?_⟩, hHol, by simp⟩
  · refine (hGm x).congr ?_
    by_cases hx : x = s₀
    · subst hx
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (if_neg hz).symm
    · filter_upwards [nhdsWithin_le_nhds (eventually_ne_nhds hx)] with z hz
      exact (if_neg hz).symm
  · show (if z = s₀ then 0 else G z) = _
    rw [if_neg (hne z hz)]
    exact hright z hz

end PositivityTheory.SiegelWeilFormula.Gen.WL

/- English proof (translation)
The claim follows from `PositivityTheory.SiegelWeilFormula.Gen.WL.whitGenLowOf`.
-/
theorem PositivityTheory.SiegelWeilFormula.Gen.whitGenLowOf : PositivityTheory.SiegelWeilFormula.Gen.WhitGenLowOf := PositivityTheory.SiegelWeilFormula.Gen.WL.whitGenLowOf

end
