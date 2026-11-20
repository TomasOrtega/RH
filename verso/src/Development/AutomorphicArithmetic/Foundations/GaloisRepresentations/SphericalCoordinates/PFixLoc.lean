import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.HeckeFixedPointCMCycleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Unfold `kap`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem kap_inv {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (v : InfinitePlace G.F)
    (t₀ : D.F →+* ℂ) (z : ℂ) : kap L v t₀ z⁻¹ = (kap L v t₀ z)⁻¹ := by
  unfold kap
  split_ifs <;> simp

/- English proof (translation)
Introduce `hSheet hFixGa hFixEq hOneAt hPow hCsp hAd hEig hLoc hRegSep hInvMin hMinB hChart hPt`. Introduce `p _ D G L ha hm v hv t₀ ht gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig hsm hreg U B PD RD i P j a hper hco y hsees k α hα h₁ h₂`. Establish `hFM : FullMark N' (U.Di i) (U.t i)`. Take `⟨⟨f, ν, hft, -, hn⟩, -⟩` from `U.mem i`. Introduce `x`.

Take `⟨a', e', hx⟩` from `(hn N' (by have := hlev.2.2.1; omega) hlev.2.2.2.1).2.2.2.1 x`. Conclude with `⟨a', e', by rw [hft]; exact hx⟩`. Take `⟨S, hSu, hSex⟩` from `hSheet D.O D.inv D.g ρ D.La (gfamD X' hX' hL') N' (D.Cls N') U i hlev.2.2.1 hFM`. Establish `hUA` using `U.unif i P hper`. Take `⟨ga, H, hga, hfix, hHQ⟩` from `hFixGa p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P) hUA y hsees`.

Take `⟨Hm, hHm1, hHm2, hHm3⟩` from `hper.2.2.2.2`. Establish `hHerm : IsHermOf (U.Di i) P Hm` using `⟨hHm1, hHm2, hHm3⟩`. Take `⟨co, hcoC⟩` from `hCsp D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm`. Take `⟨hHdet, hHcomm, hHCsp⟩` from `hAd D.O D.inv D.g ρ (U.Di i) P Hm hper hHerm ga H hfix`. Set `φ : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin D.g) (Fin D.g) ℂ` to `(LinearMap.mulRight ℂ (H.map star)⁻¹ ∘ₗ LinearMap.mulLeft ℂ H) ∘ₗ co`.

Establish `hφ : ∀ b, φ b ∈ LinearMap.range co`. Introduce `b`. Rewrite using `[hcoC.2]`. Conclude with `hHCsp _ (by rw [← hcoC.2]; exact LinearMap.mem_range_self co b)`. Set `eco` to `LinearEquiv.ofInjective co hcoC.1`.

Set `T : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Fin (D.n - 1) → ℂ` to `eco.symm.toLinearMap ∘ₗ φ.codRestrict (LinearMap.range co) hφ`. Establish `hT : ∀ b, co (T b) = H * co b * (H.map star)⁻¹`. Introduce `b`. Establish `h2` using `congrArg Subtype.val (eco.apply_symm_apply ⟨φ b, hφ b⟩)`. Simplify `h2` using `[T, φ, eco, LinearEquiv.ofInjective_apply]`.

Take `⟨Q, hQper, hQP, hQrel⟩` from `hco.2.2.2`. Establish `hfixL` using `hsees.1`. Use `set lam := RootSumWeights.eigL G v B.β y a.2.1 with hlam`. Establish `hlamspec : (LKCx.toV G v B.β y).val *ᵥ a.2.1 = lam • a.2.1`. Rewrite using `[hlam]`.

Simplify using `only [RootSumWeights.eigL, dif_pos hfixL]`. Conclude with `hfixL.choose_spec`. Establish `hne : a.2.1 ≠ 0`. Introduce `h0`. Use `a.2.2` as an intermediate fact.

Rewrite `this` using `[h0]`. Simplify using `at this`. Establish `hinvmul : (LKCx.toV G v B.β y⁻¹).val * (LKCx.toV G v B.β y).val = 1`. Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`. Establish `hback : (LKCx.toV G v B.β y⁻¹).val *ᵥ (lam • a.2.1) = a.2.1`.

Rewrite using `[← hlamspec, Matrix.mulVec_mulVec, hinvmul, Matrix.one_mulVec]`. Establish `hlam0 : lam ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← hback, h0, zero_smul, Matrix.mulVec_zero]`.

Establish `hinvspec : (LKCx.toV G v B.β y⁻¹).val *ᵥ a.2.1 = lam⁻¹ • a.2.1`. Rewrite `hback` using `[Matrix.mulVec_smul]`. Rewrite using `[← hback, smul_smul, inv_mul_cancel₀ hlam0, one_smul]`. Conclude with `hback.symm ▸ rfl`. Establish `hmark` using `RD.mark y⁻¹ Q a.2 H lam⁻¹ hQper hQrel (fun w => hHQ w Q hQP hQper) hinvspec`.

Rewrite `hmark` using `[kap_inv]`. Establish `hcy : ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) = (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ)`. Simplify using `[Subgroup.coe_inv, Prod.fst_inv]`. Establish `hmin` using `hMinB p D G L B.β (U.Di i) j hco.1 ga ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) (fun u => hga u)`. Rewrite `hmin` using `[hcy]`.

Take `⟨hIv, hIdeg, hIsep⟩` from `hInvMin G.F G.C ((↑y : G.Cˣ × ℚˣ).1)`. Take `⟨hRdeg, hRsep⟩` from `hRegSep p D G L v hv B a y hsees.1 (hreg _ hsees.2.1)`. Establish `hdeg : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).natDegree = D.n`. Rewrite using `[Polynomial.natDegree_map, hIdeg, hRdeg, L.n_eq]`. Establish `hsep : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).Separable` using `(hIsep hRsep).map`.

Take `⟨-, hEall⟩` from `hEig D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm ga H hfix _ hmin hdeg hsep (D.n - 1) co hcoC T hT k α hα`. Take `⟨-, hdetT, hdetF, hform⟩` from `hEall _ hmark`. Establish `hact : ∀ P' : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P' → ∀ (b : D.O) (z : Fin D.g → ℂ), Over.Hom.left (S.ex P' (ρ b *ᵥ z)) = Over.Hom.left (S.ex P' z) ≫ Over.Hom.left (X'.univ.act.act b)`. Introduce `P' hP' b z`. Rewrite using `[hSex, hSex, (U.unif i P' hP').2.2.2.2.1 b z, Over.comp_left]`.

Both sides reduce to the same expression. Establish `hEq : ∀ P₁ P₂ : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P₁ → PELU.IsPeriod (U.Di i) ρ P₂ → (∀ u, P₂ (ga u) = P₁ u) → S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧ ∀ z : Fin D.g → ℂ, Over.Hom.left (S.ex P₁ z) ≫ c₂.tot = Over.Hom.left (S.ex P₂ z) ≫ c₁.tot`. Introduce `P₁ P₂ h1 h2 h12`. Take `⟨hq, hz⟩` from `hFixEq p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco y hsees ga hga P₁ P₂ (U.u i P₁) (U.u i P₂) (U.ex i P₁) (U.ex i P₂) (U.unif i P₁ h1) (U.unif i P₂ h2) h12`. Use `⟨by rw [hSu, hSu]; exact hq, fun z => by rw [hSex, hSex]; exact hz z⟩` and prove the remaining obligations.

Take `⟨hCorr, hInjP⟩` from `hPow p D G L gb N N' h X X' c₁ c₂ ρ (U.Di i) S hact ga hEq k α`. Take `⟨e₁, hUA1, he₁⟩` from `hOneAt p D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hfine B PD (U.Di i) (U.t i) (U.mem i) j a.1 hco.1 hco.2.1 hco.2.2.1 P (U.u i P) (U.ex i P) hUA`. Establish `hker : ∀ z z' : Fin D.g → ℂ, Over.Hom.left (S.ex P z) ≫ c₁.tot = Over.Hom.left (S.ex P z') ≫ c₁.tot → z - z' ∈ P.range`. Introduce `z z' hzz`. Rewrite `hzz` using `[hSex, hSex]`.

Establish `hee : e₁ z = e₁ z'` using `Over.OverMorphism.ext (by rw [he₁ z, he₁ z']; exact hzz)`. Establish `hsplit : e₁ z = e₁ z' * e₁ (z - z')` using `by rw [← hUA1.2.2.1.1, add_sub_cancel]`. Rewrite `hsplit` using `[hee]`. Conclude with `(hUA1.2.2.2.1 (z - z')).1 (mul_eq_left.mp hsplit.symm)`. Establish `hinj` using `hInjP P hper hker`.

Establish `hrange : ∀ z : Fin k → Fin D.g → ℂ, (∀ s, z s ∈ P.range) → ∀ s, (fibMap H (diagAct (algebraMap (𝓞 D.F) D.O) ρ α)) z s ∈ P.range`. Introduce `z hz s`. Take `⟨x, hx⟩` from `AddMonoidHom.mem_range.mp (hz s)`. Use `AddMonoidHom.mem_range.mpr ⟨ga (algebraMap (𝓞 D.F) D.O (α s) • x), ?_⟩` and prove the remaining obligations. Rewrite using `[hfix.2, hper.1, hx]`.

Simplify using `[fibMap, diagAct, Matrix.toLin'_apply]`. Take `⟨Fx, hFx, hAt⟩` from `hLoc D.O D.inv D.g ρ (U.Di i) _ _ _ S (D.n - 1) hsm k _ (sZ X k) (c₁.pw k) (c₂.tw α) h₁ h₂ P Hm hper hHerm co hcoC ga H hfix T hT _ hCorr hrange hinj hdetT hdetF`. Establish `hpc0 : perC P 0 = P`. Use extensionality with `x s`. Simplify using `[perC, PeriodCoord.realMap]`.

Establish `hpc1 : perC P (H * 0 * (H.map star)⁻¹) = P` using `by rw [mul_zero, zero_mul, hpc0]`. Establish `hch` using `hChart _ _ _ ρ (U.Di i) _ _ _ S k _ (c₁.pw k) (c₂.tw α) P Hm hper hHerm ga H hfix _ hCorr 0 (by rw [hpc0]; exact hper) (by rw [hpc1]; exact hper) 0`. Rewrite `hch` using `[hpc0, hpc1, map_zero]`. Take `⟨hpt1, -, -, -, -⟩` from `hPt _ _ _ ρ (U.Di i) _ _ _ S k P hper`. Use `⟨Fx, fun x => by have hx := hFx x; rw [hSu] at hx; exact hx, ⟨⟨S.pt k P 0, ?_⟩, (hFx _).2 ⟨hpt1 0, hch.symm⟩⟩, fun At hTan => ⟨(hAt At hTan).1, fun t => ?_⟩⟩` and prove the remaining obligations.

Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X'.s) (hpt1 0)).trans (S.ov P hper))`. Conclude with `((hAt At hTan).2 t).trans ((hform t).trans (by unfold wtFix; rw [hIv]))`.
-/
theorem UpperTheory.Gal.W2.fixLoc_of :
    UpperTheory.Gal.W2.SheetOf → UpperTheory.Gal.W2.FixGa → UpperTheory.Gal.W2.FixEq → UpperTheory.Gal.W2.OneAt → UpperTheory.Gal.W2.PowCorr → UpperTheory.Gal.W2.CspDim → UpperTheory.Gal.W2.AdExists → UpperTheory.Gal.W2.EigTop → UpperTheory.Gal.W2.LocSum → UpperTheory.Gal.W2.RegSep → UpperTheory.Gal.W2.InvMin → UpperTheory.Gal.W2.MinBridge → UpperTheory.Gal.W2.CorrChart → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.FixLoc := by
  intro hSheet hFixGa hFixEq hOneAt hPow hCsp hAd hEig hLoc hRegSep hInvMin hMinB hChart hPt
  intro p _ D G L ha hm v hv t₀ ht gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine hsig hsm hreg U B PD RD i P j a hper hco y hsees k α hα h₁ h₂
  have hFM : FullMark N' (U.Di i) (U.t i) := by
    obtain ⟨⟨f, ν, hft, -, hn⟩, -⟩ := U.mem i
    intro x
    obtain ⟨a', e', hx⟩ := (hn N' (by have := hlev.2.2.1; omega) hlev.2.2.2.1).2.2.2.1 x
    exact ⟨a', e', by rw [hft]; exact hx⟩
  obtain ⟨S, hSu, hSex⟩ := hSheet D.O D.inv D.g ρ D.La (gfamD X' hX' hL') N' (D.Cls N') U i hlev.2.2.1 hFM
  have hUA := U.unif i P hper
  obtain ⟨ga, H, hga, hfix, hHQ⟩ := hFixGa p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco (U.u i P) (U.ex i P) hUA y hsees
  obtain ⟨Hm, hHm1, hHm2, hHm3⟩ := hper.2.2.2.2
  have hHerm : IsHermOf (U.Di i) P Hm := ⟨hHm1, hHm2, hHm3⟩
  obtain ⟨co, hcoC⟩ := hCsp D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm
  obtain ⟨hHdet, hHcomm, hHCsp⟩ := hAd D.O D.inv D.g ρ (U.Di i) P Hm hper hHerm ga H hfix
  let φ : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Matrix (Fin D.g) (Fin D.g) ℂ :=
    (LinearMap.mulRight ℂ (H.map star)⁻¹ ∘ₗ LinearMap.mulLeft ℂ H) ∘ₗ co
  have hφ : ∀ b, φ b ∈ LinearMap.range co := by
    intro b
    rw [hcoC.2]
    exact hHCsp _ (by rw [← hcoC.2]; exact LinearMap.mem_range_self co b)
  let eco := LinearEquiv.ofInjective co hcoC.1
  let T : (Fin (D.n - 1) → ℂ) →ₗ[ℂ] Fin (D.n - 1) → ℂ :=
    eco.symm.toLinearMap ∘ₗ φ.codRestrict (LinearMap.range co) hφ
  have hT : ∀ b, co (T b) = H * co b * (H.map star)⁻¹ := by
    intro b
    have h2 := congrArg Subtype.val (eco.apply_symm_apply ⟨φ b, hφ b⟩)
    simpa [T, φ, eco, LinearEquiv.ofInjective_apply] using h2
  obtain ⟨Q, hQper, hQP, hQrel⟩ := hco.2.2.2
  have hfixL := hsees.1
  set lam := RootSumWeights.eigL G v B.β y a.2.1 with hlam
  have hlamspec : (LKCx.toV G v B.β y).val *ᵥ a.2.1 = lam • a.2.1 := by
    rw [hlam]
    simp only [RootSumWeights.eigL, dif_pos hfixL]
    exact hfixL.choose_spec
  have hne : a.2.1 ≠ 0 := by
    intro h0
    have := a.2.2
    rw [h0] at this
    simp at this
  have hinvmul : (LKCx.toV G v B.β y⁻¹).val * (LKCx.toV G v B.β y).val = 1 := by
    rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hback : (LKCx.toV G v B.β y⁻¹).val *ᵥ (lam • a.2.1) = a.2.1 := by
    rw [← hlamspec, Matrix.mulVec_mulVec, hinvmul, Matrix.one_mulVec]
  have hlam0 : lam ≠ 0 := by
    intro h0
    apply hne
    rw [← hback, h0, zero_smul, Matrix.mulVec_zero]
  have hinvspec : (LKCx.toV G v B.β y⁻¹).val *ᵥ a.2.1 = lam⁻¹ • a.2.1 := by
    rw [Matrix.mulVec_smul] at hback
    rw [← hback, smul_smul, inv_mul_cancel₀ hlam0, one_smul]
    exact hback.symm ▸ rfl
  have hmark := RD.mark y⁻¹ Q a.2 H lam⁻¹ hQper hQrel (fun w => hHQ w Q hQP hQper) hinvspec
  rw [kap_inv] at hmark
  have hcy : ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) = (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) := by
    simp [Subgroup.coe_inv, Prod.fst_inv]
  have hmin := hMinB p D G L B.β (U.Di i) j hco.1 ga ((↑(y⁻¹) : G.Cˣ × ℚˣ).1 : G.C) (fun u => hga u)
  rw [hcy] at hmin
  obtain ⟨hIv, hIdeg, hIsep⟩ := hInvMin G.F G.C ((↑y : G.Cˣ × ℚˣ).1)
  obtain ⟨hRdeg, hRsep⟩ := hRegSep p D G L v hv B a y hsees.1 (hreg _ hsees.2.1)
  have hdeg : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).natDegree = D.n := by
    rw [Polynomial.natDegree_map, hIdeg, hRdeg, L.n_eq]
  have hsep : (Polynomial.map (↑L.e.symm : G.F →+* D.F) (minpoly G.F (((↑y : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ).val)).Separable :=
    (hIsep hRsep).map
  obtain ⟨-, hEall⟩ := hEig D.F D.O D.inv D.g ρ (algebraMap (𝓞 D.F) D.O) D.n t₀ (epsD D) hsig (U.Di i) P Hm hper hHerm ga H hfix _ hmin hdeg hsep (D.n - 1) co hcoC T hT k α hα
  obtain ⟨-, hdetT, hdetF, hform⟩ := hEall _ hmark
  have hact : ∀ P' : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P' → ∀ (b : D.O) (z : Fin D.g → ℂ),
      Over.Hom.left (S.ex P' (ρ b *ᵥ z)) = Over.Hom.left (S.ex P' z) ≫ Over.Hom.left (X'.univ.act.act b) := by
    intro P' hP' b z
    rw [hSex, hSex, (U.unif i P' hP').2.2.2.2.1 b z, Over.comp_left]
    rfl
  have hEq : ∀ P₁ P₂ : (U.Di i).La →+ Fin D.g → ℂ, PELU.IsPeriod (U.Di i) ρ P₁ → PELU.IsPeriod (U.Di i) ρ P₂ →
      (∀ u, P₂ (ga u) = P₁ u) →
        S.u P₁ ≫ c₂.q = S.u P₂ ≫ c₁.q ∧
          ∀ z : Fin D.g → ℂ, Over.Hom.left (S.ex P₁ z) ≫ c₂.tot = Over.Hom.left (S.ex P₂ z) ≫ c₁.tot := by
    intro P₁ P₂ h1 h2 h12
    obtain ⟨hq, hz⟩ := hFixEq p D G L gb N N' h hlev X X' c₁ c₂ hX hL hX' hL' ρ hfine v t₀ B PD RD (U.Di i) (U.t i) (U.mem i) P j a hco y hsees ga hga P₁ P₂ (U.u i P₁) (U.u i P₂) (U.ex i P₁) (U.ex i P₂) (U.unif i P₁ h1) (U.unif i P₂ h2) h12
    refine ⟨by rw [hSu, hSu]; exact hq, fun z => by rw [hSex, hSex]; exact hz z⟩
  obtain ⟨hCorr, hInjP⟩ := hPow p D G L gb N N' h X X' c₁ c₂ ρ (U.Di i) S hact ga hEq k α
  obtain ⟨e₁, hUA1, he₁⟩ := hOneAt p D G L gb N N' h hlev X X' c₁ hX hL hX' hL' ρ hfine B PD (U.Di i) (U.t i) (U.mem i) j a.1 hco.1 hco.2.1 hco.2.2.1 P (U.u i P) (U.ex i P) hUA
  have hker : ∀ z z' : Fin D.g → ℂ, Over.Hom.left (S.ex P z) ≫ c₁.tot = Over.Hom.left (S.ex P z') ≫ c₁.tot → z - z' ∈ P.range := by
    intro z z' hzz
    rw [hSex, hSex] at hzz
    have hee : e₁ z = e₁ z' := Over.OverMorphism.ext (by rw [he₁ z, he₁ z']; exact hzz)
    have hsplit : e₁ z = e₁ z' * e₁ (z - z') := by rw [← hUA1.2.2.1.1, add_sub_cancel]
    rw [hee] at hsplit
    exact (hUA1.2.2.2.1 (z - z')).1 (mul_eq_left.mp hsplit.symm)
  have hinj := hInjP P hper hker
  have hrange : ∀ z : Fin k → Fin D.g → ℂ, (∀ s, z s ∈ P.range) →
      ∀ s, (fibMap H (diagAct (algebraMap (𝓞 D.F) D.O) ρ α)) z s ∈ P.range := by
    intro z hz s
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (hz s)
    refine AddMonoidHom.mem_range.mpr ⟨ga (algebraMap (𝓞 D.F) D.O (α s) • x), ?_⟩
    rw [hfix.2, hper.1, hx]
    simp [fibMap, diagAct, Matrix.toLin'_apply]
  obtain ⟨Fx, hFx, hAt⟩ := hLoc D.O D.inv D.g ρ (U.Di i) _ _ _ S (D.n - 1) hsm k _ (sZ X k) (c₁.pw k) (c₂.tw α) h₁ h₂ P Hm hper hHerm co hcoC ga H hfix T hT _ hCorr hrange hinj hdetT hdetF
  have hpc0 : perC P 0 = P := by
    ext x s
    simp [perC, PeriodCoord.realMap]
  have hpc1 : perC P (H * 0 * (H.map star)⁻¹) = P := by rw [mul_zero, zero_mul, hpc0]
  have hch := hChart _ _ _ ρ (U.Di i) _ _ _ S k _ (c₁.pw k) (c₂.tw α) P Hm hper hHerm ga H hfix _ hCorr 0
    (by rw [hpc0]; exact hper) (by rw [hpc1]; exact hper) 0
  rw [hpc0, hpc1, map_zero] at hch
  obtain ⟨hpt1, -, -, -, -⟩ := hPt _ _ _ ρ (U.Di i) _ _ _ S k P hper
  refine ⟨Fx, fun x => by have hx := hFx x; rw [hSu] at hx; exact hx, ⟨⟨S.pt k P 0, ?_⟩, (hFx _).2 ⟨hpt1 0, hch.symm⟩⟩, fun At hTan => ⟨(hAt At hTan).1, fun t => ?_⟩⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X'.s) (hpt1 0)).trans (S.ov P hper))
  · exact ((hAt At hTan).2 t).trans ((hform t).trans (by unfold wtFix; rw [hIv]))
