import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleIsotropicTowerStepTen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneComplementDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermLinearContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarFundamentalDomainOneAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSingleSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramSkewStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.ThK.SquareIntegrability

noncomputable section

namespace GlobalTheory.ThK.DescStepCusp

/- English proof (translation)
Introduce `h0` and use `h.2 (by have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl rw [Matrix.det_smul, e, h0, map_zero, mul_zero])`.
-/
theorem det_ne_zero_of_herm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {c : E} (h : IsHermND σ (c • J.map σ)) : J.det ≠ 0 := fun h0 => h.2 (by
  have e : (J.map σ).det = (σ : E →+* E) J.det := by rw [RingHom.map_det]; rfl
  rw [Matrix.det_smul, e, h0, map_zero, mul_zero])

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨GlobalTheory.StdPar.isAutOn_const σ J X Y S K 0, fun S' _ => GlobalTheory.StdPar.isConstAlong_const σ J X S' 0⟩, 0, h, fun ψ _ μ 𝓕 _ _ g g' => ⟨?_, ?_, ?_⟩⟩ <;> simp`.
-/
theorem cuspComp_of_const_zero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {S : Finset (Fin r)}
    {K : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : GlobalTheory.StdPar.IsConstAlong σ J X S φ 0) :
    GlobalTheory.StdPar.IsCuspComp σ J X Y S K φ 0 := by
  refine ⟨⟨GlobalTheory.StdPar.isAutOn_const σ J X Y S K 0, fun S' _ => GlobalTheory.StdPar.isConstAlong_const σ J X S' 0⟩, 0, h,
    fun ψ _ μ 𝓕 _ _ g g' => ⟨?_, ?_, ?_⟩⟩ <;> simp

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram χa χb za zb Kh S hβ hS hV`. Introduce `f hf c₀ hc₀ hND₁`. Establish `hσ : ∀ x, σ (σ x) = x` using `GlobalTheory.SiegelSet.sigma_sigma hcm`. Break down `Nat.eq_zero_or_pos n₁ with h0 | hpos` into its components or cases. Introduce `φ' _ K _ r Xf Yf hWF S' hS'`.

It suffices to derive a contradiction. Apply `hS'` to reduce the goal to its premises. Introduce `k _`. Substitute `h0` using the available equality. Use `congrFun (congrFun hWF.xy k) k` as an intermediate fact.

Simplify using `[Matrix.mul_apply] at this`. Establish `hND : IsHermND σ (c₀ • W.J.map σ)` using `GlobalTheory.PlaneHermTransfer.isHermND_of_plane F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hpos c₀ hc₀ hND₁`. Establish `hdet₁ : W₁.J.det ≠ 0` using `det_ne_zero_of_herm hND₁`. Establish `hdet : W.J.det ≠ 0` using `det_ne_zero_of_herm hND`. Take `⟨M, hMc, hML, hMr⟩` from `GlobalTheory.LeviPlaneSection.leviSection W W₁ H hσ hsk hn hxx hyy hxy horth hgram hdet₁`.

Establish `hcc` using `GlobalTheory.UnipCocptForm.cocompact_unip_form W W₁ H hcm hsk hn hxx hyy hxy horth hgram hdet hdet₁`. Establish `hdom` using `GlobalTheory.ThK.UnipDomPlaneAlg.exists_haar_fundamentalDomain_one_alg F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hdet hdet₁`. Establish `hreg` using `GlobalTheory.ThK.DescB.Nondeg.alphaSpan_reg H χa χb za zb Kh S hcc hdom M hMc hML hMr hS hβ`. Introduce `φ' hφ' K hK r Xf Yf hWF S' hS'`. Establish `eφ : φ' = fun x => f ((toGAd hσ W₁.J hc₀).symm x)` using `funext fun x => hφ' _ x rfl`.

Substitute `eφ` using the available equality. Use `clear hφ'`. Establish `lin` using `GlobalTheory.CuspCompZeroLin.isCuspComp_sub_zero F E σ hcm n₁ _ hND₁ r Xf Yf hWF K S'`. Establish `tr : ∀ g : UA σ W₁.J → ℂ, Continuous g → (∀ γ ∈ ratU σ W₁.J, ∀ x, g (γ * x) = g x) → Continuous (fun x => g ((toGAd hσ W₁.J hc₀).symm x)) ∧ ∀ γ ∈ GlobalTheory.AdelicU.ratPts σ (c₀ • W₁.J.map σ), ∀ x, g ((toGAd hσ W₁.J hc₀).symm (γ * x)) = g ((toGAd hσ W₁.J hc₀).symm x)`. Introduce `g hgc hgi`.

Use `⟨hgc.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W₁.J hc₀).2, fun γ hγ x => ?_⟩` and prove the remaining obligations. Establish `hγ' : (toGAd hσ W₁.J hc₀).symm γ ∈ ratU σ W₁.J`. Rewrite using `[← GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ W₁.J hc₀, MulEquiv.apply_symm_apply]`. Conclude with `hγ`. Rewrite using `[map_mul]`.

Conclude with `hgi _ hγ' _`. It suffices to establish `key : GlobalTheory.StdPar.IsCuspComp σ (c₀ • W₁.J.map σ) Xf Yf S' K (fun x => f ((toGAd hσ W₁.J hc₀).symm x)) 0 from key`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f₀, hf₀, fa, fb, hs, h, -, -, hx'⟩` from `hx`.

Establish `hfb` using `hβ f₀ hf₀ fa fb hs`. Substitute `hfb` using the available equality. Establish `hct : IsCT H f₀ fa` using `by simpa using hs.1`. Take `⟨hfc, hfi⟩` from `hS f₀ hf₀`. Establish `ex : x = fun h₁ => fa (M h₁ * h)` using `funext fun h₁ => hx' h₁ (M h₁) (hML h₁)`.

Substitute `ex` using the available equality. Conclude with `GlobalTheory.T.hyperbolic_plane_orthogonal_gram_skew hKP F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hdom χa za f₀ fa hfc hfi hct hs.2.1 M hMc hML hMr h c₀ hc₀ hND₁ hND (hV f₀ hf₀ c₀ hc₀ hND) _ (fun g g' e => by`. Establish `e' : (toGAd hσ W₁.J hc₀).symm g' = g` using `Subtype.ext e.symm`. Simplify using `only [e']) K hK r Xf Yf hWF S' hS'`. Consider the case `zero`.

Establish `e : (fun x => (0 : UA σ W₁.J → ℂ) ((toGAd hσ W₁.J hc₀).symm x)) = fun _ => 0` using `rfl`. Rewrite using `[e]`. Conclude with `cuspComp_of_const_zero (GlobalTheory.StdPar.isConstAlong_const σ (c₀ • W₁.J.map σ) Xf S' 0)`. Consider the case `add x y hxm hym hx hy`. Take `⟨cx, ix⟩` from `tr x (hreg x hxm).1 (hreg x hxm).2`.

Take `⟨cy, iy⟩` from `tr y (hreg y hym).1 (hreg y hym).2`. Use `lin _ _ (-1) cx cy (fun γ hγ g => by simpa using ix γ hγ g) (fun γ hγ g => by simpa using iy γ hγ g) hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.

Consider the case `smul z x hxm hx`. Take `⟨cx, ix⟩` from `tr x (hreg x hxm).1 (hreg x hxm).2`. Establish `h0` using `cuspComp_of_const_zero (φ := fun _ => (0 : ℂ)) (Y := Yf) (K := K) (GlobalTheory.StdPar.isConstAlong_const σ (c₀ • W₁.J.map σ) Xf S' 0)`. Use `lin (fun _ => 0) _ (-z) continuous_const cx (fun _ _ _ => rfl) (fun γ hγ g => by simpa using ix γ hγ g) h0 hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules.
-/
theorem cuspComp_alphaSpan_eq_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (χa χb : Chr F E) (za zb : ℝ) (Kh : Set (UA σ W.J)) (S : Submodule ℂ (UA σ W.J → ℂ)),
      BetaZero W₁ H χa χb za zb S → (∀ f ∈ S, Continuous f ∧ ∀ γ ∈ ratU σ W.J, ∀ x, f (γ * x) = f x) →
      (∀ f ∈ S, ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • W.J.map σ) → ∀ φ' : GAd σ (c₀ • W.J.map σ) → ℂ,
        (∀ (g : UA σ W.J) (g' : GAd σ (c₀ • W.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W.J.map σ) Xf Yf S' K φ' 0) →
      ∀ f ∈ alphaSpan W₁ H χa χb za zb Kh S, ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • W₁.J.map σ) →
        ∀ φ' : GAd σ (c₀ • W₁.J.map σ) → ℂ, (∀ (g : UA σ W₁.J) (g' : GAd σ (c₀ • W₁.J.map σ)), g.1 = g'.1 → φ' g' = f g) →
        ∀ K : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K →
        ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
          ∀ S' : Finset (Fin r), ¬ (∀ k ∈ S', ∀ l ≤ k, l ∈ S') → GlobalTheory.StdPar.IsCuspComp σ (c₀ • W₁.J.map σ) Xf Yf S' K φ' 0 := by
  intro hKP F E _ _ _ _ _ σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram χa χb za zb Kh S hβ hS hV
  intro f hf c₀ hc₀ hND₁
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  rcases Nat.eq_zero_or_pos n₁ with h0 | hpos
  · intro φ' _ K _ r Xf Yf hWF S' hS'
    exfalso
    apply hS'
    intro k _
    subst h0
    have := congrFun (congrFun hWF.xy k) k
    simp [Matrix.mul_apply] at this
  have hND : IsHermND σ (c₀ • W.J.map σ) := GlobalTheory.PlaneHermTransfer.isHermND_of_plane F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hpos c₀ hc₀ hND₁
  have hdet₁ : W₁.J.det ≠ 0 := det_ne_zero_of_herm hND₁
  have hdet : W.J.det ≠ 0 := det_ne_zero_of_herm hND
  obtain ⟨M, hMc, hML, hMr⟩ := GlobalTheory.LeviPlaneSection.leviSection W W₁ H hσ hsk hn hxx hyy hxy horth hgram hdet₁
  have hcc := GlobalTheory.UnipCocptForm.cocompact_unip_form W W₁ H hcm hsk hn hxx hyy hxy horth hgram hdet hdet₁
  have hdom := GlobalTheory.ThK.UnipDomPlaneAlg.exists_haar_fundamentalDomain_one_alg F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hdet hdet₁
  have hreg := GlobalTheory.ThK.DescB.Nondeg.alphaSpan_reg H χa χb za zb Kh S hcc hdom M hMc hML hMr hS hβ
  intro φ' hφ' K hK r Xf Yf hWF S' hS'
  have eφ : φ' = fun x => f ((toGAd hσ W₁.J hc₀).symm x) := funext fun x => hφ' _ x rfl
  subst eφ
  clear hφ'
  have lin := GlobalTheory.CuspCompZeroLin.isCuspComp_sub_zero F E σ hcm n₁ _ hND₁ r Xf Yf hWF K S'
  have tr : ∀ g : UA σ W₁.J → ℂ, Continuous g → (∀ γ ∈ ratU σ W₁.J, ∀ x, g (γ * x) = g x) →
      Continuous (fun x => g ((toGAd hσ W₁.J hc₀).symm x)) ∧
      ∀ γ ∈ GlobalTheory.AdelicU.ratPts σ (c₀ • W₁.J.map σ), ∀ x,
        g ((toGAd hσ W₁.J hc₀).symm (γ * x)) = g ((toGAd hσ W₁.J hc₀).symm x) := by
    intro g hgc hgi
    refine ⟨hgc.comp (GlobalTheory.ThK.GLTwo.continuous_toGAd hσ W₁.J hc₀).2, fun γ hγ x => ?_⟩
    have hγ' : (toGAd hσ W₁.J hc₀).symm γ ∈ ratU σ W₁.J := by
      rw [← GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ W₁.J hc₀, MulEquiv.apply_symm_apply]; exact hγ
    rw [map_mul]
    exact hgi _ hγ' _
  suffices key : GlobalTheory.StdPar.IsCuspComp σ (c₀ • W₁.J.map σ) Xf Yf S' K (fun x => f ((toGAd hσ W₁.J hc₀).symm x)) 0 from key
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₀, hf₀, fa, fb, hs, h, -, -, hx'⟩ := hx
    have hfb := hβ f₀ hf₀ fa fb hs
    subst hfb
    have hct : IsCT H f₀ fa := by simpa using hs.1
    obtain ⟨hfc, hfi⟩ := hS f₀ hf₀
    have ex : x = fun h₁ => fa (M h₁ * h) := funext fun h₁ => hx' h₁ (M h₁) (hML h₁)
    subst ex
    exact GlobalTheory.T.hyperbolic_plane_orthogonal_gram_skew hKP F E σ hcm n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram hdom χa za f₀ fa hfc hfi hct hs.2.1 M hMc hML hMr h
      c₀ hc₀ hND₁ hND (hV f₀ hf₀ c₀ hc₀ hND) _
      (fun g g' e => by
        have e' : (toGAd hσ W₁.J hc₀).symm g' = g := Subtype.ext e.symm
        simp only [e']) K hK r Xf Yf hWF S' hS'
  | zero =>
    have e : (fun x => (0 : UA σ W₁.J → ℂ) ((toGAd hσ W₁.J hc₀).symm x)) = fun _ => 0 := rfl
    rw [e]
    exact cuspComp_of_const_zero (GlobalTheory.StdPar.isConstAlong_const σ (c₀ • W₁.J.map σ) Xf S' 0)
  | add x y hxm hym hx hy =>
    obtain ⟨cx, ix⟩ := tr x (hreg x hxm).1 (hreg x hxm).2
    obtain ⟨cy, iy⟩ := tr y (hreg y hym).1 (hreg y hym).2
    have := lin _ _ (-1) cx cy (fun γ hγ g => by simpa using ix γ hγ g) (fun γ hγ g => by simpa using iy γ hγ g) hx hy
    convert this using 1
    funext g; simp
  | smul z x hxm hx =>
    obtain ⟨cx, ix⟩ := tr x (hreg x hxm).1 (hreg x hxm).2
    have h0 := cuspComp_of_const_zero (φ := fun _ => (0 : ℂ)) (Y := Yf) (K := K)
      (GlobalTheory.StdPar.isConstAlong_const σ (c₀ • W₁.J.map σ) Xf S' 0)
    have := lin (fun _ => 0) _ (-z) continuous_const cx (fun _ _ _ => rfl) (fun γ hγ g => by simpa using ix γ hγ g) h0 hx
    convert this using 1
    funext g; simp

end GlobalTheory.ThK.DescStepCusp

end
