import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqD
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeExpPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeRatio

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.TB

attribute [local instance] Over.cartesianMonoidalCategory

namespace GaugeR

def ExpPowSt : Prop :=
  ∀ (S σ : Type) [CommRing S] [Algebra ℚ S] (q : MvPowerSeries σ S), MvPowerSeries.constantCoeff q = 0 →
    ∀ k : ℕ, PowerSeries.subst q (PowerSeries.exp S) ^ k * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S) = 1

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'`. Establish `hL` using `Xo.univ.t.PP.isLB`. Use `choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (e m) (e' m) (he.gen m) (he'.gen m)`. Set `g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m` to `fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val`. Establish `hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B), gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m)` using `fun m B _ _ f => gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)`.

Establish `htr : ∀ m, jetTrunc (g (m + 1)) = g m`. Introduce `m`. Establish `h1` using `scaled_pull Xo.univ.t.PP.L _ _ (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))`. Establish `hU` using `corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)`. Establish `h2` using `congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU`.

Conclude with `(hpull (m + 1) _ jetTrunc).symm.trans h2`. Take `⟨r, hr⟩` from `exists_ps_of_compat g htr`. Establish `hrig : MvPowerSeries.constantCoeff r = 1`. Establish `h1` using `scaled_pull Xo.univ.t.PP.L _ _ (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)`. Establish `hU` using `corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig`.

Establish `h2` using `congrArg (fun v => gam S (Units.val v)) hU`. Simplify using `only [Units.val_one, map_one] at h2`. Rewrite using `[← jetAug_psJet 0 r, hr 0]`. Conclude with `(hpull 0 S jetAug).symm.trans h2`. Establish `hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw` using `Dw) c S (1 + a * H.bar a)) r = MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r * MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by`.

Introduce `a`. Take `⟨β, hβg, hβr, hβc⟩` from `he.coc a`. Take `⟨β', hβ'g, hβ'r, hβ'c⟩` from `he'.coc a`. Take `rfl` from `hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r`. Use `GermFun.psJet_inj fun m => ?_` and prove the remaining obligations.

Establish `s1` using `scaled_pull Xo.univ.t.PP.L _ _ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)`. Establish `sa` using `scaled_pull Xo.univ.t.PP.L _ _ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)`. Establish `sb` using `scaled_pull Xo.univ.t.PP.L _ _ (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)`. Establish `srhs` using `scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left)) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))`. Establish `hU` using `corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)`.

Establish `hv` using `congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv`. Rewrite `hv` using `[hpull, hpull, hpull]`. Establish `hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw` using `Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) = jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 * (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) := hv`. Rewrite using `[psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨q, hq0, hdeg, hpair, hexp⟩` from `ratio_exp hR c S r hrig hid`. Use `⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩` and prove the remaining obligations. Use `GermFun.psJet_inj fun m => ?_` and prove the remaining obligations. Take `⟨F₁, τ₁, hP₁, hC₁, hV₁⟩` from `hf m`.

Take `⟨F₂, τ₂, hP₂, hC₂, hV₂⟩` from `hf' m`. Establish `hF` using `GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂`. Substitute `hF` using the available equality. Establish `sg` using `scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k`. Establish `sτ` using `corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂`.

Establish `hval` using `value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ`. Establish `hg` using `congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval`. Rewrite `hg` using `[gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow]`. Establish `hpow` using `congrArg (psJet m) (hP S _ q hq0 k)`. Rewrite `hpow` using `[psJet_mul, psJet_pow, ← hexp, hr m, psJet_one]`.

Rewrite using `[psJet_mul, hg]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpow, mul_one]`. Use `_ = _ := by ring`.
-/
theorem gaugeUniq_of' (hB : BetaUniqSt) (hR : GaugeRatioSt) (hP : ExpPowSt) : GaugeUniqSt := by
  intro E _ _ _ H Dw l Xo c S _ _ _ y x hx e e' he he'
  have hL := Xo.univ.t.PP.isLB
  choose u hu using fun m => ratio_of_gen Xo.univ.t.PP.L hL (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ))
    (e m) (e' m) (he.gen m) (he'.gen m)
  let g : ∀ m, Jet S (Fin 1 × Fin (dL Dw)) m := fun m => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (u m).val
  have hpull : ∀ (m : ℕ) (B : Type) [CommRing B] [Algebra S B] (f : Jet S (Fin 1 × Fin (dL Dw)) m →ₐ[S] B),
      gam B (pullUnit (homAt y.x f).left (u m)).val = f (g m) := fun m B _ _ f =>
    gam_pullUnit (f : Jet S (Fin 1 × Fin (dL Dw)) m →+* B) (u m)
  have htr : ∀ m, jetTrunc (g (m + 1)) = g m := by
    intro m
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetTrunc : Jet S (Fin 1 × Fin (dL Dw)) (m + 1) →ₐ[S] _)).left (hu (m + 1))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (hu m) (he.trunc m) (he'.trunc m)
    have h2 := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    exact (hpull (m + 1) _ jetTrunc).symm.trans h2
  obtain ⟨r, hr⟩ := exists_ps_of_compat g htr
  have hrig : MvPowerSeries.constantCoeff r = 1 := by
    have h1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetAug : Jet S (Fin 1 × Fin (dL Dw)) 0 →ₐ[S] S)).left (hu 0)
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ h1 (scaled_one _) he.rig he'.rig
    have h2 := congrArg (fun v => gam S (Units.val v)) hU
    simp only [Units.val_one, map_one] at h2
    rw [← jetAug_psJet 0 r, hr 0]
    exact (hpull 0 S jetAug).symm.trans h2
  have hid : ∀ a : 𝓞 E, MvPowerSeries.rescale (sc (Dw := Dw) c S (1 + a * H.bar a)) r =
      MvPowerSeries.rescale (sc (Dw := Dw) c S a) r ^ 2 * r *
        MvPowerSeries.rescale (sc (Dw := Dw) c S (a * H.bar a)) r := by
    intro a
    obtain ⟨β, hβg, hβr, hβc⟩ := he.coc a
    obtain ⟨β', hβ'g, hβ'r, hβ'c⟩ := he'.coc a
    obtain rfl := hB E H Dw l Xo a β β' hβg hβ'g hβr hβ'r
    refine GermFun.psJet_inj fun m => ?_
    have s1 := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (1 + a * H.bar a)))).left (hu m)
    have sa := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c a))).left (hu m)
    have sb := scaled_pull Xo.univ.t.PP.L _ _
      (homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c (a * H.bar a)))).left (hu m)
    have srhs := scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_one (LB.pullGen Xo.univ.t.PP.L _ _ β (x m).left))
      (scaled_mul Xo.univ.t.PP.L _ _ _ _ (scaled_genPow _ _ sa 2) (scaled_mul Xo.univ.t.PP.L _ _ _ _ (hu m) sb))
    have hU := corr_scaled Xo.univ.t.PP.L hL _ _ _ _ _ _ _ _ _ _ s1 srhs (hβc m) (hβ'c m)
    have hv := congrArg (fun v => gam (Jet S (Fin 1 × Fin (dL Dw)) m) (Units.val v)) hU
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, one_mul] at hv
    rw [hpull, hpull, hpull] at hv
    have hv' : jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (1 + a * H.bar a) i) * MvPolynomial.X i) (g m) =
        jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S a i) * MvPolynomial.X i) (g m) ^ 2 *
          (g m * jetSubstP m (fun i => MvPolynomial.C (sc (Dw := Dw) c S (a * H.bar a) i) * MvPolynomial.X i) (g m)) :=
      hv
    rw [psJet_mul, psJet_mul, psJet_pow, ← jetSubstP_scale, ← jetSubstP_scale, ← jetSubstP_scale, hr m, hv']
    ring
  obtain ⟨q, hq0, hdeg, hpair, hexp⟩ := ratio_exp hR c S r hrig hid
  refine ⟨q, hq0, hdeg, hpair, fun k F f f' hf hf' => ?_⟩
  refine GermFun.psJet_inj fun m => ?_
  obtain ⟨F₁, τ₁, hP₁, hC₁, hV₁⟩ := hf m
  obtain ⟨F₂, τ₂, hP₂, hC₂, hV₂⟩ := hf' m
  have hF := GermFun.pull_unique _ _ _ _ _ _ _ _ hP₁ hP₂
  subst hF
  have sg := scaled_genPow (fun _ : Fin 1 => (x m).left) (fun _ => (1 : ℤ)) (hu m) k
  have sτ := corr_scaled_left Xo.univ.t.PP.L hL (x m).left (k : ℤ) _ _ τ₁ τ₂ _ _ _ sg hC₁ hC₂
  have hval := value_scaled Xo.univ.t.G Xo.univ.t.PP.L hL (k : ℤ) _ (x m) τ₁ τ₂ _ _ _ hV₁ hV₂ sτ
  have hg := congrArg (gam (Jet S (Fin 1 × Fin (dL Dw)) m)) hval
  rw [gam_toΓ, map_mul, gam_toΓ, Units.val_pow_eq_pow_val, map_pow] at hg
  have hpow := congrArg (psJet m) (hP S _ q hq0 k)
  rw [psJet_mul, psJet_pow, ← hexp, hr m, psJet_one] at hpow
  rw [psJet_mul, hg]
  calc psJet m f' = psJet m f' * (g m ^ k * psJet m (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S))) := by
        rw [hpow, mul_one]
    _ = _ := by ring

end GaugeR

/- English proof (translation)
The claim follows from `GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k`.
-/
theorem gaugeUniq_of (hB : BetaUniqSt) : GaugeUniqSt :=
  GaugeR.gaugeUniq_of' hB GRPf.gaugeRatio fun _ _ _ _ q hq k => GaugeR.exp_pow_mul_exp_neg q hq k

/- English proof (translation)
The claim follows from `gaugeUniq_of (betaUniq_of_global hG)`.
-/
theorem gaugeUniq_of_global (hG : GlobalFnsSt) : GaugeUniqSt :=
  gaugeUniq_of (betaUniq_of_global hG)

end Formalism.MainNotions.ModuliIntegralCharts.H1
