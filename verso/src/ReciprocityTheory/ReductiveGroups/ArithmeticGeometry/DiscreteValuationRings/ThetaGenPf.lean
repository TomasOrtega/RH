import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenIff

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing TG

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `flat_G U.toUnifPre` as an intermediate fact. Use `flat_B (D := D)` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hIϖ : I = Ideal.span {ϖ}`. Rewrite using `[hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]`.

Take `⟨F, hF, -⟩` from `(U.expand 1 le_rfl).1 (secK U.toUnifPre s)`. Take `⟨r, hr0, σ, f, hσ, hfK, hexp⟩` from `hF`. Establish `hσr` using `sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ`. Take `⟨n, u, hru⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ`. Set `τ : H0 U.LG.L 1` to `SecOps.secScale (scal G.hom (u : R)) s`.

Establish `hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j` using `fun j => by`. Rewrite using `[hσr, hru]`. Use `show _ = _ * (toW G.hom _ (u : R) * s.f j)`. Rewrite using `[map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]`. Take `⟨g, hfg, hexpg⟩` from `expand_div_pow U.toUnifPre hL4.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp`.

Set `g' : ∀ α, D.toPre.SecB 1 α` to `fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)`. Establish `hexp' : ∀ e, U.ExpandsAt e 1 s g'` using `fun e => expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by show _ = _ * (toW G.hom _ (u : R) * s.f j)`. Rewrite using `[← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)`. Establish `hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α) (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1`. Introduce `α j₁ j₂ hc`.

Establish `e` using `hfK α j₁ j₂ hc`. Establish `hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂`. Rewrite using `[hfg α j₂]`. Use `show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)`. Rewrite using `[← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]`.

Establish `hBF : (DegPre.BF D.toPre (FractionRing R)).hom = (pullback.fst _ _ ≫ jFK (R` using `R) (FractionRing R)) ≫ jK R := by`. Simplify using `[DegPre.BF, TF]`. Establish `hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom` using `Over.w _`. Use `erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e`. Establish `hu` using `isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0`.

Rewrite `hu` using `[← toW_congr hBF]`. Establish `e2` using `hu.mul_left_cancel e`. Establish `h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1` using `map_one _`. Rewrite using `[h1, _root_.one_mul]`. Conclude with `e2`.

Establish `hv` using `terms_vanish hϖ hI F g' hgF`. Establish `h0` using `leading_expansion_term_ne_zero hI U s hs g' (hexp' 0) hv`. Conclude with `fun e => ⟨g', hexp' e, generates_of_ne hLaws hI (g' 0) h0⟩`.
-/
theorem isTheta_of_nonzeroOnSpecial' (hLaws : Laws) (hL4 : Laws4) (hR : CLND R)
    [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1)
    (hs : NonzeroOnSpecial U s) : IsTheta U s := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre hL4.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
  let g' : ∀ α, D.toPre.SecB 1 α := fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)
  have hexp' : ∀ e, U.ExpandsAt e 1 s g' := fun e =>
    expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by
      show _ = _ * (toW G.hom _ (u : R) * s.f j)
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)
  have hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α)
      (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
    intro α j₁ j₂ hc
    have e := hfK α j₁ j₂ hc
    have hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂ := by
      rw [hfg α j₂]
      show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)
      rw [← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    have hBF : (DegPre.BF D.toPre (FractionRing R)).hom =
        (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) ≫ jK R := by
      simp [DegPre.BF, TF]
    have hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom :=
      Over.w _
    erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e
    have hu := isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R))
      (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0
    rw [← toW_congr hBF] at hu
    have e2 := hu.mul_left_cancel e
    have h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓
        LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂)
        (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1 := map_one _
    rw [h1, _root_.one_mul]
    exact e2
  have hv := terms_vanish hϖ hI F g' hgF
  have h0 := leading_expansion_term_ne_zero hI U s hs g' (hexp' 0) hv
  exact fun e => ⟨g', hexp' e, generates_of_ne hLaws hI (g' 0) h0⟩

end ReciprocityTheory.ChartRestriction.G.DVR
