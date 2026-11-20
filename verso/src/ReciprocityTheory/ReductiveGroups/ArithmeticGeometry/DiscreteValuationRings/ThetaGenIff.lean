import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenFam

set_option autoImplicit false
set_option linter.overlappingInstances false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm SectionScalarValuation

section Scale

end Scale

section Integral

open IsLocalRing

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

/- English proof (translation)
Use `flat_G U.toUnifPre` as an intermediate fact. Use `flat_B (D := D)` as an intermediate fact. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Establish `hIϖ : I = Ideal.span {ϖ}`. Rewrite using `[hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]`.

Take `⟨F, hF, -⟩` from `(U.expand 1 le_rfl).1 (secK U.toUnifPre s)`. Establish `hF0` using `hF`. Take `⟨r, hr0, σ, f, hσ, hfK, hexp⟩` from `hF`. Establish `hσr` using `sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ`. Take `⟨n, u, hru⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ`.

Set `τ : H0 U.LG.L 1` to `SecOps.secScale (scal G.hom (u : R)) s`. Establish `hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j` using `fun j => by`. Rewrite using `[hσr, hru]`. Use `show _ = _ * (toW G.hom _ (u : R) * s.f j)`. Rewrite using `[map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]`.

Take `⟨g, hfg, hexpg⟩` from `expand_div_pow U.toUnifPre ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp`. Set `g' : ∀ α, D.toPre.SecB 1 α` to `fun α => SecOps.secScale (scal D.toPre.P.A.hom ((u⁻¹ : Rˣ) : R)) (g α)`. Establish `hexp' : ∀ e, U.ExpandsAt e 1 s g'` using `fun e => expandsAt_scale U.toUnifPre ((u⁻¹ : Rˣ) : R) τ s (fun j => by show _ = _ * (toW G.hom _ (u : R) * s.f j)`. Rewrite using `[← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]) g g' (fun α j => rfl) e (hexpg e)`. Establish `hgF : ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (F.s α) (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1`.

Introduce `α j₁ j₂ hc`. Establish `e` using `hfK α j₁ j₂ hc`. Establish `hf' : (f α).f j₂ = toW D.toPre.P.A.hom _ r * (g' α).f j₂`. Rewrite using `[hfg α j₂]`. Use `show _ = _ * (toW _ _ ((u⁻¹ : Rˣ) : R) * (g α).f j₂)`.

Rewrite using `[← _root_.mul_assoc, ← map_mul, hru, mul_comm (u : R), _root_.mul_assoc, Units.mul_inv, _root_.mul_one]`. Establish `hBF : (DegPre.BF D.toPre (FractionRing R)).hom = (pullback.fst _ _ ≫ jFK (R` using `R) (FractionRing R)) ≫ jK R := by`. Simplify using `[DegPre.BF, TF]`. Establish `hw : (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom = (DegPre.BF D.toPre (FractionRing R)).hom` using `Over.w _`. Use `erw [hf', map_mul, app_toW, map_mul, toW_res, resTop_scal, toW_congr hw] at e`.

Establish `hu` using `isUnit_toW_of_K (pullback.fst _ _ ≫ jFK (R := R) (FractionRing R)) (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) hr0`. Rewrite `hu` using `[← toW_congr hBF]`. Establish `e2` using `hu.mul_left_cancel e`. Establish `h1 : resTop (LB.wchart D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) j₁ ⊓ LB.wchart D.toPre.P.L (fun k => (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.famφB α k) j₂) (1 : Γ((DegPre.BF D.toPre (FractionRing R)).left, ⊤)) = 1` using `map_one _`. Rewrite using `[h1, _root_.one_mul]`.

Conclude with `e2`. Conclude with `⟨F, g', hF0, hexp', hgF⟩`.
-/
theorem integral_exp [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G) (s : H0 U.LG.L 1) :
    ∃ (F : Fam D.toPre (FractionRing R) 1) (g' : ∀ α, D.toPre.SecB 1 α), U.Expands 1 (secK U.toUnifPre s) F ∧
      (∀ e, U.ExpandsAt e 1 s g') ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α)
        (DegPre.famε 1) (F.s α) (D.toPre.famφB α) (DegPre.famε 1) (g' α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  have := flat_G U.toUnifPre
  have := flat_B (D := D)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hIϖ : I = Ideal.span {ϖ} := by
    rw [hI, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
  obtain ⟨F, hF, -⟩ := (U.expand 1 le_rfl).1 (secK U.toUnifPre s)
  have hF0 := hF
  obtain ⟨r, hr0, σ, f, hσ, hfK, hexp⟩ := hF
  have hσr := sec_eq_of_secScal U.toUnifPre s σ (secK U.toUnifPre s) r (secK_rel U.toUnifPre s) hσ
  obtain ⟨n, u, hru⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr0 hϖ
  let τ : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (u : R)) s
  have hστ : ∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j := fun j => by
    rw [hσr, hru]
    show _ = _ * (toW G.hom _ (u : R) * s.f j)
    rw [map_mul, mul_comm (toW G.hom _ (u : R)), _root_.mul_assoc]
  obtain ⟨g, hfg, hexpg⟩ := expand_div_pow U.toUnifPre ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep hϖ.ne_zero hIϖ n σ τ hστ f hexp
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
  exact ⟨F, g', hF0, hexp', hgF⟩

/- English proof (translation)
Substitute `hI` using the available equality. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Use `flat_B (D := D)` as an intermediate fact. Take `⟨f, hexp, hgen⟩` from `hϑ 0`. Assume the negation of the conclusion as `hnz`.

Establish `hvan : ∀ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom (ϑ.f j) = 0` using `fun j => by`. Assume the negation of the conclusion as `h`. Conclude with `hnz ⟨j, h⟩`. Establish `hpG` using `ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep R (maximalIdeal R) D A G U.toUnifPre 0 1 ϑ f hvan hexp`. Establish `hB : ∀ j, (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app _ ((f 0).f j) = 0`.

Introduce `j`. Use `(U.gt 0).q_flat` as an intermediate fact. Use `(U.gt 0).q_surj` as an intermediate fact. Apply `app_injective_of_flat_surj (U.gt 0).q.left` to reduce the goal to its premises. Rewrite using `[map_zero]`.

Establish `h` using `hpG 0 j`. Establish `e : (U.gt 0).pG.left = (U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)` using `rfl`. Rewrite `h` using `[e, Scheme.Hom.comp_app]`. Conclude with `h`. Take `⟨g0, hg0⟩` from `sec_div D.toPre.P.A.hom (f 0) hϖ.ne_zero (J := maximalIdeal R ^ (0 + 1)) (by rw [zero_add, pow_one, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]) hB`.

Take `⟨a, ha, -⟩` from `hgen g0`. Establish `hf0 : ∀ j, (f 0).f j = 0`. Introduce `j`. Establish `h1 : toW D.toPre.P.A.hom _ (1 - ϖ * a) * (f 0).f j = 0`. Rewrite using `[map_sub, map_one, map_mul, sub_mul, _root_.one_mul, _root_.mul_assoc]`.

Use `ha j` as an intermediate fact. Rewrite `this` using `[resTop_scal]`. Rewrite using `[← this, ← hg0 j, sub_self]`. Use `toW_mul_eq_zero D.toPre.P.A.hom _ ?_ h1` and prove the remaining obligations. Introduce `h`.

Apply `hϖ.not_isUnit` to reduce the goal to its premises. Establish `h' : ϖ * a = 1` using `by linear_combination -h`. Conclude with `⟨⟨ϖ, a, h', by rw [mul_comm]; exact h'⟩, rfl⟩`. Take `⟨b, -, hb⟩` from `hgen (f 0)`. Establish `e1` using `hb 1 fun j => by rw [hf0 j, mul_zero]`.

Establish `e0` using `hb 0 fun j => by rw [hf0 j, mul_zero]`. Conclude with `one_ne_zero (e1.trans e0.symm)`.
-/
theorem nonzero_of_isTheta [IsDiscreteValuationRing R] (hI : I = maximalIdeal R) (U : Unif I D A G)
    {ϑ : H0 U.LG.L 1} (hϑ : IsTheta U ϑ) : NonzeroOnSpecial U ϑ := by
  subst hI
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have := flat_B (D := D)
  obtain ⟨f, hexp, hgen⟩ := hϑ 0
  by_contra hnz
  have hvan : ∀ j, ((fstG (maximalIdeal R) 0 G).left.app _).hom (ϑ.f j) = 0 := fun j => by
    by_contra h
    exact hnz ⟨j, h⟩
  have hpG := ReciprocityTheory.ChartRestriction.G.Out.WeightPf.weightIndep R (maximalIdeal R) D A G U.toUnifPre 0 1 ϑ f hvan hexp
  have hB : ∀ j, (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)).app _ ((f 0).f j) = 0 := by
    intro j
    have := (U.gt 0).q_flat
    have := (U.gt 0).q_surj
    apply app_injective_of_flat_surj (U.gt 0).q.left
    rw [map_zero]
    have h := hpG 0 j
    have e : (U.gt 0).pG.left = (U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) := rfl
    rw [e, Scheme.Hom.comp_app] at h
    exact h
  obtain ⟨g0, hg0⟩ := sec_div D.toPre.P.A.hom (f 0) hϖ.ne_zero (J := maximalIdeal R ^ (0 + 1))
    (by rw [zero_add, pow_one, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]) hB
  obtain ⟨a, ha, -⟩ := hgen g0
  have hf0 : ∀ j, (f 0).f j = 0 := by
    intro j
    have h1 : toW D.toPre.P.A.hom _ (1 - ϖ * a) * (f 0).f j = 0 := by
      rw [map_sub, map_one, map_mul, sub_mul, _root_.one_mul, _root_.mul_assoc]
      have := ha j
      rw [resTop_scal] at this
      rw [← this, ← hg0 j, sub_self]
    refine toW_mul_eq_zero D.toPre.P.A.hom _ ?_ h1
    intro h
    apply hϖ.not_isUnit
    have h' : ϖ * a = 1 := by linear_combination -h
    exact ⟨⟨ϖ, a, h', by rw [mul_comm]; exact h'⟩, rfl⟩
  obtain ⟨b, -, hb⟩ := hgen (f 0)
  have e1 := hb 1 fun j => by rw [hf0 j, mul_zero]
  have e0 := hb 0 fun j => by rw [hf0 j, mul_zero]
  exact one_ne_zero (e1.trans e0.symm)

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR.TG
