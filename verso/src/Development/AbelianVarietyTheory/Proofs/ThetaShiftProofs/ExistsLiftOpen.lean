import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FrameChangeExistsUniqueInvertible
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsIsArcFr
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators

noncomputable section

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section Units

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Establish `h` using `IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ) (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)`. Rewrite `h` using `[map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))]`. Conclude with `isUnit_of_mul_isUnit_left h`.
-/
theorem arcιR_isUnit_mul (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) :
    IsUnit (arcιR Dw V ϖ (PowerSeries.C ϖ * PowerSeries.X)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  exact isUnit_of_mul_isUnit_left h

/- English proof (translation)
Establish `h` using `IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ) (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)`. Rewrite `h` using `[map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))]`. Establish `h2` using `isUnit_of_mul_isUnit_right h`. Establish `h3` using `isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) => (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Fi …`. Rewrite `h3` using `[RingHom.map_det]`.

Conclude with `h3`.
-/
theorem letMR_det_isUnit (Dw : Datum H) (V : Type) [CommRing V] (ϖ : V) (τ : E →+* ℂ) :
    IsUnit (letMR Dw V ϖ τ).det := by
  classical
  have h := IsLocalization.Away.algebraMap_isUnit (S := ArcSR Dw V ϖ)
    (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)
  rw [map_mul (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))] at h
  have h2 := isUnit_of_mul_isUnit_right h
  have h3 := isUnit_of_dvd_unit (map_dvd (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ))
    (Finset.dvd_prod_of_mem (fun τ : E →+* ℂ => Matrix.det (Matrix.of fun i k : Fin (Dw.mult τ) =>
      (MvPolynomial.X (⟨τ, i, k⟩ : ArcLt Dw) : MvPolynomial (ArcLt Dw) (PowerSeries V)))) (Finset.mem_univ τ))) h2
  rw [RingHom.map_det] at h3
  exact h3

/- English proof (translation)
Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ`. Establish `h` using `arcιR_isUnit_mul Dw V ϖ`. Rewrite `h` using `[map_mul (arcιR Dw V ϖ)]`. Rewrite using `[map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ), map_pow (arcιR Dw V ϖ)]`. Conclude with `((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)`.
-/
theorem arcιR_C_isUnit (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) {v : V} (hv : v ≠ 0) : IsUnit (arcιR Dw V ϖ (PowerSeries.C v)) := by
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv hϖ
  have h := arcιR_isUnit_mul Dw V ϖ
  rw [map_mul (arcιR Dw V ϖ)] at h
  rw [map_mul (PowerSeries.C (R := V)), map_pow (PowerSeries.C (R := V)), map_mul (arcιR Dw V ϖ),
    map_pow (arcιR Dw V ϖ)]
  exact ((u.isUnit.map _).map _).mul ((isUnit_of_mul_isUnit_left h).pow n)

end Units

/- English proof (translation)
Set `p : Sp S ⟶ pullback Y.s (spMap β)` to `pullback.lift χ (spMap g) hcond`. Establish `hr : Set.range p ⊆ Set.range Y.jQ`. Introduce and unpack `_ ⟨q, rfl⟩`. Rewrite using `[← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]`. Take `⟨w, hw⟩` from `hj q`.

Rewrite using `[← hw]`. Establish `h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G`. Rewrite using `[Y.ab_gen]`. Conclude with `⟨w, rfl⟩`. Simplify `h2` using `only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage]`.

Use `Y.jQ_open` as an intermediate fact. Use `⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩` and prove the remaining obligations. Use `show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _`. Rewrite using `[← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]`. Rewrite using `[← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]`.
-/
theorem exists_lift_open {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {S : Type} [CommRing S] (g : c.F →+* S) (χ : Sp S ⟶ Y.X) (hcond : χ ≫ Y.s = spMap g ≫ spMap β)
    (hj : ∀ q : Sp S, χ q ∈ Set.range Y.j) :
    ∃ z : Sp S ⟶ Xo.XF c, z ≫ Y.j = χ ∧ z ≫ pullback.snd _ _ = spMap g := by
  let p : Sp S ⟶ pullback Y.s (spMap β) := pullback.lift χ (spMap g) hcond
  have hr : Set.range p ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst]
    obtain ⟨w, hw⟩ := hj q
    rw [← hw]
    have h2 : Y.jQ w ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]; exact ⟨w, rfl⟩
    simpa only [Model.j, Scheme.Hom.comp_apply, Set.mem_preimage] using h2
  have := Y.jQ_open
  refine ⟨IsOpenImmersion.lift Y.jQ p hr, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ p hr ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Y.jQ_over, ← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

/- English proof (translation)
Introduce `L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth`. Set `ι` to `arcιR Dw Tv.V ϖ`. Set `κ : Tv.V →+* ArcSR Dw Tv.V ϖ` to `ι.comp (PowerSeries.C (R := Tv.V))`. Establish `hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y)` using `fun y => arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)`. Set `g : Tv.Fr →+* ArcSR Dw Tv.V ϖ` to `IsLocalization.lift hκ`.

Establish `hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v` using `fun v => IsLocalization.lift_eq hκ v`. Use `letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra`. Establish `halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x)` using `fun _ => rfl`. Use `⟨alg, ?_, ?_⟩` and prove the remaining obligations. Introduce `x v n h`.

Establish `h2` using `congrArg g h`. Rewrite `h2` using `[map_mul, map_pow, hg, hg]`. Conclude with `h2`. Establish `hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R` using `Tv.V)).comp b) := by ext1 x`. Establish `h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x)` using `RingHom.congr_fun hfb x`.

Use `show g (f (β x)) = κ (b x)`. Rewrite using `[h1, hg]`. Establish `hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β`. Rewrite using `[Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]`. Take `⟨z, hz1, hz2⟩` from `exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by`.

Introduce `q`. Rewrite using `[Scheme.Hom.comp_apply]`. Use `hj _ fun h => ?_` and prove the remaining obligations. Establish `h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal` using `h`. Conclude with `q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))`.

Establish `hflat` using `(GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1`. Take `⟨y₀, -, hy₀⟩` from `exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush) (ArcSR Dw Tv.V ϖ) ι z hflat hz1 (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl) (fun τ x => by rw [halg, ← hρ, hg]; rfl)`. Take `⟨yR, hyR⟩` from `(frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1 (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one`. Conclude with `⟨y₀, yR, hy₀, hyR⟩`.
-/
theorem exists_dvr_frPt : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Tv : CDVR) (ϖ : Tv.V) (f : c.F →+* Tv.Fr) (b : O →+* Tv.V) (a : ArcIn Dw l β Tv.V b) (χ : Sp (PowerSeries Tv.V) ⟶ Y.X) (W : Wit Y a χ) (ρ : (E →+* ℂ) → (𝓞 E →+* Tv.V)) (e : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Out.GtPt a.D₀ (epsR Tv.V)) (th : a.D₀.P.L.Sec), Irreducible ϖ → f.comp β = (algebraMap Tv.V Tv.Fr).comp b → (∀ τ x, algebraMap Tv.V Tv.Fr (ρ τ x) = f (embK c τ x)) → χ ≫ Y.s = spMap (PowerSeries.C (R := Tv.V)) ≫ spMap b → (∀ x : Sp (PowerSeries Tv.V), PowerSeries.C ϖ * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → Mono (spMap β) → PushInvertible Y.t.G Y.t.PP.L → ArcBasis W ρ e → ThNZ th → ∃ (_ : Algebra c.F (ArcSR Dw Tv.V ϖ)), (∀ (x : c.F) (v : Tv.V) (n : ℕ), f x * algebraMap Tv.V Tv.Fr ϖ ^ n = algebraMap Tv.V Tv.Fr v → algebraMap c.F (ArcSR Dw Tv.V ϖ) x * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ) ^ n = arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) v)) ∧ ∃ y₀ yR : FrPt Xo c (ArcSR Dw Tv.V ϖ), IsArcFr W e th (arcιR Dw Tv.V ϖ) y₀ ∧ FrChg (letMR Dw Tv.V ϖ) 1 y₀ yR := by
  intro L1 L2 E _ _ _ H Dw l Xo c O _ β Y Tv ϖ f b a χ W ρ e th hϖ hfb hρ hχ hj _ hpush hbasis hth
  let ι := arcιR Dw Tv.V ϖ
  let κ : Tv.V →+* ArcSR Dw Tv.V ϖ := ι.comp (PowerSeries.C (R := Tv.V))
  have hκ : ∀ y : nonZeroDivisors Tv.V, IsUnit (κ y) := fun y =>
    arcιR_C_isUnit Dw Tv.V hϖ (nonZeroDivisors.ne_zero y.2)
  let g : Tv.Fr →+* ArcSR Dw Tv.V ϖ := IsLocalization.lift hκ
  have hg : ∀ v, g (algebraMap Tv.V Tv.Fr v) = κ v := fun v => IsLocalization.lift_eq hκ v
  letI alg : Algebra c.F (ArcSR Dw Tv.V ϖ) := (g.comp f).toAlgebra
  have halg : ∀ x, algebraMap c.F (ArcSR Dw Tv.V ϖ) x = g (f x) := fun _ => rfl
  refine ⟨alg, ?_, ?_⟩
  · intro x v n h
    have h2 := congrArg g h
    rw [map_mul, map_pow, hg, hg] at h2
    exact h2
  · have hcomp : (algebraMap c.F (ArcSR Dw Tv.V ϖ)).comp β = ι.comp ((PowerSeries.C (R := Tv.V)).comp b) := by
      ext1 x
      have h1 : f (β x) = algebraMap Tv.V Tv.Fr (b x) := RingHom.congr_fun hfb x
      show g (f (β x)) = κ (b x)
      rw [h1, hg]
    have hcond : (spMap ι ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcSR Dw Tv.V ϖ)) ≫ spMap β := by
      rw [Category.assoc, hχ, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
    obtain ⟨z, hz1, hz2⟩ := exists_lift_open Y (algebraMap c.F (ArcSR Dw Tv.V ϖ)) (spMap ι ≫ χ) hcond (by
      intro q
      rw [Scheme.Hom.comp_apply]
      refine hj _ fun h => ?_
      have h' : ι (PowerSeries.C ϖ * PowerSeries.X) ∈ q.asIdeal := h
      exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (arcιR_isUnit_mul Dw Tv.V ϖ)))
    have hflat := (GlobalTheory.LetterDenom.main E H Dw Tv ϖ hϖ.ne_zero).2.2.1
    obtain ⟨y₀, -, hy₀⟩ := exists_isArcFr L1 L2 E H Dw l Xo c O β Y Tv.V b a χ W ρ e th hbasis hth (Or.inr hpush)
      (ArcSR Dw Tv.V ϖ) ι z hflat hz1
      (by rw [pullback.condition, ← Category.assoc, hz2, ← spMap_comp]; rfl)
      (fun τ x => by rw [halg, ← hρ, hg]; rfl)
    obtain ⟨yR, hyR⟩ := (frChg_exists_unique_units E H Dw l Xo c (ArcSR Dw Tv.V ϖ) (letMR Dw Tv.V ϖ) 1 y₀).1
      (letMR_det_isUnit Dw Tv.V ϖ) isUnit_one
    exact ⟨y₀, yR, hy₀, hyR⟩

end GlobalTheory.ArcQ
