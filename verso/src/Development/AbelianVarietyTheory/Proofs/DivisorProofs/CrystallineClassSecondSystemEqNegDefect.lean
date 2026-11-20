import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleFirstOrderTaylorSqZeroStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

/- English proof (translation)
Use `set f₀ := (redMor hI hk s₀).coef.pullbackOneCocycle f with hf₀`. Establish `e : f₀ = F.1 + ⟨d0 _ h, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ h⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f₀.1 = F.1.1 + d0 _ h`. Rewrite using `[hh]`.

Normalize the expressions using the abelian group laws. Set `hU : ∀ U : AffOp X₀, Sec s₀ U.unop.1` to `fun U ↦ @id (Sec s₀ U.unop.1) <| h (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))`. Set `qU : ∀ U : AffOp X₀, Sec s₀ U.unop.1` to `fun U ↦ @id (Sec s₀ U.unop.1) <| ev f (Q U)`. Set `k : C0 (OAff s₀)` to `fun U ↦ hU U - S.p U (g U) - qU U`. Establish `hk0 : d0 _ k = 0`.

Use function extensionality and compare the values at `U V a`. Set `tr` to `Thick.trivHom (hx := affPt_w s₀ U.unop) (T := Thick.triv _ _ (affPt_w s₀ V.unop)) (Sec.res s₀ (leOfHom a.unop)) (affPt_res s₀ (leOfHom a.unop))`. Establish `h1` using `congrArg (fun q ↦ q _ _ tr) hh`. Simplify using `only [amitsur_d0_apply, Pi.sub_apply] at h1`. Establish `h0 : F.1.1 _ _ tr = 0` using `F.2 tr rfl rfl`.

Rewrite `h1` using `[h0, sub_zero]`. Establish `h1' : hU V - Sec.res s₀ (leOfHom a.unop) (hU U) = (f₀.1 _ _ tr : Sec s₀ V.unop.1)` using `h1`. Establish `h2` using `ev_sq f (Q U) ((redMor hI hk s₀).functor.map tr) ((S.thick hI).map a) (Q V) fun c ↦ by`. Express the relevant statement in the definitionally equal form `Sec.res s₀ (leOfHom a.unop) ((Q U).φ c) = (Q V).φ (mp S.F a c)`. Rewrite using `[hQ, hQ, S.nat]`.

Both sides reduce to the same expression. Establish `h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U)`. Use `congrArg (fun q ↦ q U V a) hg` as an intermediate fact. Simplify using `only [amitsur_d0_apply] at this`. Conclude with `this.symm`.

Establish `h2' : Sec.res s₀ (leOfHom a.unop) (qU U) + (f₀.1 _ _ tr : Sec s₀ V.unop.1) = @id (Sec s₀ V.unop.1) ((Q V).φ (ev f ((S.thick hI).map a))) + qU V` using `h2`. Rewrite `h2'` using `[hQ, id]`. Use `erw [h3] at h2'`. Establish `nat' : S.p V (mp S.F a (g U)) = Sec.res s₀ (leOfHom a.unop) (S.p U (g U))` using `S.nat a (g U)`. Rewrite `h2'` using `[map_sub, nat']`.

Express the relevant statement in the definitionally equal form `k V - Sec.res s₀ (leOfHom a.unop) (k U) = 0`. Simplify using `only [k, map_sub]`. Take the linear combination `h1' + h2'`. Take `⟨r, hr⟩` from `hC k hk0`. Establish `hD : D R₀ (Sec s₀ U.unop.1) (k U) = 0` using `by rw [hr U]; exact (D R₀ _).map_algebraMap r`.

Simplify using `only [k, map_sub] at hD`. Rewrite using `[e, connForm_add, crystallineConnectionForm_coboundaryZero, ← sub_eq_zero]`. Express the relevant statement in the definitionally equal form `connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (hU U) - D R₀ (Sec s₀ U.unop.1) (qU U) - (connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (S.p U (g U))) = 0`. Rewrite using `[← hD]`. Normalize the expressions using the abelian group laws.
-/
theorem connForm_sub_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
    {s₀ : X₀ ⟶ Sp R₀} (hI : I ^ 2 = 0) (hk : RingHom.ker π = I) (hC : Const s₀) (S : Sys I π s₀)
    (Q : ∀ U : AffOp X₀, S.thickObj hI U ⟶
      (redMor hI hk s₀).obj (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop)))
    (hQ : ∀ U b, (Q U).φ b = S.p U b) (f : Z1 (O (divided₂ hI) (s₀ ≫ spMap π))) (g : C0 S.F)
    (hg : d0 S.F g = ((S.coef hI).pullbackOneCocycle f).1) (F : Form s₀) (h : C0 (O (dp0 R₀) s₀))
    (hh : d0 _ h = ((redMor hI hk s₀).coef.pullbackOneCocycle f).1 - F.1.1) (U : AffOp X₀) :
    connForm ((redMor hI hk s₀).coef.pullbackOneCocycle f) (affPt s₀ U.unop) (affPt_w s₀ U.unop) -
        D R₀ (Sec s₀ U.unop.1) (ev f (Q U) : Sec s₀ U.unop.1) =
      connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) + D R₀ (Sec s₀ U.unop.1) (S.p U (g U)) := by
  set f₀ := (redMor hI hk s₀).coef.pullbackOneCocycle f with hf₀
  have e : f₀ = F.1 + ⟨d0 _ h, commAlgFunctorCoboundaryZero_mem_cocyclesOne _ h⟩ := by
    apply Subtype.ext
    change f₀.1 = F.1.1 + d0 _ h
    rw [hh]; abel
  let hU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦
    @id (Sec s₀ U.unop.1) <| h (Thick.triv (Sec s₀ U.unop.1) (affPt s₀ U.unop) (affPt_w s₀ U.unop))
  let qU : ∀ U : AffOp X₀, Sec s₀ U.unop.1 := fun U ↦ @id (Sec s₀ U.unop.1) <| ev f (Q U)
  let k : C0 (OAff s₀) := fun U ↦ hU U - S.p U (g U) - qU U
  have hk0 : d0 _ k = 0 := by
    funext U V a
    let tr := Thick.trivHom (hx := affPt_w s₀ U.unop) (T := Thick.triv _ _ (affPt_w s₀ V.unop))
      (Sec.res s₀ (leOfHom a.unop)) (affPt_res s₀ (leOfHom a.unop))
    have h1 := congrArg (fun q ↦ q _ _ tr) hh
    simp only [amitsur_d0_apply, Pi.sub_apply] at h1
    have h0 : F.1.1 _ _ tr = 0 := F.2 tr rfl rfl
    rw [h0, sub_zero] at h1
    have h1' : hU V - Sec.res s₀ (leOfHom a.unop) (hU U) = (f₀.1 _ _ tr : Sec s₀ V.unop.1) := h1
    have h2 := ev_sq f (Q U) ((redMor hI hk s₀).functor.map tr) ((S.thick hI).map a) (Q V) fun c ↦ by
      change Sec.res s₀ (leOfHom a.unop) ((Q U).φ c) = (Q V).φ (mp S.F a c)
      rw [hQ, hQ, S.nat]; rfl
    have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
      have := congrArg (fun q ↦ q U V a) hg
      simp only [amitsur_d0_apply] at this
      exact this.symm
    have h2' : Sec.res s₀ (leOfHom a.unop) (qU U) + (f₀.1 _ _ tr : Sec s₀ V.unop.1) =
        @id (Sec s₀ V.unop.1) ((Q V).φ (ev f ((S.thick hI).map a))) + qU V := h2
    rw [hQ, id] at h2'
    erw [h3] at h2'
    have nat' : S.p V (mp S.F a (g U)) = Sec.res s₀ (leOfHom a.unop) (S.p U (g U)) := S.nat a (g U)
    rw [map_sub, nat'] at h2'
    change k V - Sec.res s₀ (leOfHom a.unop) (k U) = 0
    simp only [k, map_sub]
    linear_combination h1' + h2'
  obtain ⟨r, hr⟩ := hC k hk0
  have hD : D R₀ (Sec s₀ U.unop.1) (k U) = 0 := by rw [hr U]; exact (D R₀ _).map_algebraMap r
  simp only [k, map_sub] at hD
  rw [e, connForm_add, crystallineConnectionForm_coboundaryZero, ← sub_eq_zero]
  change connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (hU U) - D R₀ (Sec s₀ U.unop.1) (qU U) -
    (connForm F.1 _ _ + D R₀ (Sec s₀ U.unop.1) (S.p U (g U))) = 0
  rw [← hD]; abel

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk X₀ s₀ hC S S' Φ θ hΘ c hc w hw z hz`. Establish `T` using `fun (U V : AffOp X₀) ↦ GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V`. Use `choose Q hQ using fun U ↦ (T U U).1`. Take `⟨f, rfl⟩` from `H1.mk_surjective _ c`. Take `⟨g, hg⟩` from `H1.mk_eq_zero.1 (LinearMap.mem_ker.1 hc)`.

Take `⟨F, hF, hFw⟩` from `hw`. Take `⟨h, hh⟩` from `H1.mk_eq_mk.1 (show H1.mk _ ((redMor hI hk s₀).coef.pullbackOneCocycle f) = H1.mk _ F.1 from hF.symm)`. Set `ΦU : ∀ U : AffOp X₀, S.thickObj hI U ⟶ S'.thickObj hI U` to `fun U ↦ S.thickHom S' hI (𝟙 U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) fun b ↦ (Φ.red U b).trans (mp_id (OAff s₀) U (S.p U b)).symm`. Express the relevant statement in the definitionally equal form `H1.mk _ ((S'.coef hI).pullbackOneCocycle f) = -H1.mk _ z`. Rewrite using `[← map_neg, H1.mk_eq_mk]`.

Use `⟨fun U ↦ Φ.φ U (g U) + ev f (ΦU U), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `U V a`. Set `α : S.thickObj hI U ⟶ S'.thickObj hI V` to `ΦU U ≫ (S'.thick hI).map a`. Set `β : S.thickObj hI U ⟶ S'.thickObj hI V` to `(S.thick hI).map a ≫ ΦU V`. Establish `hθ : IsTheta I (S.p U) α.φ β.φ (θ U V a)` using `hΘ U V a`.

Establish `tay` using `(T U V).2 (Q U) (hQ U) α β (θ U V a) hθ f`. Rewrite `tay` using `[connForm_sub_eq hI hk hC S Q hQ f g hg F h hh U, map_add]`. Use `erw [hθ.der (g U)] at tay`. Establish `hw' : connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) = w.1 U`. Rewrite using `[← hFw, cmpForm_apply]`.

Rewrite `tay` using `[hw', ← hz]`. Establish `E1 : ev f α = mp S'.F a (ev f (ΦU U)) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a))` using `ev_comp f _ _`. Establish `E2 : ev f β = Φ.φ V (ev f ((S.thick hI).map a)) + ev f (ΦU V)` using `ev_comp f _ _`. Establish `h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U)`. Use `congrArg (fun q ↦ q U V a) hg` as an intermediate fact.

Simplify using `only [amitsur_d0_apply] at this`. Conclude with `this.symm`. Rewrite `E2` using `[h3, map_sub]`. Establish `E3 : α.φ (g U) = mp S'.F a (Φ.φ U (g U))` using `rfl`. Establish `E4 : β.φ (g U) = Φ.φ V (mp S.F a (g U))` using `rfl`.

Use `erw [E3, E4] at tay`. Express the relevant statement in the definitionally equal form `Φ.φ V (g V) + ev f (ΦU V) - mp S'.F a (Φ.φ U (g U) + ev f (ΦU U)) = @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) - -z.1 U V a`. Rewrite using `[map_add]`. Establish `key : ∀ x y z' p q r s t u : S'.F.obj V, x - y = z' + (p - q) → y = r + s → x = t - q + u → t + u - (p + r) = s - -z'`. Introduce `x y z' p q r s t u h₁ h₂ h₃`.

Take the linear combination `h₁ + h₂ - h₃`. Conclude with `key _ _ _ _ _ _ _ _ _ tay E1 E2`.
-/
theorem r_eq_neg_defect : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ → ∀ (S S' : Sys I π s₀) (Φ : S.LocIso S') (θ : ∀ (U V : AffOp X₀) (_ : U ⟶ V), Ω[Sec s₀ U.unop.1⁄R₀] →+ S'.F.obj V), Φ.IsDefect θ → ∀ c ∈ S.K hI, ∀ w, FormOf hI hk c w → ∀ z : Z1 S'.F, (∀ U V a, z.1 U V a = θ U V a (w.1 U)) → S'.r hI c = -H1.mk _ z := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hC S S' Φ θ hΘ c hc w hw z hz
  have T := fun (U V : AffOp X₀) ↦ GlobalTheory.T.crystallineCocycle_firstOrder_taylor_sqZero R R₀ I hI π hπ hk X₀ s₀ S S' U V
  choose Q hQ using fun U ↦ (T U U).1
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 (LinearMap.mem_ker.1 hc)
  obtain ⟨F, hF, hFw⟩ := hw
  obtain ⟨h, hh⟩ := H1.mk_eq_mk.1
    (show H1.mk _ ((redMor hI hk s₀).coef.pullbackOneCocycle f) = H1.mk _ F.1 from hF.symm)
  let ΦU : ∀ U : AffOp X₀, S.thickObj hI U ⟶ S'.thickObj hI U := fun U ↦
    S.thickHom S' hI (𝟙 U) (Φ.φ U : S.F.obj U →ₐ[R] S'.F.obj U) fun b ↦
      (Φ.red U b).trans (mp_id (OAff s₀) U (S.p U b)).symm
  change H1.mk _ ((S'.coef hI).pullbackOneCocycle f) = -H1.mk _ z
  rw [← map_neg, H1.mk_eq_mk]
  refine ⟨fun U ↦ Φ.φ U (g U) + ev f (ΦU U), ?_⟩
  funext U V a
  let α : S.thickObj hI U ⟶ S'.thickObj hI V := ΦU U ≫ (S'.thick hI).map a
  let β : S.thickObj hI U ⟶ S'.thickObj hI V := (S.thick hI).map a ≫ ΦU V
  have hθ : IsTheta I (S.p U) α.φ β.φ (θ U V a) := hΘ U V a
  have tay := (T U V).2 (Q U) (hQ U) α β (θ U V a) hθ f
  rw [connForm_sub_eq hI hk hC S Q hQ f g hg F h hh U, map_add] at tay
  erw [hθ.der (g U)] at tay
  have hw' : connForm F.1 (affPt s₀ U.unop) (affPt_w s₀ U.unop) = w.1 U := by
    rw [← hFw, cmpForm_apply]
  rw [hw', ← hz] at tay
  have E1 : ev f α = mp S'.F a (ev f (ΦU U)) + @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) := ev_comp f _ _
  have E2 : ev f β = Φ.φ V (ev f ((S.thick hI).map a)) + ev f (ΦU V) := ev_comp f _ _
  have h3 : ev f ((S.thick hI).map a) = g V - mp S.F a (g U) := by
    have := congrArg (fun q ↦ q U V a) hg
    simp only [amitsur_d0_apply] at this
    exact this.symm
  rw [h3, map_sub] at E2
  have E3 : α.φ (g U) = mp S'.F a (Φ.φ U (g U)) := rfl
  have E4 : β.φ (g U) = Φ.φ V (mp S.F a (g U)) := rfl
  erw [E3, E4] at tay
  change Φ.φ V (g V) + ev f (ΦU V) - mp S'.F a (Φ.φ U (g U) + ev f (ΦU U)) =
    @id (S'.F.obj V) (ev f ((S'.thick hI).map a)) - -z.1 U V a
  rw [map_add]
  have key : ∀ x y z' p q r s t u : S'.F.obj V, x - y = z' + (p - q) → y = r + s → x = t - q + u →
      t + u - (p + r) = s - -z' := by
    intro x y z' p q r s t u h₁ h₂ h₃
    linear_combination h₁ + h₂ - h₃
  exact key _ _ _ _ _ _ _ _ _ tay E1 E2

end GlobalTheory.LiftSys
