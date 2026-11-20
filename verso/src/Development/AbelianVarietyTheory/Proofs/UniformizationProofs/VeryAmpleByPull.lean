import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw.VeryAmplePull

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cst_eq_appLE (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) :
    cst f W r = (f.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := rfl

/- English proof (translation)
Establish `e₁ : f.appLE ⊤ D le_top ≫ φ.appLE D W e = (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ W le_top`. Use `(Scheme.Hom.appLE_comp_appLE φ f ⊤ D W le_top e).trans (Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE f' (Spec.map (CommRingCat.ofHom g)) ⊤ ⊤ W le_top le_top).symm)` and prove the remaining obligations. Simplify using `only [h]`. Establish `e₂` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)`. Establish `e₃ : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom g)).appTop` using `(Scheme.Hom.app_eq_appLE (Spec.map (CommRingCat.ofHom g)) (U := ⊤)).symm`.

Rewrite using `[cst_eq_appLE, cst_eq_appLE]`. Use `(congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e₁).trans ?_` and prove the remaining obligations. Rewrite using `[e₃]`. Conclude with `congrArg (f'.appLE ⊤ W le_top).hom (congrArg (fun q => q.hom r) e₂).symm`.
-/
theorem appLE_cst {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (D : X.Opens) (W : X'.Opens)
    (e : W ≤ φ ⁻¹ᵁ D) (r : R) : (φ.appLE D W e).hom (cst f D r) = cst f' W (g r) := by
  have e₁ : f.appLE ⊤ D le_top ≫ φ.appLE D W e =
      (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top ≫ f'.appLE ⊤ W le_top := by
    refine (Scheme.Hom.appLE_comp_appLE φ f ⊤ D W le_top e).trans (Eq.trans ?_
      (Scheme.Hom.appLE_comp_appLE f' (Spec.map (CommRingCat.ofHom g)) ⊤ ⊤ W le_top le_top).symm)
    simp only [h]
  have e₂ := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g)
  have e₃ : (Spec.map (CommRingCat.ofHom g)).appLE ⊤ ⊤ le_top = (Spec.map (CommRingCat.ofHom g)).appTop :=
    (Scheme.Hom.app_eq_appLE (Spec.map (CommRingCat.ofHom g)) (U := ⊤)).symm
  rw [cst_eq_appLE, cst_eq_appLE]
  refine (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e₁).trans ?_
  rw [e₃]
  exact congrArg (f'.appLE ⊤ W le_top).hom (congrArg (fun q => q.hom r) e₂).symm

/- English proof (translation)
Establish `H` using `IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))`. Use `set p := pullback.fst f (Spec.map (CommRingCat.ofHom g)) with hp`. Use `set q := pullback.snd f (Spec.map (CommRingCat.ofHom g)) with hq`. Use `set u := pullback.lift φ f' h with hu`. Establish `up : u ≫ p = φ` using `pullback.lift_fst _ _ _`.

Establish `uq : u ≫ q = f'` using `pullback.lift_snd _ _ _`. Establish `: IsAffineHom p` using `MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance`. Establish `e' : W = u ⁻¹ᵁ (p ⁻¹ᵁ D)` using `by rw [e, ← up]; rfl`. Establish `po` using `(isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := D) le_top le_top (UY := p ⁻¹ᵁ D) (by simp)).1 (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hD)`. Establish `hs : Function.Surjective (u.appLE (p ⁻¹ᵁ D) W e'.le).hom`.

Substitute `e'` using the available equality. Rewrite using `[← Scheme.Hom.app_eq_appLE]`. Conclude with `u.app_surjective _ (hD.preimage p)`. Take `⟨y, rfl⟩` from `hs x`. Express the relevant statement in the definitionally equal form `y ∈ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom`.

Use `(show ⊤ ≤ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom from ?_) trivial` and prove the remaining obligations. Rewrite using `[← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]`. Introduce and unpack `_ (⟨d, rfl⟩ | ⟨c, rfl⟩)`. Establish `e₁` using `congrArg (fun k => k.hom d) (Scheme.Hom.appLE_comp_appLE u p D (p ⁻¹ᵁ D) W le_rfl e'.le)`. Simplify using `only [up] at e₁`.

Conclude with `(congrArg (· ∈ T) e₁).mpr (h₁ d)`. Establish `e₁` using `congrArg (fun k => k.hom c) (Scheme.Hom.appLE_comp_appLE u q ⊤ (p ⁻¹ᵁ D) W le_top e'.le)`. Simplify using `only [uq] at e₁`. Take `⟨c, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c`. Conclude with `(congrArg (· ∈ T) e₁).mpr (h₂ c)`.
-/
theorem closure_eq_top {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {f' : X' ⟶ Spec (CommRingCat.of R')}
    {φ : X' ⟶ X} (h : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) [IsClosedImmersion (pullback.lift φ f' h)]
    {D : X.Opens} (hD : IsAffineOpen D) {W : X'.Opens} (e : W = φ ⁻¹ᵁ D) (T : Subring Γ(X', W))
    (h₁ : ∀ a, (φ.appLE D W e.le).hom a ∈ T) (h₂ : ∀ c, cst f' W c ∈ T) (x : Γ(X', W)) : x ∈ T := by
  have H := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))
  set p := pullback.fst f (Spec.map (CommRingCat.ofHom g)) with hp
  set q := pullback.snd f (Spec.map (CommRingCat.ofHom g)) with hq
  set u := pullback.lift φ f' h with hu
  have up : u ≫ p = φ := pullback.lift_fst _ _ _
  have uq : u ≫ q = f' := pullback.lift_snd _ _ _
  have : IsAffineHom p := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  have e' : W = u ⁻¹ᵁ (p ⁻¹ᵁ D) := by rw [e, ← up]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := D) le_top le_top
      (UY := p ⁻¹ᵁ D) (by simp)).1
      (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hD)
  have hs : Function.Surjective (u.appLE (p ⁻¹ᵁ D) W e'.le).hom := by
    subst e'
    rw [← Scheme.Hom.app_eq_appLE]
    exact u.app_surjective _ (hD.preimage p)
  obtain ⟨y, rfl⟩ := hs x
  change y ∈ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom
  refine (show ⊤ ≤ T.comap (u.appLE (p ⁻¹ᵁ D) W e'.le).hom from ?_) trivial
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
  rintro _ (⟨d, rfl⟩ | ⟨c, rfl⟩)
  · have e₁ := congrArg (fun k => k.hom d) (Scheme.Hom.appLE_comp_appLE u p D (p ⁻¹ᵁ D) W le_rfl e'.le)
    simp only [up] at e₁
    exact (congrArg (· ∈ T) e₁).mpr (h₁ d)
  · have e₁ := congrArg (fun k => k.hom c) (Scheme.Hom.appLE_comp_appLE u q ⊤ (p ⁻¹ᵁ D) W le_top e'.le)
    simp only [uq] at e₁
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c
    exact (congrArg (· ∈ T) e₁).mpr (h₂ c)

/- English proof (translation)
Introduce `R _ X f H n s hP ⟨hcov, hs⟩ R' _ g X' f' φ h hcl H' W s' hP' _ hs'`. Establish `: IsAffineHom φ`. Establish `: IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom g)))` using `MorphismProperty.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))).flip inferInstance`. Rewrite using `[← pullback.lift_fst φ f' h]`. Use `infer_instance`.

Establish `loc : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i)` using `fun i => by`. Use extensionality with `y`. Use `(mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (φ y)).symm)` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hP (φ y)`. Establish `e` using `hs' i y j k hj hk`.

Rewrite `e` using `[gs_stalkMap φ y _ hj]`. Conclude with `⟨j, hj, (isUnit_map_iff (φ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩`. Take `⟨k, hk⟩` from `exists_chart hP' y`. Establish `e` using `hs' i y j k hj hk`. Conclude with `⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap φ y _ hj _).symm.trans e)).mp (u.map _))⟩`.

Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Use `top_le_iff.1 fun y _ => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩`. Take `⟨haff, r, hr, hsurj⟩` from `hs i`.

Use `⟨by rw [loc]; exact haff.preimage φ, fun j => (φ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩` and prove the remaining obligations. Take `⟨l, hl⟩` from `exists_chart hP (φ y)`. Establish `hm : φ y ∈ nonzeroLocus (s i) ⊓ H.U l` using `⟨(loc i).le hy.1, hl⟩`. Establish `e` using `congrArg (gs φ y _) (hr j l)`. Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`.

Establish `e₁` using `hs' j y l k hl hy.2`. Establish `e₂` using `hs' i y l k hl hy.2`. Establish `e₃` using `(Geo.Tor.gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))`. Use `(gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE φ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))` and prove the remaining obligations. Introduce `x`.

Use `closure_eq_top h haff (loc i) (RingHom.range _) (fun d => ?_) (fun c => ?_) x` and prove the remaining obligations. Take `⟨p, rfl⟩` from `hsurj d`. Use `⟨MvPolynomial.map g p, ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]`. Conclude with `congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (RingHom.ext fun c => (appLE_cst h _ _ _ c).symm)`.

Conclude with `⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩`.
-/
theorem veryAmpleBy_pull : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (φ : X' ⟶ X) (h : φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g))), IsClosedImmersion (pullback.lift φ f' h) → ∀ (H' : LB X') (w : LB.Iso H' (H.pull φ)) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → VeryAmpleBy f' H' s' := by
  intro R _ X f H n s hP ⟨hcov, hs⟩ R' _ g X' f' φ h hcl H' W s' hP' _ hs'
  have : IsAffineHom φ := by
    have : IsAffineHom (pullback.fst f (Spec.map (CommRingCat.ofHom g))) :=
      MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom g))).flip inferInstance
    rw [← pullback.lift_fst φ f' h]
    infer_instance
  have loc : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans
      (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (φ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hP (φ y)
      have e := hs' i y j k hj hk
      rw [gs_stalkMap φ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (φ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hP' y
      have e := hs' i y j k hj hk
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap φ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨?_, fun i => ?_⟩
  · refine top_le_iff.1 fun y _ => ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show φ y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [loc]; exact hi⟩
  obtain ⟨haff, r, hr, hsurj⟩ := hs i
  refine ⟨by rw [loc]; exact haff.preimage φ, fun j => (φ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hP (φ y)
    have hm : φ y ∈ nonzeroLocus (s i) ⊓ H.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs φ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j y l k hl hy.2
    have e₂ := hs' i y l k hl hy.2
    have e₃ := (Geo.Tor.gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE φ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · intro x
    refine closure_eq_top h haff (loc i) (RingHom.range _) (fun d => ?_) (fun c => ?_) x
    · obtain ⟨p, rfl⟩ := hsurj d
      refine ⟨MvPolynomial.map g p, ?_⟩
      rw [MvPolynomial.eval₂Hom_map_hom, MvPolynomial.map_eval₂Hom]
      exact congrArg (fun q => MvPolynomial.eval₂Hom q _ p) (RingHom.ext fun c => (appLE_cst h _ _ _ c).symm)
    · exact ⟨MvPolynomial.C c, MvPolynomial.eval₂Hom_C _ _ _⟩

end GlobalTheory.AbLaw.VeryAmplePull
