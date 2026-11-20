import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.VeryAmplePow

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

/- English proof (translation)
Introduce `z _` and use `(g z).2`.
-/
theorem le_pre {Y Z : Scheme.{0}} (D : Y.Opens) (g : Z ⟶ D.toScheme) : ⊤ ≤ (g ≫ D.ι) ⁻¹ᵁ D :=
  fun z _ => (g z).2

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem appLE_congr' {Y Z : Scheme.{0}} {g g' : Z ⟶ Y} (e : g = g') {U : Y.Opens} {V : Z.Opens} (h : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V h = g'.appLE U V (e ▸ h) := by subst e; rfl

/- English proof (translation)
Establish `e : D.topIso.inv ≫ g.appTop = (g ≫ D.ι).appLE D ⊤ (le_pre D g)`. Rewrite using `[← Scheme.Hom.appLE_comp_appLE g D.ι D ⊤ ⊤ (by simp) le_top]`. Use `congr 1`. Rewrite using `[Scheme.Opens.ι_appLE]`. Both sides reduce to the same expression.

Conclude with `Scheme.Hom.app_eq_appLE g`. Rewrite using `[Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, ← e]`. Simplify using `only [Category.assoc]`. Rewrite using `[Scheme.ΓSpecIso_naturality_assoc]`.
-/
theorem appTop_chart {Y Z : Scheme.{0}} (D : Y.Opens) {B : CommRingCat.{0}} (φ : B ⟶ Γ(Y, D))
    (g : Z ⟶ D.toScheme) :
    (g ≫ D.toSpecΓ ≫ Spec.map φ).appTop =
      (Scheme.ΓSpecIso B).hom ≫ φ ≫ (g ≫ D.ι).appLE D ⊤ (le_pre D g) := by
  have e : D.topIso.inv ≫ g.appTop = (g ≫ D.ι).appLE D ⊤ (le_pre D g) := by
    rw [← Scheme.Hom.appLE_comp_appLE g D.ι D ⊤ ⊤ (by simp) le_top]
    congr 1
    · rw [Scheme.Opens.ι_appLE]; rfl
    · exact Scheme.Hom.app_eq_appLE g
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, ← e]
  simp only [Category.assoc]
  rw [Scheme.ΓSpecIso_naturality_assoc]

/- English proof (translation)
Set `B : CommRingCat.{0}` to `.of (MvPolynomial σ Γ(W, ⊤))`. Set `φ : B ⟶ Γ(Y, D)` to `CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r)`. Set `c : Γ(W, ⊤) ⟶ B` to `CommRingCat.ofHom MvPolynomial.C`. Set `ψ : D.toScheme ⟶ Spec B` to `D.toSpecΓ ≫ Spec.map φ`. Set `π : Spec B ⟶ W` to `Spec.map c ≫ W.isoSpec.inv`.

Establish `hc : c ≫ φ = f.appLE ⊤ D hD`. Use extensionality with `a`. Conclude with `MvPolynomial.eval₂Hom_C _ _ a`. Establish `hπ : ψ ≫ π = D.ι ≫ f`. Simplify using `only [ψ, π, Category.assoc]`.

Rewrite using `[← Spec.map_comp_assoc, hc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Scheme.Opens.toSpecΓ_top, Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id, Scheme.Hom.resLE_comp_ι]`. Establish `hX : ∀ {Z : Scheme.{0}} (g : Z ⟶ D.toScheme) (j : σ), (g ≫ ψ).appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)) = ((g ≫ D.ι).appLE D ⊤ (le_pre D g)).hom (r j)`. Introduce `Z g j`. Rewrite using `[appTop_chart, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc, CommRingCat.comp_apply]`. Conclude with `congrArg _ (MvPolynomial.eval₂Hom_X' _ _ j)`.

Establish `: IsLocallyNoetherian Y` using `LocallyOfFiniteType.isLocallyNoetherian f`. Establish `: CompactSpace Y` using `QuasiCompact.compactSpace_of_compactSpace f`. Establish `: IsNoetherian Y` using `{}`. Establish `: CompactSpace D.toScheme` using `isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact (D : Set Y))`. Establish `: QuasiCompact ψ`.

Rewrite using `[quasiCompact_iff_compactSpace]` and apply the resulting hypothesis. Establish `: LocallyOfFiniteType (ψ ≫ π)` using `hπ ▸ inferInstance`. Establish `: LocallyOfFiniteType ψ` using `locallyOfFiniteType_of_comp ψ π`. Establish `: Mono ψ`. Establish `: IsLocallyNoetherian (pullback ψ ψ)` using `LocallyOfFiniteType.isLocallyNoetherian (pullback.fst ψ ψ)`.

Establish `e : pullback.fst ψ ψ = pullback.snd ψ ψ`. Rewrite using `[← cancel_mono D.ι]`. Use `hmono _ _ _ (le_pre D _) (le_pre D _) ?_ fun j => ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, ← hπ, pullback.condition_assoc]`. Rewrite using `[← hX, ← hX, pullback.condition]`.

Conclude with `⟨fun a b hab => by`. Rewrite using `[← pullback.lift_fst a b hab, e, pullback.lift_snd]⟩`. Establish `: UniversallyClosed ψ`. Use `UniversallyClosed.of_valuativeCriterion ψ fun S => ?_` and prove the remaining obligations. Establish `hf : ValuativeCriterion.Existence f` using `(UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) : (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1`.

Establish `w` using `S.commSq.w`. Take `⟨l, h₁, h₂⟩` from `(hf { R := S.R, K := S.K, i₁ := S.i₁ ≫ D.ι, i₂ := S.i₂ ≫ π, commSq := ⟨by`. Rewrite using `[Category.assoc, ← hπ, reassoc_of% w]⟩ }).exists_lift`. Simplify using `only at l h₁ h₂`. Establish `hl : ⊤ ≤ l ⁻¹ᵁ D`.

Use `hval S.R S.K l ((le_pre D S.i₁).trans_eq (by rw [h₁])) fun j => ⟨S.i₂.appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)), ?_⟩` and prove the remaining obligations. Use `hX S.i₁ j` as an intermediate fact. Rewrite `this` using `[w, Scheme.Hom.comp_appTop]`. Use `Eq.trans this ?_` and prove the remaining obligations. Rewrite using `[appLE_congr' h₁.symm]`.

Set `l' : Spec (.of S.R) ⟶ D.toScheme` to `IsOpenImmersion.lift D.ι l (by`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hl trivial)`. Establish `hl' : l' ≫ D.ι = l` using `IsOpenImmersion.lift_fac _ _ _`.

Establish `e₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' = S.i₁`. Rewrite using `[← cancel_mono D.ι, Category.assoc, hl', h₁]`. Use `⟨⟨l', e₁, ?_⟩⟩` and prove the remaining obligations. Establish `e₂ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂` using `by rw [← w, reassoc_of% e₁]`. Take `⟨a, ha⟩` from `Spec.map_surjective (l' ≫ ψ)`.

Take `⟨b, hb⟩` from `Spec.map_surjective S.i₂`. Rewrite `e₂` using `[← ha, ← hb, ← Spec.map_comp, ← Spec.map_comp]`. Establish `: Mono (CommRingCat.ofHom (algebraMap S.R S.K))` using `ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)`. Rewrite using `[← ha, ← hb, (cancel_mono _).1 (Spec.map_injective e₂)]`. Establish `: IsProper ψ` using `{}`.

Establish `: IsClosedImmersion ψ` using `(IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨inferInstance, inferInstance⟩`. Take `⟨h₁, h₂⟩` from `IsClosedImmersion.isAffine_surjective_of_isAffine ψ`. Use `⟨h₁, ?_⟩` and prove the remaining obligations. Establish `e : ψ.appTop = (Scheme.ΓSpecIso B).hom ≫ φ ≫ D.topIso.inv`. Rewrite using `[Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality_assoc]`.

Establish `e' : φ = (Scheme.ΓSpecIso B).inv ≫ ψ.appTop ≫ D.topIso.hom`. Rewrite using `[e, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]`. Express the relevant statement in the definitionally equal form `Function.Surjective φ.hom`. Rewrite using `[e', CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]`. Conclude with `((ConcreteCategory.bijective_of_isIso D.topIso.hom).2.comp h₂).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2`.
-/
theorem affine_surj {Y W : Scheme.{0}} (f : Y ⟶ W) [IsAffine W] [IsProper f] [IsLocallyNoetherian W]
    (D : Y.Opens) {σ : Type} (r : σ → Γ(Y, D)) (hD : D ≤ f ⁻¹ᵁ ⊤)
    (hval : ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
      (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ D),
      (∀ j, ∃ ρ : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom ρ =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE D ⊤ h).hom (r j)) → ⊤ ≤ l ⁻¹ᵁ D)
    (hmono : ∀ (Z : Scheme.{0}) [IsLocallyNoetherian Z] (x y : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ D) (hy : ⊤ ≤ y ⁻¹ᵁ D),
      x ≫ f = y ≫ f → (∀ j, (x.appLE D ⊤ hx).hom (r j) = (y.appLE D ⊤ hy).hom (r j)) → x = y) :
    IsAffineOpen D ∧ Function.Surjective (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r) := by
  let B : CommRingCat.{0} := .of (MvPolynomial σ Γ(W, ⊤))
  let φ : B ⟶ Γ(Y, D) := CommRingCat.ofHom (MvPolynomial.eval₂Hom (f.appLE ⊤ D hD).hom r)
  let c : Γ(W, ⊤) ⟶ B := CommRingCat.ofHom MvPolynomial.C
  let ψ : D.toScheme ⟶ Spec B := D.toSpecΓ ≫ Spec.map φ
  let π : Spec B ⟶ W := Spec.map c ≫ W.isoSpec.inv
  have hc : c ≫ φ = f.appLE ⊤ D hD := by
    ext a; exact MvPolynomial.eval₂Hom_C _ _ a
  have hπ : ψ ≫ π = D.ι ≫ f := by
    simp only [ψ, π, Category.assoc]
    rw [← Spec.map_comp_assoc, hc, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Scheme.Opens.toSpecΓ_top,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id, Scheme.Hom.resLE_comp_ι]
  have hX : ∀ {Z : Scheme.{0}} (g : Z ⟶ D.toScheme) (j : σ),
      (g ≫ ψ).appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)) =
        ((g ≫ D.ι).appLE D ⊤ (le_pre D g)).hom (r j) := by
    intro Z g j
    rw [appTop_chart, ← CommRingCat.comp_apply, Iso.inv_hom_id_assoc, CommRingCat.comp_apply]
    exact congrArg _ (MvPolynomial.eval₂Hom_X' _ _ j)
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian Y := {}
  have : CompactSpace D.toScheme := isCompact_iff_compactSpace.1 (NoetherianSpace.isCompact (D : Set Y))
  have : QuasiCompact ψ := by
    rwa [quasiCompact_iff_compactSpace]
  have : LocallyOfFiniteType (ψ ≫ π) := hπ ▸ inferInstance
  have : LocallyOfFiniteType ψ := locallyOfFiniteType_of_comp ψ π
  have : Mono ψ := by
    have : IsLocallyNoetherian (pullback ψ ψ) := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst ψ ψ)
    have e : pullback.fst ψ ψ = pullback.snd ψ ψ := by
      rw [← cancel_mono D.ι]
      refine hmono _ _ _ (le_pre D _) (le_pre D _) ?_ fun j => ?_
      · rw [Category.assoc, Category.assoc, ← hπ, pullback.condition_assoc]
      · rw [← hX, ← hX, pullback.condition]
    exact ⟨fun a b hab => by
      rw [← pullback.lift_fst a b hab, e, pullback.lift_snd]⟩
  have : UniversallyClosed ψ := by
    refine UniversallyClosed.of_valuativeCriterion ψ fun S => ?_
    have hf : ValuativeCriterion.Existence f :=
      (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
        (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
    have w := S.commSq.w
    obtain ⟨l, h₁, h₂⟩ := (hf { R := S.R, K := S.K, i₁ := S.i₁ ≫ D.ι, i₂ := S.i₂ ≫ π, commSq := ⟨by
      rw [Category.assoc, ← hπ, reassoc_of% w]⟩ }).exists_lift
    dsimp only at l h₁ h₂
    have hl : ⊤ ≤ l ⁻¹ᵁ D := by
      refine hval S.R S.K l ((le_pre D S.i₁).trans_eq (by rw [h₁])) fun j =>
        ⟨S.i₂.appTop.hom ((Scheme.ΓSpecIso B).inv.hom (MvPolynomial.X j)), ?_⟩
      have := hX S.i₁ j
      rw [w, Scheme.Hom.comp_appTop] at this
      refine Eq.trans this ?_
      rw [appLE_congr' h₁.symm]
    let l' : Spec (.of S.R) ⟶ D.toScheme := IsOpenImmersion.lift D.ι l (by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hl trivial)
    have hl' : l' ≫ D.ι = l := IsOpenImmersion.lift_fac _ _ _
    have e₁ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' = S.i₁ := by
      rw [← cancel_mono D.ι, Category.assoc, hl', h₁]
    refine ⟨⟨l', e₁, ?_⟩⟩
    have e₂ : Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ l' ≫ ψ =
        Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) ≫ S.i₂ := by rw [← w, reassoc_of% e₁]
    obtain ⟨a, ha⟩ := Spec.map_surjective (l' ≫ ψ)
    obtain ⟨b, hb⟩ := Spec.map_surjective S.i₂
    rw [← ha, ← hb, ← Spec.map_comp, ← Spec.map_comp] at e₂
    have : Mono (CommRingCat.ofHom (algebraMap S.R S.K)) :=
      ConcreteCategory.mono_of_injective _ (IsFractionRing.injective S.R S.K)
    rw [← ha, ← hb, (cancel_mono _).1 (Spec.map_injective e₂)]
  have : IsProper ψ := {}
  have : IsClosedImmersion ψ := (IsClosedImmersion.iff_isProper_and_mono ψ).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨h₁, h₂⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ψ
  refine ⟨h₁, ?_⟩
  have e : ψ.appTop = (Scheme.ΓSpecIso B).hom ≫ φ ≫ D.topIso.inv := by
    rw [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality_assoc]
  have e' : φ = (Scheme.ΓSpecIso B).inv ≫ ψ.appTop ≫ D.topIso.hom := by
    rw [e, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
  change Function.Surjective φ.hom
  rw [e', CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
  exact ((ConcreteCategory.bijective_of_isIso D.topIso.hom).2.comp h₂).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso B).inv).2

/- English proof (translation)
Rewrite using `[gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]`. Both sides reduce to the same expression.
-/
theorem isUnit_gs {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.mem_basicOpen Z _ z h, ← Scheme.preimage_basicOpen]
  rfl

/- English proof (translation)
The claim follows from `(gs_res q z hle h _).trans (gs_pull q r z U (hle h) a)`.
-/
theorem gs_appLE {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (r : Z ⟶ Y) (z : Z') (U : Y.Opens) (V : Z.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : q z ∈ V) (a : Γ(Y, U)) :
    gs q z V ((r.appLE U V hle).hom a) = gs (q ≫ r) z U a :=
  (gs_res q z hle h _).trans (gs_pull q r z U (hle h) a)

/- English proof (translation)
The claim follows from `gs_pull q r z ⊤ trivial a`.
-/
theorem gs_appTop {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (r : Z ⟶ Y) (z : Z') (a : Γ(Y, ⊤)) :
    gs q z ⊤ (r.appTop.hom a) = gs (q ≫ r) z ⊤ a := gs_pull q r z ⊤ trivial a

/- English proof (translation)
Simplify using `only [gs_eq r z U h, map_sum]`.
-/
theorem gs_sum {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) {I : Type} [Fintype I]
    (a : I → Γ(Y, U)) : gs r z U (∑ i, a i) = ∑ i, gs r z U (a i) := by simp only [gs_eq r z U h, map_sum]

/- English proof (translation)
Establish `hm : r z ∈ M.U j ⊓ M.U j'` using `⟨hj, hj'⟩`. Conclude with `(gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))`.
-/
theorem sec_trans' {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z _ (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

/- English proof (translation)
Use `⟨fun h => Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩, fun h => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 h`. Establish `hk' : r z ∈ M.U k` using `Y.basicOpen_le _ hk`. Rewrite using `[sec_trans' s r z hj hk']`. Conclude with `(Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)`.
-/
theorem isUnit_iff_mem {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j : M.ι}
    (hj : r z ∈ M.U j) : IsUnit (gs r z (M.U j) (s.f j)) ↔ r z ∈ nonzeroLocus s := by
  refine ⟨fun h => Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩, fun h => ?_⟩
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 h
  have hk' : r z ∈ M.U k := Y.basicOpen_le _ hk
  rw [sec_trans' s r z hj hk']
  exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

/- English proof (translation)
Set `V : M.ι → Y.Opens` to `fun k => Y.basicOpen (s.f k)`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : ∀ k, Γ(Y, V k), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ V k → gs r z _ (t.f k) = gs r z _ (u k) * gs r z _ (s.f k) := by`. Establish `hs : ∀ k, IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k) : V k ≤ M.U k)).op).hom (s.f k))` using `fun k => Y.toRingedSpace.isUnit_res_basicOpen (s.f k)`. Use `choose w hw using fun k => (hs k).exists_left_inv`. Use `⟨fun k => (Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k))).op).hom (t.f k) * w k, fun Z r z k hz => ?_⟩` and prove the remaining obligations.

Establish `e` using `congrArg (gs r z (V k)) (hw k)`. Establish `e' : gs r z (V k) (w k) * gs r z _ (s.f k) = 1`. Use `Eq.trans ?_ (e.trans (by rw [gs_eq r z _ hz, map_one, map_one]))` and prove the remaining obligations. Conclude with `((gs_mul r z _ hz _ _).trans (congrArg _ (gs_res r z (Y.basicOpen_le (s.f k)) hz _))).symm`. Rewrite using `[gs_mul r z _ hz, gs_res r z _ hz, _root_.mul_assoc, e', _root_.mul_one]`.

Take `⟨a, ha, -⟩` from `Y.sheaf.existsUnique_gluing' V (nonzeroLocus s) (fun k => homOfLE (le_iSup V k)) le_rfl u (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by`. Use `(gs_res (𝟙 Y) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)` and prove the remaining obligations. Establish `h₁ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j` using `Y.basicOpen_le _ hz.1`. Establish `h₂ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j'` using `Y.basicOpen_le _ hz.2`. Establish `e₁` using `hu _ (𝟙 Y) z j hz.1`.

Rewrite `e₁` using `[sec_trans' t _ z h₁ h₂, sec_trans' s _ z h₁ h₂, hu _ (𝟙 Y) z j' hz.2, mul_left_comm (gs _ _ _ (u j)), Units.mul_right_inj]`. Conclude with `(((isUnit_gs (𝟙 Y) z _ h₂ _).2 hz.2).mul_left_inj.1 e₁).symm)`. Use `⟨a, fun Z r z k h hk => ?_⟩` and prove the remaining obligations. Establish `hz : r z ∈ V k` using `(isUnit_gs r z _ hk _).1 ((isUnit_iff_mem s r z hk).2 h)`. Rewrite using `[hu Z r z k hz, ← ha k]`.

Conclude with `congrArg (· * _) (gs_res r z (le_iSup V k) hz a)`.
-/
theorem exists_ratio {Y : Scheme.{0}} {M : LB Y} (s t : LB.Sec M) :
    ∃ ρ : Γ(Y, nonzeroLocus s), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus s → r z ∈ M.U k →
      gs r z _ (t.f k) = gs r z _ ρ * gs r z _ (s.f k) := by
  let V : M.ι → Y.Opens := fun k => Y.basicOpen (s.f k)
  obtain ⟨u, hu⟩ : ∃ u : ∀ k, Γ(Y, V k), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ V k →
      gs r z _ (t.f k) = gs r z _ (u k) * gs r z _ (s.f k) := by
    have hs : ∀ k, IsUnit ((Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k) : V k ≤ M.U k)).op).hom (s.f k)) :=
      fun k => Y.toRingedSpace.isUnit_res_basicOpen (s.f k)
    choose w hw using fun k => (hs k).exists_left_inv
    refine ⟨fun k => (Y.presheaf.map (homOfLE (Y.basicOpen_le (s.f k))).op).hom (t.f k) * w k, fun Z r z k hz => ?_⟩
    have e := congrArg (gs r z (V k)) (hw k)
    have e' : gs r z (V k) (w k) * gs r z _ (s.f k) = 1 := by
      refine Eq.trans ?_ (e.trans (by rw [gs_eq r z _ hz, map_one, map_one]))
      exact ((gs_mul r z _ hz _ _).trans (congrArg _ (gs_res r z (Y.basicOpen_le (s.f k)) hz _))).symm
    rw [gs_mul r z _ hz, gs_res r z _ hz, _root_.mul_assoc, e', _root_.mul_one]
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' V (nonzeroLocus s) (fun k => homOfLE (le_iSup V k)) le_rfl u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Y) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Y) z inf_le_right hz _).symm)
      have h₁ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j := Y.basicOpen_le _ hz.1
      have h₂ : (𝟙 Y : Y ⟶ Y) z ∈ M.U j' := Y.basicOpen_le _ hz.2
      have e₁ := hu _ (𝟙 Y) z j hz.1
      rw [sec_trans' t _ z h₁ h₂, sec_trans' s _ z h₁ h₂, hu _ (𝟙 Y) z j' hz.2, mul_left_comm (gs _ _ _ (u j)),
        Units.mul_right_inj] at e₁
      exact (((isUnit_gs (𝟙 Y) z _ h₂ _).2 hz.2).mul_left_inj.1 e₁).symm)
  refine ⟨a, fun Z r z k h hk => ?_⟩
  have hz : r z ∈ V k := (isUnit_gs r z _ hk _).1 ((isUnit_iff_mem s r z hk).2 h)
  rw [hu Z r z k hz, ← ha k]
  exact congrArg (· * _) (gs_res r z (le_iSup V k) hz a)

/- English proof (translation)
Set `q : Spec (.of K) ⟶ Spec (.of V)` to `Spec.map (CommRingCat.ofHom (algebraMap V K))`. Set `p : Spec (.of V)` to `IsLocalRing.closedPoint V`. Take `⟨k, hk⟩` from `Opens.mem_iSup.1 (show l p ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)`. Take `⟨c, hc⟩` from `Opens.mem_iSup.1 hk`. Establish `hc' : l p ∈ M.U c` using `Y.basicOpen_le _ hc`.

Establish `ht : ⊤ ≤ l ⁻¹ᵁ M.U c` using `(Scheme.preimage_eq_top_of_closedPoint_mem l hc').ge`. Establish `inj : Function.Injective q.appTop.hom`. Establish `e : q.appTop = (Scheme.ΓSpecIso (.of V)).hom ≫ CommRingCat.ofHom (algebraMap V K) ≫ (Scheme.ΓSpecIso (.of K)).inv`. Rewrite using `[← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]`.

Conclude with `((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1.comp (IsFractionRing.injective V K)).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).hom).1`. Take `⟨a, ha⟩` from `H k`. Use `replace ha : q.appTop.hom a = ((q ≫ l).appLE _ ⊤ h).hom (ρ k) := ha`. Establish `e : (l.appLE _ ⊤ ht).hom ((s k).f c) = a * (l.appLE _ ⊤ ht).hom ((s i).f c)`. Use `inj (fn_ext fun z _ => ?_)` and prove the remaining obligations.

Rewrite using `[map_mul, ha, gs_mul _ z ⊤ trivial, gs_appTop, gs_appTop, gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial]`. Simplify using `only [Category.id_comp]`. Conclude with `hρ k _ (q ≫ l) z c (h trivial) (ht trivial)`. Establish `e'` using `congrArg (gs (𝟙 _) p ⊤) e`. Rewrite `e'` using `[gs_mul _ p ⊤ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, Category.id_comp]`.

Establish `u` using `(isUnit_gs l p _ hc' _).2 hc`. Rewrite `u` using `[e']`. Conclude with `(Scheme.preimage_eq_top_of_closedPoint_mem l ((isUnit_iff_mem (s i) l p hc').1 (isUnit_of_mul_isUnit_right u))).ge`.
-/
theorem valuative {Y : Scheme.{0}} {M : LB Y} {I : Type} (s : I → LB.Sec M) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (i : I) (ρ : I → Γ(Y, nonzeroLocus (s i)))
    (hρ : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus (s i) → r z ∈ M.U k →
      gs r z _ ((s j).f k) = gs r z _ (ρ j) * gs r z _ ((s i).f k))
    (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K]
    (l : Spec (.of V) ⟶ Y) (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) ⁻¹ᵁ nonzeroLocus (s i))
    (H : ∀ j, ∃ a : Γ(Spec (.of V), ⊤), (Spec.map (CommRingCat.ofHom (algebraMap V K))).appTop.hom a =
        ((Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l).appLE _ ⊤ h).hom (ρ j)) :
    ⊤ ≤ l ⁻¹ᵁ nonzeroLocus (s i) := by
  let q : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  let p : Spec (.of V) := IsLocalRing.closedPoint V
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show l p ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  obtain ⟨c, hc⟩ := Opens.mem_iSup.1 hk
  have hc' : l p ∈ M.U c := Y.basicOpen_le _ hc
  have ht : ⊤ ≤ l ⁻¹ᵁ M.U c := (Scheme.preimage_eq_top_of_closedPoint_mem l hc').ge
  have inj : Function.Injective q.appTop.hom := by
    have e : q.appTop = (Scheme.ΓSpecIso (.of V)).hom ≫ CommRingCat.ofHom (algebraMap V K) ≫
        (Scheme.ΓSpecIso (.of K)).inv := by
      rw [← Scheme.ΓSpecIso_naturality_assoc, Iso.hom_inv_id, Category.comp_id]
    rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp, RingHom.coe_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).1.comp
      (IsFractionRing.injective V K)).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of V)).hom).1
  obtain ⟨a, ha⟩ := H k
  replace ha : q.appTop.hom a = ((q ≫ l).appLE _ ⊤ h).hom (ρ k) := ha
  have e : (l.appLE _ ⊤ ht).hom ((s k).f c) = a * (l.appLE _ ⊤ ht).hom ((s i).f c) := by
    refine inj (fn_ext fun z _ => ?_)
    rw [map_mul, ha, gs_mul _ z ⊤ trivial, gs_appTop, gs_appTop, gs_appLE _ _ _ _ ⊤ _ trivial,
      gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial]
    simp only [Category.id_comp]
    exact hρ k _ (q ≫ l) z c (h trivial) (ht trivial)
  have e' := congrArg (gs (𝟙 _) p ⊤) e
  rw [gs_mul _ p ⊤ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, gs_appLE _ _ _ _ ⊤ _ trivial, Category.id_comp] at e'
  have u := (isUnit_gs l p _ hc' _).2 hc
  rw [e'] at u
  exact (Scheme.preimage_eq_top_of_closedPoint_mem l
    ((isUnit_iff_mem (s i) l p hc').1 (isUnit_of_mul_isUnit_right u))).ge

/- English proof (translation)
Take `rfl : φ' = fun k => h ≫ φ k` from `funext e`. Conclude with `⟨H1.SectionArithmetic.pullSec s h, fun _ _ => rfl, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩`.
-/
theorem exists_pull {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, φ' k = h ≫ φ k) :
    ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (l : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE l).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) J, Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext e
  exact ⟨H1.SectionArithmetic.pullSec s h, fun _ _ => rfl, fun Z r z J hJ => H1.SectionArithmetic.sval_pullSec s h r z hJ⟩

/- English proof (translation)
The claim follows from `isUnit_iff_mem (M := LB.LinComb L φ ε) s r z (hJ.mem φ r)`.
-/
theorem isUnit_sval {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s :=
  isUnit_iff_mem (M := LB.LinComb L φ ε) s r z (hJ.mem φ r)

/- English proof (translation)
Introduce `U _ h`. Simplify using `[e]`.
-/
theorem formEq_pow {X Y : Scheme.{0}} (a b : Y ⟶ X) (e : a = b) (n : ℕ) :
    FormEq (K := Fin 1) (K' := Fin n) (fun _ => a) (fun _ => (n : ℤ)) (fun _ => b) (fun _ => 1) := by
  intro U _ h
  simp [e]

/- English proof (translation)
Take `⟨t, ht⟩` from `exists_sec hL (fun U _ h => (formEq_pow x' (x ≫ w) e n U h).symm) (H1.SectionArithmetic.pullSec s x)`. Establish `ht' : ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → sval t r z J = sval s (r ≫ x) z J` using `fun Z' r z J hJ => (ht Z' r z J hJ).trans (H1.SectionArithmetic.sval_pullSec s x r z hJ)`. Establish `hu : ∀ j, IsUnit (t.f j)` using `fun j => Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by`. Take `⟨J, hJ, e⟩` from `sval_trans hL t y j hy`. Rewrite `e` using `[ht' _ _ y J hJ]`.

Use `(congrArg IsUnit ((gs_eq (𝟙 Z) y _ hy _).symm.trans e)).mpr ((Units.isUnit _).mul ?_)` and prove the remaining obligations. Conclude with `(isUnit_sval s _ y hJ).2 (hx trivial)`. Conclude with `⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (t.compat i j), fun Z' r z J hJ => (gs_unit r z _ (hJ.mem _ r) _).symm.trans (ht' Z' r z J hJ)⟩`.
-/
theorem exists_frame {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (w : Y ⟶ X) (n : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin n) (fun _ => w) (fun _ => 1))) (x : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus s)
    (x' : Z ⟶ X) (e : x' = x ≫ w) :
    ∃ τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => x') (fun _ => (n : ℤ))), τ.IsGen ∧
      ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → (val τ r z J).val = sval s (r ≫ x) z J := by
  obtain ⟨t, ht⟩ := exists_sec hL (fun U _ h => (formEq_pow x' (x ≫ w) e n U h).symm) (H1.SectionArithmetic.pullSec s x)
  have ht' : ∀ (Z' : Scheme.{0}) (r : Z' ⟶ Z) (z : Z') J, Good L z J → sval t r z J = sval s (r ≫ x) z J :=
    fun Z' r z J hJ => (ht Z' r z J hJ).trans (H1.SectionArithmetic.sval_pullSec s x r z hJ)
  have hu : ∀ j, IsUnit (t.f j) := fun j => Z.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    obtain ⟨J, hJ, e⟩ := sval_trans hL t y j hy
    rw [ht' _ _ y J hJ] at e
    refine (congrArg IsUnit ((gs_eq (𝟙 Z) y _ hy _).symm.trans e)).mpr ((Units.isUnit _).mul ?_)
    exact (isUnit_sval s _ y hJ).2 (hx trivial)
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (t.compat i j), fun Z' r z J hJ =>
    (gs_unit r z _ (hJ.mem _ r) _).symm.trans (ht' Z' r z J hJ)⟩

section

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}

/- English proof (translation)
Establish `e : (ptSecT A x).left ≫ (snd T A).left = x.left` using `by rw [← Over.comp_left, ptSecT, lift_snd]`. Use `(sval_of _ _ z J (fun _ => J x.left) (fun _ => by rw [e])).trans ?_` and prove the remaining obligations. Rewrite using `[val_of τ _ z J (fun _ => J x.left) (fun _ => by rw [Category.id_comp])]`. Establish `hm : (𝟙 T.left : T.left ⟶ T.left) z ∈ LB.wchart L (fun _ : Fin 1 => x.left) (fun _ => J x.left)` using `Set.mem_iInter.2 fun _ => hJ x.left`. Use `congrArg (gs (𝟙 _) z _) (h fun _ => J x.left)` as an intermediate fact.

Rewrite `this` using `[gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm]`. Use `Eq.trans ?_ (this.trans (congrArg _ (gs_unit _ z _ hm _)))` and prove the remaining obligations. Conclude with `((gs_pull (𝟙 _) (ptSecT A x).left z _ (val_le A L x _ hm) _).trans (by rw [Category.id_comp])).symm`.
-/
theorem value_sval {a : ℤ} {T : Over S} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (h : IsValueAt A L a s x τ v) (z : T.left) {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (ptSecT A x).left z J =
      gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val := by
  have e : (ptSecT A x).left ≫ (snd T A).left = x.left := by rw [← Over.comp_left, ptSecT, lift_snd]
  refine (sval_of _ _ z J (fun _ => J x.left) (fun _ => by rw [e])).trans ?_
  rw [val_of τ _ z J (fun _ => J x.left) (fun _ => by rw [Category.id_comp])]
  have hm : (𝟙 T.left : T.left ⟶ T.left) z ∈ LB.wchart L (fun _ : Fin 1 => x.left) (fun _ => J x.left) :=
    Set.mem_iInter.2 fun _ => hJ x.left
  have := congrArg (gs (𝟙 _) z _) (h fun _ => J x.left)
  rw [gs_res _ z _ hm, gs_mul _ z _ hm, gs_res _ z _ hm] at this
  refine Eq.trans ?_ (this.trans (congrArg _ (gs_unit _ z _ hm _)))
  exact ((gs_pull (𝟙 _) (ptSecT A x).left z _ (val_le A L x _ hm) _).trans (by rw [Category.id_comp])).symm

/- English proof (translation)
Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 (show SecM.ofSec A s ∈ _ from hb ▸ Submodule.mem_top)`. Establish `hc' : ∀ j, s.f j = ∑ i, liftHom A _ (c i) * (b i).f j` using `fun j => by`. Use `congrArg (fun x : SecM A L a T => x.1 j) hc` as an intermediate fact. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply] at this`. Conclude with `this.symm`.

Use `⟨c, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Establish `hm` using `hJ.mem (fun _ : Fin 1 => (snd T A).left) r`. Use `(congrArg (gs r z _) (hc' _)).trans ((gs_sum r z _ hm _).trans (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Conclude with `(gs_mul r z _ hm _ _).trans (congrArg (· * _) ((gs_res r z le_top hm _).trans (gs_appTop r _ z _)))`.
-/
theorem span_sval {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T))
    (hb : Submodule.span Γ(T.left, ⊤) (Set.range fun i => (SecM.ofSec A (b i) : SecM A L a T)) = ⊤)
    (s : LB.Sec (LPow A L a T)) : ∃ c : I → Γ(T.left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J,
      Good L z J → sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s r z J =
        ∑ i, gs (r ≫ (fst T A).left) z ⊤ (c i) *
          sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) r z J := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (show SecM.ofSec A s ∈ _ from hb ▸ Submodule.mem_top)
  have hc' : ∀ j, s.f j = ∑ i, liftHom A _ (c i) * (b i).f j := fun j => by
    have := congrArg (fun x : SecM A L a T => x.1 j) hc
    simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply] at this
    exact this.symm
  refine ⟨c, fun Z r z J hJ => ?_⟩
  have hm := hJ.mem (fun _ : Fin 1 => (snd T A).left) r
  refine (congrArg (gs r z _) (hc' _)).trans ((gs_sum r z _ hm _).trans (Finset.sum_congr rfl fun i _ => ?_))
  exact (gs_mul r z _ hm _ _).trans (congrArg (· * _) ((gs_res r z le_top hm _).trans (gs_appTop r _ z _)))

/- English proof (translation)
Use `choose b' h₁ h₂ using fun i => exists_pull (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) (h ▷ A).left (fun _ => (snd T' A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])`. Take `⟨c, hc⟩` from `span_sval A b' (hb b' fun i j => h₁ i j _) s`. Use `⟨c, fun x g e₁ e₂ τ v hv z J hJ => ?_⟩` and prove the remaining obligations. Establish `k₁ : (ptSecT A x).left ≫ (fst T' A).left = 𝟙 _` using `by rw [← Over.comp_left, ptSecT, lift_fst]; rfl`. Establish `k₂ : (ptSecT A x).left ≫ (h ▷ A).left = g`.

Use `pullback.hom_ext (f := T.hom) (g := A.hom) (Eq.trans ?_ e₁.symm) (Eq.trans ?_ e₂.symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(ptSecT A x ≫ h ▷ A ≫ fst T A).left = _`. Rewrite using `[whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]`. Express the relevant statement in the definitionally equal form `(ptSecT A x ≫ h ▷ A ≫ snd T A).left = _`. Rewrite using `[whiskerRight_snd, ptSecT, lift_snd]`.

Rewrite using `[← value_sval A hv z hJ, hc _ _ z J hJ, k₁]`. Conclude with `Finset.sum_congr rfl fun i _ => congrArg _ ((h₂ i _ _ z J hJ).trans (by rw [k₂]))`.
-/
theorem key {a : ℤ} {T : Over S} {I : Type} [Fintype I] (b : I → LB.Sec (LPow A L a T)) (T' : Over S) (h : T' ⟶ T)
    (hb : ∀ b' : I → LB.Sec (LPow A L a T'), (∀ i, IsPullSec A L a (h ▷ A) (whiskerRight_snd h A) (b i) (b' i)) →
      Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec A (b' i) : SecM A L a T')) = ⊤)
    (s : LB.Sec (LPow A L a T')) : ∃ c : I → Γ(T'.left, ⊤), ∀ (x : T' ⟶ A) (g : T'.left ⟶ (T ⊗ A).left),
      g ≫ (fst T A).left = h.left → g ≫ (snd T A).left = x.left →
      ∀ (τ : LB.Gen (LB.LinComb L (Y := T'.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))) (v : Γ(T'.left, ⊤)),
      IsValueAt A L a s x τ v → ∀ z J, Good L z J → gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val =
        ∑ i, gs (𝟙 _) z ⊤ (c i) * sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i) g z J := by
  choose b' h₁ h₂ using fun i => exists_pull (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (b i)
    (h ▷ A).left (fun _ => (snd T' A).left) (fun _ => by rw [← Over.comp_left, whiskerRight_snd])
  obtain ⟨c, hc⟩ := span_sval A b' (hb b' fun i j => h₁ i j _) s
  refine ⟨c, fun x g e₁ e₂ τ v hv z J hJ => ?_⟩
  have k₁ : (ptSecT A x).left ≫ (fst T' A).left = 𝟙 _ := by rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have k₂ : (ptSecT A x).left ≫ (h ▷ A).left = g := by
    refine pullback.hom_ext (f := T.hom) (g := A.hom) (Eq.trans ?_ e₁.symm) (Eq.trans ?_ e₂.symm)
    · change (ptSecT A x ≫ h ▷ A ≫ fst T A).left = _
      rw [whiskerRight_fst, ptSecT, lift_fst_assoc, Category.id_comp]
    · change (ptSecT A x ≫ h ▷ A ≫ snd T A).left = _
      rw [whiskerRight_snd, ptSecT, lift_snd]
  rw [← value_sval A hv z hJ, hc _ _ z J hJ, k₁]
  exact Finset.sum_congr rfl fun i _ => congrArg _ ((h₂ i _ _ z J hJ).trans (by rw [k₂]))

end

/- English proof (translation)
Introduce `hS hG hM S _ P n hn`. It suffices to establish `H : VeryAmpleAt P.A P.L n from ⟨fun U hU => by obtain ⟨m, s, h, -⟩` using `H U hU; exact ⟨m, s, h⟩, H⟩`. Introduce `U hU`. Take `⟨m, b, hb⟩` from `hS S P n (by omega) U hU`. Establish `hL` using `P.isLB`.

Establish `: IsProper P.A.hom` using `P.isAb.proper`. Establish `: IsAffine U.toScheme` using `hU`. Set `T : Over S` to `overRes (T := baseOver S) U`. Set `Y : Scheme.{0}` to `(P.A.hom ⁻¹ᵁ U).toScheme`. Set `w : Y ⟶ P.A.left` to `(P.A.hom ⁻¹ᵁ U).ι`.

Set `f : Y ⟶ U.toScheme` to `P.A.hom ∣_ U`. Establish `hf : f ≫ T.hom = w ≫ P.A.hom`. Express the relevant statement in the definitionally equal form `f ≫ U.ι ≫ 𝟙 S = _`. Rewrite using `[Category.comp_id]`. Conclude with `morphismRestrict_ι _ _`.

Take `⟨e, e₁, e₂⟩ : ∃ e : Y ⟶ (T ⊗ P.A).left, e ≫ (fst T P.A).left = f ∧ e ≫ (snd T P.A).left = w` from `⟨pullback.lift f w hf, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩`. Establish `hs : ∀ i, ∃ s : LB.Sec (LB.LinComb P.L (K` using `Fin n) (fun _ => w) (fun _ => 1)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good P.L z J → sval s r z J = sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (n : ℤ)) (b i) (r ≫ e) z J := fun i => by`. Take `⟨s, hs⟩` from `exists_sec hL (formEq_pow _ w e₂ n) (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (n : ℤ)) (b i) e)`. Conclude with `⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ e r z hJ)⟩`. Use `choose s hs using hs`.

Establish `key' : ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T) (σ : LB.Sec (LPow P.A P.L n T')), ∃ c : Fin (m + 1) → Γ(T'.left, ⊤), ∀ (x : T' ⟶ P.A) (g : T'.left ⟶ Y), g ≫ f = h.left → g ≫ w = x.left → ∀ (τ : LB.Gen (LB.LinComb P.L (Y` using `T'.left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ(T'.left, ⊤)), IsValueAt P.A P.L n σ x τ v → ∀ z J, Good P.L z J → gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val = ∑ i, gs (𝟙 _) z ⊤ (c i) * sval (s i) g z J := by`. Introduce `T' _ h σ`. Take `⟨c, hc⟩` from `key P.A b T' h (hb T' h) σ`. Use `⟨c, fun x g a₁ a₂ τ v hv z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[hc x (g ≫ e) (by rw [Category.assoc, e₁, a₁]) (by rw [Category.assoc, e₂, a₂]) τ v hv z J hJ]`.

Conclude with `Finset.sum_congr rfl fun i _ => by rw [hs i _ g z J hJ]`. Establish `hcov : ⨆ i, nonzeroLocus (s i) = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Set `K` to `AlgebraicClosure (Y.residueField y)`. Set `g : Spec (.of K) ⟶ Y` to `Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y`.

Set `z : Spec (.of K)` to `IsLocalRing.closedPoint K`. Establish `hz : g z = y` using `Scheme.fromSpecResidueField_apply y _`. Set `x : Over.mk (g ≫ w ≫ P.A.hom) ⟶ P.A` to `Over.homMk (g ≫ w) (Category.assoc _ _ _)`. Take `⟨σ, τ, v, -, hv, hu⟩` from `hG S P K (g ≫ w ≫ P.A.hom) n (by omega) x`. Establish `: IsAffine (Over.mk (g ≫ w ≫ P.A.hom)).left` using `inferInstanceAs (IsAffine (Spec (.of K)))`.

Take `⟨c, hc⟩` from `key' (Over.mk (g ≫ w ≫ P.A.hom)) (Over.homMk (g ≫ f) (by`. Express the relevant statement in the definitionally equal form `(g ≫ f) ≫ T.hom = g ≫ w ≫ P.A.hom`. Rewrite using `[Category.assoc, hf])) σ`. Use `choose J hJ using fun χ : Spec (.of K) ⟶ P.A.left => exists_chart hL (χ z)`. Establish `k` using `hc x g rfl rfl τ v hv z J hJ`.

Establish `u : IsUnit (gs (𝟙 (Over.mk (g ≫ w ≫ P.A.hom)).left) z ⊤ v)`. Rewrite using `[gs_eq _ _ ⊤ trivial]`. Conclude with `(hu.map _).map _`. Take `⟨i, -, hi⟩` from `IsLocalRing.exists_of_isUnit_sum (k ▸ u.mul (Units.isUnit _))`. Conclude with `Opens.mem_iSup.2 ⟨i, hz ▸ (isUnit_sval (s i) g z hJ).1 (isUnit_of_mul_isUnit_right hi)⟩`.

Use `⟨m, s, hcov, fun i => ?_⟩` and prove the remaining obligations. Use `choose ρ hρ using fun j => exists_ratio (s i) (s j)`. Use `affine_surj f (nonzeroLocus (s i)) ρ le_top (valuative s hcov i ρ hρ) ?_` as an intermediate fact. Use `⟨this.1, ρ, fun j k => fn_ext fun y hy => ?_, this.2⟩` and prove the remaining obligations. Conclude with `(gs_res _ y _ hy _).trans ((hρ j _ (𝟙 Y) y k hy.1 hy.2).trans ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _))).symm)`.

Introduce `Z _ x y hx hy hxy hr`. Set `Z' : Over S` to `Over.mk (x ≫ w ≫ P.A.hom)`. Set `x' : Z' ⟶ P.A` to `Over.homMk (x ≫ w) (Category.assoc _ _ _)`. Set `y' : Z' ⟶ P.A` to `Over.homMk (y ≫ w) (by`. Express the relevant statement in the definitionally equal form `(y ≫ w) ≫ P.A.hom = x ≫ w ≫ P.A.hom`.

Rewrite using `[Category.assoc, ← hf, reassoc_of% hxy])`. Set `q : Z' ⟶ T` to `Over.homMk (x ≫ f) (by`. Express the relevant statement in the definitionally equal form `(x ≫ f) ≫ T.hom = x ≫ w ≫ P.A.hom`. Rewrite using `[Category.assoc, hf])`. Take `⟨τx, gx, hτx⟩` from `exists_frame hL w n (s i) x hx x'.left rfl`.

Take `⟨τy, gy, hτy⟩` from `exists_frame hL w n (s i) y hy y'.left rfl`. Establish `: IsLocallyNoetherian Z'.left` using `inferInstanceAs (IsLocallyNoetherian Z)`. Establish `E` using `hM S P n (by omega) Z' x' y' τx τy gx gy fun T' _ h σ vx vy hvx hvy => by`. Take `⟨c, hc⟩` from `key' T' (h ≫ q) σ`. Use `fn_ext fun z _ => ?_` and prove the remaining obligations.

Use `choose J hJ using fun χ : T'.left ⟶ P.A.left => exists_chart hL (χ z)`. Establish `aux : ∀ (x : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s i)) (v u : T'.left.presheaf.stalk z), u = sval (s i) (h.left ≫ x) z J → v * u = ∑ j, gs (𝟙 _) z ⊤ (c j) * sval (s j) (h.left ≫ x) z J → v = ∑ j, gs (𝟙 _) z ⊤ (c j) * gs h.left z ⊤ ((x.appLE _ ⊤ hx).hom (ρ j))`. Introduce and unpack `x hx v _ rfl hv`. Establish `hm : (h.left ≫ x) z ∈ nonzeroLocus (s i)` using `hx trivial`. Use `((isUnit_sval (s i) (h.left ≫ x) z hJ).2 hm).mul_left_inj.1 (hv.trans ?_)` and prove the remaining obligations.

Rewrite using `[Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[_root_.mul_assoc]`. Use `congrArg _ ((hρ j _ (h.left ≫ x) z _ hm (Good.mem hJ _ _)).trans (congrArg (· * _) ?_))` and prove the remaining obligations. Conclude with `(gs_appLE h.left x z _ ⊤ hx trivial _).symm`.

Establish `a₁` using `aux x hx _ _ ((congrArg Units.val (val_pull hJ τx h.left (𝟙 _))).trans ((hτx _ _ z J hJ).trans (by rw [Category.id_comp]))) (hc (h ≫ x') (h.left ≫ x) (Category.assoc _ _ _) (Category.assoc _ _ _) _ vx hvx z J hJ)`. Establish `a₂` using `aux y hy _ _ ((congrArg Units.val (val_pull hJ τy h.left (𝟙 _))).trans ((hτy _ _ z J hJ).trans (by rw [Category.id_comp]))) (hc (h ≫ y') (h.left ≫ y) ((Category.assoc _ _ _).trans (congrArg (h.left ≫ ·) hxy.symm)) (Category.assoc _ _ _) _ vy hvy z J hJ)`. Rewrite using `[a₁, a₂]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [hr j]`. Conclude with `(cancel_mono w).1 (congrArg (fun a => a.left) E)`.
-/
theorem ample : (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → ∀ U : S.Opens, IsAffineOpen U → ∃ (m : ℕ) (b : Fin (m + 1) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) U))), ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ overRes (T := baseOver S) U) (b' : Fin (m + 1) → LB.Sec (LPow P.A P.L n T')), (∀ i, IsPullSec P.A P.L n (h ▷ P.A) (whiskerRight_snd h P.A) (b i) (b' i)) → Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T')) = ⊤) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (n : ℕ), 2 ≤ n → ∀ x : Over.mk t ⟶ P.A, ∃ (s : LB.Sec (LPow P.A P.L n (Over.mk t))) (τ : LB.Gen (LB.LinComb P.L (Y := (Over.mk t).left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (v : Γ((Over.mk t).left, ⊤)), τ.IsGen ∧ IsValueAt P.A P.L n s x τ v ∧ IsUnit v) → (∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 3 ≤ n → ∀ (T : Over S) [IsLocallyNoetherian T.left] (x y : T ⟶ P.A) (τx : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ)))) (τy : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => y.left) (fun _ => (n : ℤ)))), τx.IsGen → τy.IsGen → (∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T) (s : LB.Sec (LPow P.A P.L n T')) (vx vy : Γ(T'.left, ⊤)), IsValueAt P.A P.L n s (h ≫ x) (LB.pullGen P.L _ _ τx h.left) vx → IsValueAt P.A P.L n s (h ≫ y) (LB.pullGen P.L _ _ τy h.left) vy → vx = vy) → x = y) → AmpleSt := by
  intro hS hG hM S _ P n hn
  suffices H : VeryAmpleAt P.A P.L n from
    ⟨fun U hU => by obtain ⟨m, s, h, -⟩ := H U hU; exact ⟨m, s, h⟩, H⟩
  intro U hU
  obtain ⟨m, b, hb⟩ := hS S P n (by omega) U hU
  have hL := P.isLB
  have : IsProper P.A.hom := P.isAb.proper
  have : IsAffine U.toScheme := hU
  let T : Over S := overRes (T := baseOver S) U
  let Y : Scheme.{0} := (P.A.hom ⁻¹ᵁ U).toScheme
  let w : Y ⟶ P.A.left := (P.A.hom ⁻¹ᵁ U).ι
  let f : Y ⟶ U.toScheme := P.A.hom ∣_ U
  have hf : f ≫ T.hom = w ≫ P.A.hom := by
    change f ≫ U.ι ≫ 𝟙 S = _
    rw [Category.comp_id]
    exact morphismRestrict_ι _ _
  obtain ⟨e, e₁, e₂⟩ : ∃ e : Y ⟶ (T ⊗ P.A).left, e ≫ (fst T P.A).left = f ∧ e ≫ (snd T P.A).left = w :=
    ⟨pullback.lift f w hf, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hs : ∀ i, ∃ s : LB.Sec (LB.LinComb P.L (K := Fin n) (fun _ => w) (fun _ => 1)),
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good P.L z J → sval s r z J =
        sval (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (n : ℤ)) (b i) (r ≫ e) z J := fun i => by
    obtain ⟨s, hs⟩ := exists_sec hL (formEq_pow _ w e₂ n)
      (H1.SectionArithmetic.pullSec (φ := fun _ : Fin 1 => (snd T P.A).left) (ε := fun _ => (n : ℤ)) (b i) e)
    exact ⟨s, fun Z r z J hJ => (hs Z r z J hJ).trans (H1.SectionArithmetic.sval_pullSec _ e r z hJ)⟩
  choose s hs using hs
  have key' : ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ T) (σ : LB.Sec (LPow P.A P.L n T')),
      ∃ c : Fin (m + 1) → Γ(T'.left, ⊤), ∀ (x : T' ⟶ P.A) (g : T'.left ⟶ Y), g ≫ f = h.left → g ≫ w = x.left →
      ∀ (τ : LB.Gen (LB.LinComb P.L (Y := T'.left) (K := Fin 1) (fun _ => x.left) (fun _ => (n : ℤ))))
        (v : Γ(T'.left, ⊤)), IsValueAt P.A P.L n σ x τ v → ∀ z J, Good P.L z J →
        gs (𝟙 _) z ⊤ v * (val τ (𝟙 _) z J).val = ∑ i, gs (𝟙 _) z ⊤ (c i) * sval (s i) g z J := by
    intro T' _ h σ
    obtain ⟨c, hc⟩ := key P.A b T' h (hb T' h) σ
    refine ⟨c, fun x g a₁ a₂ τ v hv z J hJ => ?_⟩
    rw [hc x (g ≫ e) (by rw [Category.assoc, e₁, a₁]) (by rw [Category.assoc, e₂, a₂]) τ v hv z J hJ]
    exact Finset.sum_congr rfl fun i _ => by rw [hs i _ g z J hJ]
  have hcov : ⨆ i, nonzeroLocus (s i) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    let K := AlgebraicClosure (Y.residueField y)
    let g : Spec (.of K) ⟶ Y := Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) K)) ≫ Y.fromSpecResidueField y
    let z : Spec (.of K) := IsLocalRing.closedPoint K
    have hz : g z = y := Scheme.fromSpecResidueField_apply y _
    let x : Over.mk (g ≫ w ≫ P.A.hom) ⟶ P.A := Over.homMk (g ≫ w) (Category.assoc _ _ _)
    obtain ⟨σ, τ, v, -, hv, hu⟩ := hG S P K (g ≫ w ≫ P.A.hom) n (by omega) x
    have : IsAffine (Over.mk (g ≫ w ≫ P.A.hom)).left := inferInstanceAs (IsAffine (Spec (.of K)))
    obtain ⟨c, hc⟩ := key' (Over.mk (g ≫ w ≫ P.A.hom)) (Over.homMk (g ≫ f) (by
      change (g ≫ f) ≫ T.hom = g ≫ w ≫ P.A.hom
      rw [Category.assoc, hf])) σ
    choose J hJ using fun χ : Spec (.of K) ⟶ P.A.left => exists_chart hL (χ z)
    have k := hc x g rfl rfl τ v hv z J hJ
    have u : IsUnit (gs (𝟙 (Over.mk (g ≫ w ≫ P.A.hom)).left) z ⊤ v) := by
      rw [gs_eq _ _ ⊤ trivial]
      exact (hu.map _).map _
    obtain ⟨i, -, hi⟩ := IsLocalRing.exists_of_isUnit_sum (k ▸ u.mul (Units.isUnit _))
    exact Opens.mem_iSup.2 ⟨i, hz ▸ (isUnit_sval (s i) g z hJ).1 (isUnit_of_mul_isUnit_right hi)⟩
  refine ⟨m, s, hcov, fun i => ?_⟩
  choose ρ hρ using fun j => exists_ratio (s i) (s j)
  have := affine_surj f (nonzeroLocus (s i)) ρ le_top (valuative s hcov i ρ hρ) ?_
  · refine ⟨this.1, ρ, fun j k => fn_ext fun y hy => ?_, this.2⟩
    exact (gs_res _ y _ hy _).trans ((hρ j _ (𝟙 Y) y k hy.1 hy.2).trans ((gs_mul _ y _ hy _ _).trans
      (congrArg₂ (· * ·) (gs_res _ y _ hy _) (gs_res _ y _ hy _))).symm)
  intro Z _ x y hx hy hxy hr
  let Z' : Over S := Over.mk (x ≫ w ≫ P.A.hom)
  let x' : Z' ⟶ P.A := Over.homMk (x ≫ w) (Category.assoc _ _ _)
  let y' : Z' ⟶ P.A := Over.homMk (y ≫ w) (by
    change (y ≫ w) ≫ P.A.hom = x ≫ w ≫ P.A.hom
    rw [Category.assoc, ← hf, reassoc_of% hxy])
  let q : Z' ⟶ T := Over.homMk (x ≫ f) (by
    change (x ≫ f) ≫ T.hom = x ≫ w ≫ P.A.hom
    rw [Category.assoc, hf])
  obtain ⟨τx, gx, hτx⟩ := exists_frame hL w n (s i) x hx x'.left rfl
  obtain ⟨τy, gy, hτy⟩ := exists_frame hL w n (s i) y hy y'.left rfl
  have : IsLocallyNoetherian Z'.left := inferInstanceAs (IsLocallyNoetherian Z)
  have E := hM S P n (by omega) Z' x' y' τx τy gx gy fun T' _ h σ vx vy hvx hvy => by
    obtain ⟨c, hc⟩ := key' T' (h ≫ q) σ
    refine fn_ext fun z _ => ?_
    choose J hJ using fun χ : T'.left ⟶ P.A.left => exists_chart hL (χ z)
    have aux : ∀ (x : Z ⟶ Y) (hx : ⊤ ≤ x ⁻¹ᵁ nonzeroLocus (s i)) (v u : T'.left.presheaf.stalk z),
        u = sval (s i) (h.left ≫ x) z J → v * u = ∑ j, gs (𝟙 _) z ⊤ (c j) * sval (s j) (h.left ≫ x) z J →
        v = ∑ j, gs (𝟙 _) z ⊤ (c j) * gs h.left z ⊤ ((x.appLE _ ⊤ hx).hom (ρ j)) := by
      rintro x hx v _ rfl hv
      have hm : (h.left ≫ x) z ∈ nonzeroLocus (s i) := hx trivial
      refine ((isUnit_sval (s i) (h.left ≫ x) z hJ).2 hm).mul_left_inj.1 (hv.trans ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [_root_.mul_assoc]
      refine congrArg _ ((hρ j _ (h.left ≫ x) z _ hm (Good.mem hJ _ _)).trans (congrArg (· * _) ?_))
      exact (gs_appLE h.left x z _ ⊤ hx trivial _).symm
    have a₁ := aux x hx _ _ ((congrArg Units.val (val_pull hJ τx h.left (𝟙 _))).trans
      ((hτx _ _ z J hJ).trans (by rw [Category.id_comp])))
      (hc (h ≫ x') (h.left ≫ x) (Category.assoc _ _ _) (Category.assoc _ _ _) _ vx hvx z J hJ)
    have a₂ := aux y hy _ _ ((congrArg Units.val (val_pull hJ τy h.left (𝟙 _))).trans
      ((hτy _ _ z J hJ).trans (by rw [Category.id_comp])))
      (hc (h ≫ y') (h.left ≫ y) ((Category.assoc _ _ _).trans (congrArg (h.left ≫ ·) hxy.symm))
        (Category.assoc _ _ _) _ vy hvy z J hJ)
    rw [a₁, a₂]
    exact Finset.sum_congr rfl fun j _ => by rw [hr j]
  exact (cancel_mono w).1 (congrArg (fun a => a.left) E)

end GlobalTheory.VeryAmplePow
