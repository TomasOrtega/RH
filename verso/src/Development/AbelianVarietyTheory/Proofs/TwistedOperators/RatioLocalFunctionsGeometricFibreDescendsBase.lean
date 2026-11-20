import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFunctionOfSmoothLocalDescentReducedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.GlobalSectionsBijection

/- English proof (translation)
The claim follows from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)`.
-/
theorem toΓ_bij (S : Type) [CommRing S] : Function.Bijective (toΓ S) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)

/- English proof (translation)
The claim follows from `(Scheme.Hom.app_eq_appLE _).symm`.
-/
theorem appLE_top_top {X Y : Scheme.{0}} (f : X ⟶ Y) : f.appLE ⊤ ⊤ le_top = f.appTop :=
  (Scheme.Hom.app_eq_appLE _).symm

/- English proof (translation)
Rewrite using `[appLE_top_top]`. Conclude with `(congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ))).symm`.
-/
theorem spMap_appLE_toΓ {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) (a : T) :
    ((spMap χ).appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
  rw [appLE_top_top]
  exact (congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom χ))).symm

/- English proof (translation)
Establish `key : (q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h) = (w ≫ q).appLE ⊤ ⊤ le_top` using `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`. Rewrite using `[← CommRingCat.comp_apply, key]`. Establish `: ∀ g : Sp Ω ⟶ Sp T, g = spMap χ → (g.appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a)`. Introduce and unpack `_ rfl`. Conclude with `spMap_appLE_toΓ χ a`.

Conclude with `this _ hw`.
-/
theorem compat {T Ω : Type} [CommRing T] [CommRing Ω] {Y : Scheme.{0}} (q : Y ⟶ Sp T) (χ : T →+* Ω)
    (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (hw : w ≫ q = spMap χ) (a : T) :
    (w.appLE U ⊤ h).hom ((q.appLE ⊤ U le_top).hom (toΓ T a)) = toΓ Ω (χ a) := by
  have key : (q.appLE ⊤ U le_top ≫ w.appLE U ⊤ h) = (w ≫ q).appLE ⊤ ⊤ le_top :=
    Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
  rw [← CommRingCat.comp_apply, key]
  have : ∀ g : Sp Ω ⟶ Sp T, g = spMap χ → (g.appLE ⊤ ⊤ le_top).hom (toΓ T a) = toΓ Ω (χ a) := by
    rintro _ rfl; exact spMap_appLE_toΓ χ a
  exact this _ hw

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

/- English proof (translation)
Introduce `h0`. Establish `e` using `Scheme.basicOpen_appLE w ⊤ U h s`. Rewrite `e` using `[h0, Scheme.basicOpen_zero]`. Establish `: x ∈ (⊤ ⊓ w ⁻¹ᵁ Y.basicOpen s : (Sp Ω).Opens)` using `⟨trivial, hx⟩`. Rewrite `this` using `[← e]`.

Conclude with `this`.
-/
theorem ne_zero_of_mem {Ω : Type} [CommRing Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (x : Sp Ω) (hx : w x ∈ Y.basicOpen s) : (w.appLE U ⊤ h).hom s ≠ 0 := by
  intro h0
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at e
  have : x ∈ (⊤ ⊓ w ⁻¹ᵁ Y.basicOpen s : (Sp Ω).Opens) := ⟨trivial, hx⟩
  rw [← e] at this
  exact this

/- English proof (translation)
Use `set g := (w.appLE U ⊤ h).hom s`. Establish `hu : IsUnit g`. Establish `e0 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom g ≠ 0`. Introduce `e0`. Apply `hs` to reduce the goal to its premises.

Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom e0` as an intermediate fact. Rewrite `this` using `[← CommRingCat.comp_apply, Iso.hom_inv_id, map_zero]`. Conclude with `this`. Use `(IsUnit.mk0 _ e0).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom` as an intermediate fact. Rewrite `this` using `[← CommRingCat.comp_apply, Iso.hom_inv_id]`.

Conclude with `this`. Establish `e` using `Scheme.basicOpen_appLE w ⊤ U h s`. Rewrite `e` using `[Scheme.basicOpen_of_isUnit _ hu]`. Establish `: x ∈ (⊤ : (Sp Ω).Opens)` using `trivial`. Rewrite `this` using `[e]`.

Conclude with `this.2`.
-/
theorem mem_of_ne_zero {Ω : Type} [Field Ω] {Y : Scheme.{0}} (w : Sp Ω ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U)
    (s : Γ(Y, U)) (hs : (w.appLE U ⊤ h).hom s ≠ 0) (x : Sp Ω) : w x ∈ Y.basicOpen s := by
  set g := (w.appLE U ⊤ h).hom s
  have hu : IsUnit g := by
    have e0 : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom g ≠ 0 := by
      intro e0
      apply hs
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom e0
      rw [← CommRingCat.comp_apply, Iso.hom_inv_id, map_zero] at this
      exact this
    have := (IsUnit.mk0 _ e0).map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id] at this
    exact this
  have e := Scheme.basicOpen_appLE w ⊤ U h s
  rw [Scheme.basicOpen_of_isUnit _ hu] at e
  have : x ∈ (⊤ : (Sp Ω).Opens) := trivial
  rw [e] at this
  exact this.2

/- English proof (translation)
Use `⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance, Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫ Y.fromSpecResidueField y, fun x => ?_⟩` and prove the remaining obligations. Establish `: (Y.fromSpecResidueField y) ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y))))) x) ∈ Set.range (Y.fromSpecResidueField y)` using `⟨_, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecResidueField]`. Conclude with `this`.
-/
theorem exists_geom (Y : Scheme.{0}) (y : Y) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (w : Sp Ω ⟶ Y), ∀ x, w x = y := by
  refine ⟨AlgebraicClosure (Y.residueField y), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
      Y.fromSpecResidueField y, fun x => ?_⟩
  have : (Y.fromSpecResidueField y) ((Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y)
      (AlgebraicClosure (Y.residueField y))))) x) ∈ Set.range (Y.fromSpecResidueField y) := ⟨_, rfl⟩
  rw [Scheme.range_fromSpecResidueField] at this
  exact this

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

/- English proof (translation)
Rewrite using `[Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Rewrite using `[show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id, Category.comp_id]`.
-/
theorem fromSpec_appLE_top {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) (e : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W) :
    hW.fromSpec.appLE W ⊤ e = (Scheme.ΓSpecIso Γ(Y, W)).inv := by
  rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  rw [show (eqToHom hW.fromSpec_preimage_self).op ≫ (homOfLE e).op = 𝟙 _ from Subsingleton.elim _ _,
    CategoryTheory.Functor.map_id, Category.comp_id]

/- English proof (translation)
Introduce `x _`. Use `show hV.fromSpec (spMap c x) ∈ (V : Set Y)`. Rewrite using `[← hV.range_fromSpec]`. Conclude with `⟨_, rfl⟩`.
-/
theorem chart_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ V := by
  intro x _
  show hV.fromSpec (spMap c x) ∈ (V : Set Y)
  rw [← hV.range_fromSpec]
  exact ⟨_, rfl⟩

/- English proof (translation)
Establish `h'` using `chart_top hV c`. Establish `e1 : (spMap c ≫ hV.fromSpec).appLE U' ⊤ h = Y.presheaf.map (homOfLE hle).op ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ h'` using `(Scheme.Hom.map_appLE _ _ _).symm`. Establish `e0 : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V` using `by simp`. Establish `e2 : (spMap c ≫ hV.fromSpec).appLE V ⊤ h' = hV.fromSpec.appLE V ⊤ e0 ≫ (spMap c).appLE ⊤ ⊤ le_top` using `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`. Rewrite using `[e1, e2, fromSpec_appLE_top]`.

Simplify using `only [CommRingCat.comp_apply]`. Conclude with `spMap_appLE_toΓ c _`.
-/
theorem chart_eval {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R : Type} [CommRing R]
    (c : Γ(Y, V) →+* R) (U' : Y.Opens) (hle : V ≤ U') (h : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U')
    (s : Γ(Y, U')) :
    ((spMap c ≫ hV.fromSpec).appLE U' ⊤ h).hom s = toΓ R (c ((Y.presheaf.map (homOfLE hle).op).hom s)) := by
  have h' := chart_top hV c
  have e1 : (spMap c ≫ hV.fromSpec).appLE U' ⊤ h =
      Y.presheaf.map (homOfLE hle).op ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ h' :=
    (Scheme.Hom.map_appLE _ _ _).symm
  have e0 : (⊤ : (Spec Γ(Y, V)).Opens) ≤ hV.fromSpec ⁻¹ᵁ V := by simp
  have e2 : (spMap c ≫ hV.fromSpec).appLE V ⊤ h' =
      hV.fromSpec.appLE V ⊤ e0 ≫ (spMap c).appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e1, e2, fromSpec_appLE_top]
  simp only [CommRingCat.comp_apply]
  exact spMap_appLE_toΓ c _

end GlobalTheory.GlobalSectionsBijection

namespace GlobalTheory.GlobalSectionsBijection

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← appLE_top_top, ← appLE_top_top]`. Use extensionality with `x`. Take `⟨a, rfl⟩` from `(toΓ_bij T).2 x`. Establish `key : ((spMap c ≫ hV.fromSpec) ≫ q).appLE ⊤ ⊤ le_top = q.appLE ⊤ V le_top ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ (chart_top hV c)` using `(Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm`.

Rewrite using `[key, CommRingCat.comp_apply, chart_eval hV c V le_rfl, spMap_appLE_toΓ]`. Simplify using the standard rewrite rules.
-/
theorem chart_comp {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {R T : Type} [CommRing R] [CommRing T]
    (q : Y ⟶ Sp T) (c : Γ(Y, V) →+* R) :
    (spMap c ≫ hV.fromSpec) ≫ q = spMap (c.comp ((q.appLE ⊤ V le_top).hom.comp (toΓ T))) := by
  apply ext_of_isAffine
  rw [← appLE_top_top, ← appLE_top_top]
  ext x
  obtain ⟨a, rfl⟩ := (toΓ_bij T).2 x
  have key : ((spMap c ≫ hV.fromSpec) ≫ q).appLE ⊤ ⊤ le_top =
      q.appLE ⊤ V le_top ≫ (spMap c ≫ hV.fromSpec).appLE V ⊤ (chart_top hV c) :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [key, CommRingCat.comp_apply, chart_eval hV c V le_rfl, spMap_appLE_toΓ]
  simp

end GlobalTheory.GlobalSectionsBijection

open GlobalTheory.GlobalSectionsBijection in

/- English proof (translation)
Introduce `T _ _ Y q I₀ U t t₀ hq H`. Use `haveI := hq`. Use `haveI : IsReduced Y := GlobalTheory.isReduced_of_smooth_of_isReduced q`. Set `F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω], (T →ₐ[ℤ] Ω) → Ω` to `fun Ω _ _ _ χ => Classical.choose (H Ω χ.toRingHom)`. Establish `hF : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω] (χ : T →ₐ[ℤ] Ω) (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ.toRingHom → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω (F Ω χ) * (w.appLE (U j) ⊤ h).hom (t₀ j)` using `fun Ω _ _ _ χ => (Classical.choose_spec (H Ω χ.toRingHom)).1`.

Use `(GlobalTheory.T.exists_function_of_smooth_local_descent_reduced ℤ T F ?_).elim ?_` and prove the remaining obligations. Introduce `p`. Set `κ` to `p.asIdeal.ResidueField`. Set `Ω` to `AlgebraicClosure κ`. Set `χ : T →+* Ω` to `(algebraMap κ Ω).comp (algebraMap T κ)`.

Take `⟨α, hα, j, w, h, hwq, hne⟩` from `H Ω χ`. Establish `hyD : w default ∈ Y.basicOpen (t₀ j)` using `mem_of_ne_zero w (U j) h (t₀ j) hne default`. Take `⟨V, hV, hyV, hVD⟩` from `exists_isAffineOpen_mem_and_subset hyD`. Establish `hVU : V ≤ U j` using `hVD.trans (Y.basicOpen_le _)`. Set `φ : T →+* Γ(Y, V)` to `(q.appLE ⊤ V le_top).hom.comp (toΓ T)`.

Use `letI := φ.toAlgebra`. Establish `hu : IsUnit ((Y.presheaf.map (homOfLE hVU).op).hom (t₀ j))`. Establish `h0` using `Y.toRingedSpace.isUnit_res_basicOpen (t₀ j)`. Establish `h1` using `h0.map (Y.presheaf.map (homOfLE hVD).op).hom`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Conclude with `congrArg (fun f => (CommRingCat.Hom.hom f) (t₀ j)) (Y.presheaf.map_comp (homOfLE (Y.basicOpen_le (t₀ j))).op (homOfLE hVD).op)`. Set `b' : Γ(Y, V)` to `(Y.presheaf.map (homOfLE hVU).op).hom (t j) * ↑hu.unit⁻¹`. Use `⟨Γ(Y, V), inferInstance, inferInstance, inferInstance, inferInstance, b', ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show φ.Smooth`. Conclude with `(RingHom.Smooth.of_bijective (toΓ_bij T)).comp (q.smooth_appLE (isAffineOpen_top _) hV le_top)`.

Establish `hwV : ⊤ ≤ w ⁻¹ᵁ V` using `fun x _ => by show w x ∈ V`. Rewrite using `[Subsingleton.elim x default]`. Conclude with `hyV`. Set `ψ : Γ(Y, V) →+* Ω` to `(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (w.appLE V ⊤ hwV).hom`. Establish `hψφ : ψ.comp φ = χ`.

Use extensionality with `a`. Use `show (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE V ⊤ hwV).hom ((q.appLE ⊤ V le_top).hom (toΓ T a))) = χ a`. Rewrite using `[compat q χ w V hwV hwq a, toΓ, ← CommRingCat.comp_apply, Iso.inv_hom_id]`. Both sides reduce to the same expression. Use `⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩` and prove the remaining obligations.

Use `show Ideal.comap φ (RingHom.ker ψ) = p.asIdeal`. Rewrite using `[RingHom.comap_ker, hψφ]`. Use extensionality with `a`. Simplify using `only [RingHom.mem_ker, χ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Ω).injective]`. Rewrite using `[← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]`.

Introduce `Ω' _ _ _ χ'`. Set `c : Γ(Y, V) →+* Ω'` to `χ'.toRingHom`. Establish `hw'U : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U j` using `fun x hx => hVU (chart_top hV c hx)`. Establish `hcomp : (spMap c ≫ hV.fromSpec) ≫ q = spMap (χ'.comp (IsScalarTower.toAlgHom ℤ T Γ(Y, V))).toRingHom` using `chart_comp hV q c`. Establish `e` using `hF Ω' _ j _ hw'U hcomp`.

Rewrite `e` using `[chart_eval hV c (U j) hVU, chart_eval hV c (U j) hVU, ← map_mul]`. Establish `e2` using `(toΓ_bij Ω').1 e`. Use `show c (_ * _) = _`. Rewrite using `[map_mul, e2, _root_.mul_assoc, ← map_mul, hu.mul_val_inv, map_one, _root_.mul_one]`. Introduce `a ha`.

Use `⟨a, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Apply `eq_zero_of_basicOpen_eq_bot` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

It suffices to derive a contradiction. Take `⟨Ω, _, _, w, hw⟩` from `exists_geom Y y`. Establish `hyU : y ∈ U j` using `Y.basicOpen_le _ hy`. Establish `h : ⊤ ≤ w ⁻¹ᵁ U j` using `fun x _ => by show w x ∈ U j`. Rewrite using `[hw]`.

Conclude with `hyU`. Set `χ : T →+* Ω` to `(Spec.preimage (w ≫ q)).hom`. Establish `hχ : w ≫ q = spMap χ` using `(Spec.map_preimage (w ≫ q)).symm`. Establish `e1` using `hF Ω χ.toIntAlgHom j w h hχ`. Establish `e2` using `ha Ω χ.toIntAlgHom`.

Apply `ne_zero_of_mem w (U j) h _ default (by rw [hw]; exact hy)` to reduce the goal to its premises. Rewrite using `[map_sub, map_mul, compat q χ w (U j) h hχ a, e1]`. Rewrite using `[← e2]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.ratio_descends : ∀ (T : Type) [CommRing T] [IsReduced T] (Y : Scheme.{0}) (q : Y ⟶ Sp T) (I₀ : Type) (U : I₀ → Y.Opens) (t t₀ : ∀ j, Γ(Y, U j)), Smooth q → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω), ∃ α : Ω, (∀ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ → (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω α * (w.appLE (U j) ⊤ h).hom (t₀ j)) ∧ ∃ (j : I₀) (w : Sp Ω ⟶ Y) (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ ∧ (w.appLE (U j) ⊤ h).hom (t₀ j) ≠ 0) → ∃ a : T, ∀ j, t j = (q.appLE ⊤ (U j) le_top).hom (toΓ T a) * t₀ j := by
  intro T _ _ Y q I₀ U t t₀ hq H
  haveI := hq
  haveI : IsReduced Y := GlobalTheory.isReduced_of_smooth_of_isReduced q
  let F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω], (T →ₐ[ℤ] Ω) → Ω :=
    fun Ω _ _ _ χ => Classical.choose (H Ω χ.toRingHom)
  have hF : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℤ Ω] (χ : T →ₐ[ℤ] Ω) (j : I₀) (w : Sp Ω ⟶ Y)
      (h : ⊤ ≤ w ⁻¹ᵁ U j), w ≫ q = spMap χ.toRingHom →
      (w.appLE (U j) ⊤ h).hom (t j) = toΓ Ω (F Ω χ) * (w.appLE (U j) ⊤ h).hom (t₀ j) :=
    fun Ω _ _ _ χ => (Classical.choose_spec (H Ω χ.toRingHom)).1
  refine (GlobalTheory.T.exists_function_of_smooth_local_descent_reduced ℤ T F ?_).elim ?_
  · intro p
    let κ := p.asIdeal.ResidueField
    let Ω := AlgebraicClosure κ
    let χ : T →+* Ω := (algebraMap κ Ω).comp (algebraMap T κ)
    obtain ⟨α, hα, j, w, h, hwq, hne⟩ := H Ω χ
    have hyD : w default ∈ Y.basicOpen (t₀ j) := mem_of_ne_zero w (U j) h (t₀ j) hne default
    obtain ⟨V, hV, hyV, hVD⟩ := exists_isAffineOpen_mem_and_subset hyD
    have hVU : V ≤ U j := hVD.trans (Y.basicOpen_le _)
    let φ : T →+* Γ(Y, V) := (q.appLE ⊤ V le_top).hom.comp (toΓ T)
    letI := φ.toAlgebra
    have hu : IsUnit ((Y.presheaf.map (homOfLE hVU).op).hom (t₀ j)) := by
      have h0 := Y.toRingedSpace.isUnit_res_basicOpen (t₀ j)
      have h1 := h0.map (Y.presheaf.map (homOfLE hVD).op).hom
      convert h1 using 1
      exact congrArg (fun f => (CommRingCat.Hom.hom f) (t₀ j))
        (Y.presheaf.map_comp (homOfLE (Y.basicOpen_le (t₀ j))).op (homOfLE hVD).op)
    let b' : Γ(Y, V) := (Y.presheaf.map (homOfLE hVU).op).hom (t j) * ↑hu.unit⁻¹
    refine ⟨Γ(Y, V), inferInstance, inferInstance, inferInstance, inferInstance, b', ?_, ?_, ?_⟩
    · show φ.Smooth
      exact (RingHom.Smooth.of_bijective (toΓ_bij T)).comp (q.smooth_appLE (isAffineOpen_top _) hV le_top)
    · have hwV : ⊤ ≤ w ⁻¹ᵁ V := fun x _ => by
        show w x ∈ V
        rw [Subsingleton.elim x default]; exact hyV
      let ψ : Γ(Y, V) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp (w.appLE V ⊤ hwV).hom
      have hψφ : ψ.comp φ = χ := by
        ext a
        show (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((w.appLE V ⊤ hwV).hom ((q.appLE ⊤ V le_top).hom (toΓ T a))) = χ a
        rw [compat q χ w V hwV hwq a, toΓ, ← CommRingCat.comp_apply, Iso.inv_hom_id]
        rfl
      refine ⟨⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩, PrimeSpectrum.ext ?_⟩
      show Ideal.comap φ (RingHom.ker ψ) = p.asIdeal
      rw [RingHom.comap_ker, hψφ]
      ext a
      simp only [RingHom.mem_ker, χ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap κ Ω).injective]
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    · intro Ω' _ _ _ χ'
      let c : Γ(Y, V) →+* Ω' := χ'.toRingHom
      have hw'U : ⊤ ≤ (spMap c ≫ hV.fromSpec) ⁻¹ᵁ U j := fun x hx => hVU (chart_top hV c hx)
      have hcomp : (spMap c ≫ hV.fromSpec) ≫ q =
          spMap (χ'.comp (IsScalarTower.toAlgHom ℤ T Γ(Y, V))).toRingHom := chart_comp hV q c
      have e := hF Ω' _ j _ hw'U hcomp
      rw [chart_eval hV c (U j) hVU, chart_eval hV c (U j) hVU, ← map_mul] at e
      have e2 := (toΓ_bij Ω').1 e
      show c (_ * _) = _
      rw [map_mul, e2, _root_.mul_assoc, ← map_mul, hu.mul_val_inv, map_one, _root_.mul_one]
  · intro a ha
    refine ⟨a, fun j => ?_⟩
    rw [← sub_eq_zero]
    apply eq_zero_of_basicOpen_eq_bot
    rw [eq_bot_iff]
    intro y hy
    exfalso
    obtain ⟨Ω, _, _, w, hw⟩ := exists_geom Y y
    have hyU : y ∈ U j := Y.basicOpen_le _ hy
    have h : ⊤ ≤ w ⁻¹ᵁ U j := fun x _ => by
      show w x ∈ U j
      rw [hw]; exact hyU
    let χ : T →+* Ω := (Spec.preimage (w ≫ q)).hom
    have hχ : w ≫ q = spMap χ := (Spec.map_preimage (w ≫ q)).symm
    have e1 := hF Ω χ.toIntAlgHom j w h hχ
    have e2 := ha Ω χ.toIntAlgHom
    apply ne_zero_of_mem w (U j) h _ default (by rw [hw]; exact hy)
    rw [map_sub, map_mul, compat q χ w (U j) h hχ a, e1]
    rw [← e2]
    simp
