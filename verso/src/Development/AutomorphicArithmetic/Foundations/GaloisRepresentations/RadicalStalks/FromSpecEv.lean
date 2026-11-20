import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.ExistsFunctionalNeZeroProjective
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.RootGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroSmoothAffineOpenStatement

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

/- English proof (translation)
Rewrite using `[← Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h (by simp), Category.assoc, Category.assoc]`. Use `congr 1`. Establish `hh : (spMap g).appLE ⊤ ⊤ (by simp) = (spMap g).appTop`. Simplify using `[Scheme.Hom.appLE]`. Conclude with `Category.comp_id _`.

Rewrite using `[hh]`. Conclude with `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)`.
-/
private lemma ev_comp {T T' : Type} [CommRing T] [CommRing T'] (g : T →+* T') {Y : Scheme.{0}} (U : Y.Opens)
    (f : Sp T ⟶ Y) (h : ⊤ ≤ f ⁻¹ᵁ U) (h' : ⊤ ≤ (spMap g ≫ f) ⁻¹ᵁ U) :
    (spMap g ≫ f).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of T')).hom =
      (f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom) ≫ CommRingCat.ofHom g := by
  rw [← Scheme.Hom.appLE_comp_appLE (spMap g) f U ⊤ ⊤ h (by simp), Category.assoc, Category.assoc]
  congr 1
  have hh : (spMap g).appLE ⊤ ⊤ (by simp) = (spMap g).appTop := by
    simp [Scheme.Hom.appLE]
    exact Category.comp_id _
  rw [hh]
  exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom g)

/- English proof (translation)
Establish `e' : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V` using `hV.fromSpec_preimage_self.ge`. Rewrite using `[← Scheme.Hom.map_appLE hV.fromSpec e' (homOfLE hVW).op, Category.assoc]`. Establish `key : hV.fromSpec.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = 𝟙 _`. Simplify using `only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]`. Rewrite using `[← Functor.map_comp_assoc]`.

Establish `hid : ∀ i : Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤, i = 𝟙 _` using `fun i => Quiver.Hom.unop_inj (Subsingleton.elim _ _)`. Rewrite using `[hid (_ ≫ _), CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]`. Rewrite using `[key, Category.comp_id]`.
-/
private lemma fromSpec_ev {X : Scheme.{0}} {V W : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ W)
    (e : ⊤ ≤ hV.fromSpec ⁻¹ᵁ W) :
    hV.fromSpec.appLE W ⊤ e ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = X.presheaf.map (homOfLE hVW).op := by
  have e' : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  rw [← Scheme.Hom.map_appLE hV.fromSpec e' (homOfLE hVW).op, Category.assoc]
  have key : hV.fromSpec.appLE V ⊤ e' ≫ (Scheme.ΓSpecIso Γ(X, V)).hom = 𝟙 _ := by
    simp only [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc]
    rw [← Functor.map_comp_assoc]
    have hid : ∀ i : Opposite.op (⊤ : (Spec Γ(X, V)).Opens) ⟶ Opposite.op ⊤, i = 𝟙 _ :=
      fun i => Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [hid (_ ≫ _), CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id]
  rw [key, Category.comp_id]

/- English proof (translation)
Establish `h0 : ⊤ ≤ hA.fromSpec ⁻¹ᵁ (ψ ⁻¹ᵁ U)` using `hA.fromSpec_preimage_self.ge.trans ((TopologicalSpace.Opens.map hA.fromSpec.base).map (homOfLE hV)).le`. Establish `h1 : ⊤ ≤ (hA.fromSpec ≫ ψ) ⁻¹ᵁ U` using `h0`. Establish `h2 : ⊤ ≤ (spMap φ ≫ hA.fromSpec ≫ ψ) ⁻¹ᵁ U` using `fun x _ => h1 (Set.mem_univ _)`. Establish `hc' : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ spMap φ ≫ hA.fromSpec ≫ ψ = spMap φ ≫ hA.fromSpec ≫ ψ` using `hc`. Establish `hcongr : ∀ (w₁ w₂ : Sp (DualNumber k) ⟶ Y), w₁ = w₂ → ∀ (e₁ : ⊤ ≤ w₁ ⁻¹ᵁ U) (e₂ : ⊤ ≤ w₂ ⁻¹ᵁ U), w₁.appLE U ⊤ e₁ = w₂.appLE U ⊤ e₂`.

Introduce and unpack `_ _ rfl _ _`. Both sides reduce to the same expression. Establish `A` using `ev_comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) U (spMap φ ≫ hA.fromSpec ≫ ψ) h2 (hc'.symm ▸ h2)`. Rewrite `A` using `[hcongr _ _ hc' _ h2]`. Establish `B` using `ev_comp φ U (hA.fromSpec ≫ ψ) h1 h2`.

Establish `C` using `fromSpec_ev hA hV h0`. Establish `B' : (spMap φ ≫ hA.fromSpec ≫ ψ).appLE U ⊤ h2 ≫ (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom = ψ.app U ≫ X.presheaf.map (homOfLE hV).op ≫ CommRingCat.ofHom φ`. Rewrite using `[B, Scheme.Hom.comp_appLE, Category.assoc, Category.assoc]`. Use `erw [← Category.assoc (hA.fromSpec.appLE _ _ _), C]`. Establish `A'` using `ConcreteCategory.congr_hom A t`.

Rewrite `A'` using `[B']`. Establish `hxx : φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)) = ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)))`. Simplify using `using A'`. Rewrite using `[hxx, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]`.
-/
private lemma snd_zero {k : Type} [Field k] {X Y : Scheme.{0}} (ψ : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hV : V ≤ ψ ⁻¹ᵁ U) (hA : IsAffineOpen V) (φ : Γ(X, V) →+* DualNumber k)
    (hc : IsConst (spMap φ ≫ hA.fromSpec ≫ ψ)) (t : Γ(Y, U)) :
    TrivSqZeroExt.snd (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) = 0 := by
  have h0 : ⊤ ≤ hA.fromSpec ⁻¹ᵁ (ψ ⁻¹ᵁ U) :=
    hA.fromSpec_preimage_self.ge.trans
      ((TopologicalSpace.Opens.map hA.fromSpec.base).map (homOfLE hV)).le
  have h1 : ⊤ ≤ (hA.fromSpec ≫ ψ) ⁻¹ᵁ U := h0
  have h2 : ⊤ ≤ (spMap φ ≫ hA.fromSpec ≫ ψ) ⁻¹ᵁ U := fun x _ => h1 (Set.mem_univ _)
  have hc' : spMap ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom) ≫
      spMap φ ≫ hA.fromSpec ≫ ψ = spMap φ ≫ hA.fromSpec ≫ ψ := hc
  have hcongr : ∀ (w₁ w₂ : Sp (DualNumber k) ⟶ Y), w₁ = w₂ → ∀ (e₁ : ⊤ ≤ w₁ ⁻¹ᵁ U)
      (e₂ : ⊤ ≤ w₂ ⁻¹ᵁ U), w₁.appLE U ⊤ e₁ = w₂.appLE U ⊤ e₂ := by
    rintro _ _ rfl _ _
    rfl
  have A := ev_comp ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
    U (spMap φ ≫ hA.fromSpec ≫ ψ) h2 (hc'.symm ▸ h2)
  rw [hcongr _ _ hc' _ h2] at A
  have B := ev_comp φ U (hA.fromSpec ≫ ψ) h1 h2
  have C := fromSpec_ev hA hV h0
  have B' : (spMap φ ≫ hA.fromSpec ≫ ψ).appLE U ⊤ h2 ≫
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom =
      ψ.app U ≫ X.presheaf.map (homOfLE hV).op ≫ CommRingCat.ofHom φ := by
    rw [B, Scheme.Hom.comp_appLE, Category.assoc, Category.assoc]
    erw [← Category.assoc (hA.fromSpec.appLE _ _ _), C]
  have A' := ConcreteCategory.congr_hom A t
  rw [B'] at A'
  have hxx : φ (X.presheaf.map (homOfLE hV).op (ψ.app U t)) =
      ((algebraMap k (DualNumber k)).comp (TrivSqZeroExt.fstHom k k k).toRingHom)
        (φ (X.presheaf.map (homOfLE hV).op (ψ.app U t))) := by
    simpa using A'
  rw [hxx, RingHom.comp_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.snd_inl]

/- English proof (translation)
Introduce `p _ k _ _ hk X Y _ s _ ψ hψ U t`. Establish `hp : (p : Γ(X, ⊤)) = 0`. Establish `h` using `congrArg (GlobalTheory.CechDR.secMap s ⊤).hom hk`. Rewrite `h` using `[map_natCast, map_zero]`. Then use the resulting hypothesis. Use `rootGlue p X hp (ψ ⁻¹ᵁ U) (ψ.app U t) ?_` and prove the remaining obligations.

Introduce `V hV hA`. Set `V' : X.affineOpens` to `⟨V, hA⟩`. Use `haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s V) := by`. Establish `hi : Smooth hA.fromSpec` using `inferInstance`. Establish `h0 : Smooth (hA.fromSpec ≫ s)` using `MorphismProperty.comp_mem _ _ _ hi ‹Smooth s›`.

Establish `h1 : Smooth (GlobalTheory.CechDR.affPt s V' ≫ s)` using `h0`. Rewrite `h1` using `[GlobalTheory.CechDR.affPt_w]`. Conclude with `RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h1)`. Use `haveI : _root_.IsReduced (GlobalTheory.CechDR.Sec s V) := IsReduced.component_reduced V`. Establish `hD` using `dz1 k (GlobalTheory.CechDR.Sec s V) (X.presheaf.map (homOfLE hV).op (ψ.app U t)) ?_`.

Conclude with `GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen p k hk X s V' _ hD`. Introduce `v`. Establish `hw : (spMap v.toRingHom ≫ hA.fromSpec) ≫ s = spMap (algebraMap k (DualNumber k))`. Express the relevant statement in the definitionally equal form `spMap v.toRingHom ≫ GlobalTheory.CechDR.affPt s V' ≫ s = _`. Rewrite using `[GlobalTheory.CechDR.affPt_w, ← Geo.Tor.spMap_comp]`.

Conclude with `congrArg spMap v.comp_algebraMap`. Establish `hc : IsConst (spMap v.toRingHom ≫ hA.fromSpec ≫ ψ)`. Use `hψ _ hw using 1` and compare the differences between its conclusion and the goal. Conclude with `(Category.assoc _ _ _).symm`. Conclude with `snd_zero ψ hV hA v.toRingHom hc t`.
-/
theorem UpperTheory.Gal.Ord.dzero :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (X Y : Scheme.{0}) [IsIntegral X] (s : X ⟶ Sp k) [Smooth s] (ψ : X ⟶ Y),
      (∀ v : Sp (DualNumber k) ⟶ X, v ≫ s = spMap (algebraMap k (DualNumber k)) → IsConst (v ≫ ψ)) →
      ∀ (U : Y.Opens) (t : Γ(Y, U)), ∃ r : Γ(X, ψ ⁻¹ᵁ U), r ^ p = ψ.app U t := by
  intro p _ k _ _ hk X Y _ s _ ψ hψ U t
  have hp : (p : Γ(X, ⊤)) = 0 := by
    have h := congrArg (GlobalTheory.CechDR.secMap s ⊤).hom hk
    rwa [map_natCast, map_zero] at h
  refine rootGlue p X hp (ψ ⁻¹ᵁ U) (ψ.app U t) ?_
  intro V hV hA
  let V' : X.affineOpens := ⟨V, hA⟩
  haveI hsm : Algebra.Smooth k (GlobalTheory.CechDR.Sec s V) := by
    have hi : Smooth hA.fromSpec := inferInstance
    have h0 : Smooth (hA.fromSpec ≫ s) := MorphismProperty.comp_mem _ _ _ hi ‹Smooth s›
    have h1 : Smooth (GlobalTheory.CechDR.affPt s V' ≫ s) := h0
    rw [GlobalTheory.CechDR.affPt_w] at h1
    exact RingHom.smooth_algebraMap.mp (HasRingHomProperty.Spec_iff.mp h1)
  haveI : _root_.IsReduced (GlobalTheory.CechDR.Sec s V) := IsReduced.component_reduced V
  have hD := dz1 k (GlobalTheory.CechDR.Sec s V) (X.presheaf.map (homOfLE hV).op (ψ.app U t)) ?_
  · exact GlobalTheory.T.exists_pow_eq_of_kaehlerD_eq_zero_smooth_affineOpen p k hk X s V' _ hD
  intro v
  have hw : (spMap v.toRingHom ≫ hA.fromSpec) ≫ s = spMap (algebraMap k (DualNumber k)) := by
    change spMap v.toRingHom ≫ GlobalTheory.CechDR.affPt s V' ≫ s = _
    rw [GlobalTheory.CechDR.affPt_w, ← Geo.Tor.spMap_comp]
    exact congrArg spMap v.comp_algebraMap
  have hc : IsConst (spMap v.toRingHom ≫ hA.fromSpec ≫ ψ) := by
    convert hψ _ hw using 1
    exact (Category.assoc _ _ _).symm
  exact snd_zero ψ hV hA v.toRingHom hc t
