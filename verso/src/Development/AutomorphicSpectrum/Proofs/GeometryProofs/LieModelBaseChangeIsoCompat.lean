import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductPullbackIffStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GMove

section Ring

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_algebraMap (f : R →+* S) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp f := by
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by simp [dualMap]`.
-/
theorem fstHom_dualMap (f : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

/- English proof (translation)
Apply the tactic sequence `ext x <;> simp [dualMap]`.
-/
theorem dualMap_comp (f : R →+* S) (g : S →+* T) : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem specMap_comp (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

end Ring

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

/- English proof (translation)
Use `h.map e.inv.continuous` as an intermediate fact. Simplify using `using this`.
-/
theorem specializes_of_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

/- English proof (translation)
Establish `e` using `Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2`. Establish `e2` using `congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e`. Establish `e3` using `Scheme.stalkClosedPointTo_comp ξ' g`. Establish `e4` using `congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3`. Conclude with `e2.symm.trans e4.symm`.
-/
theorem genMap_stalkMap_eq (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

/- English proof (translation)
Establish `hw` using `h.1.w`. Set `x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G` to `Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by`. Rewrite using `[Category.assoc, hw, ← Category.assoc, Over.w]`. Use the proof step `simp)`. Establish `hm` using `h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl`.

Establish `hx : x₀ * x₀ = x₀` using `by ext1`. Rewrite using `[hm, _root_.mul_one]`. Both sides reduce to the same expression. Establish `h1 : x₀ = 1` using `by simpa using hx`. Establish `h2` using `congrArg (fun u => u.left) h1`.

Simplify `h2` using `[x₀, Hom.one_def]`.
-/
theorem eta_comp {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left)
    (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw := h.1.w
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  have hm := h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hm, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := by simpa using hx
  have h2 := congrArg (fun u => u.left) h1
  simpa [x₀, Hom.one_def] using h2

end Scheme

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

/- English proof (translation)
Substitute `hξ hz` using the available equality. Introduce and unpack `⟨h, v, ⟨hvt, hve⟩, hvw⟩`. Establish `h' : genPt ξ' ⤳ centre z` using `specializes_of_iso e h`. Express the relevant statement in the definitionally equal form `e.hom (genPt ξ') ⤳ e.hom (centre z) at h`. Express the relevant statement in the definitionally equal form `epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v`.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left = (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt`. Express the relevant statement in the definitionally equal form `(M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫ v.left at hve`. Express the relevant statement in the definitionally equal form `w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw`. Establish `hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv`. Rewrite using `[Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]`.

Establish `hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left`. Rewrite using `[← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]`. Establish `hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z))) (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))` using `Over.w v`. Establish `hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) = X'.fromSpecStalk (centre z) ≫ e.hom` using `Scheme.SpecMap_stalkMap_fromSpecStalk e.hom`. Establish `k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z))) (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z) …`.

Rewrite using `[specMap_comp, dualMap_algebraMap, ← specMap_comp]`. Both sides reduce to the same expression. Set `v' : epsAt (R` to `X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' := Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z)) …`. Rewrite using `[Category.assoc, hφ, reassoc_of% hv]`. Use `show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z))) (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _`.

Rewrite using `[← Category.assoc, ← Category.assoc]`. Use `erw [k1]`. Use `erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]`. Use the proof step `rfl)`. Establish `hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv` using `rfl`.

Use `⟨h', v', ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left`. Simplify using `[Hom.one_def]`. Establish `e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left = X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left`. Rewrite using `[hvt]`.

Simplify using `[Hom.one_def]`. Establish `k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) = Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.m …`. Rewrite using `[specMap_comp, fstHom_dualMap, ← specMap_comp]`. Both sides reduce to the same expression. Use `show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left = (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left`.

Rewrite using `[hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]`. Both sides reduce to the same expression. Establish `k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩)))`. Establish `hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom = genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩` using `RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)`. Rewrite using `[specMap_comp, ← dualMap_comp, hg]`.

Use `show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left`. Rewrite using `[(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]`. Conclude with `Category.assoc _ _ _`. Establish `k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫ Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom))`. Use `(specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_` and prove the remaining obligations.

Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Conclude with `congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm`. Rewrite using `[(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]`. Use `erw [Category.assoc, Category.assoc]`.
-/
theorem valAt_up (e : X' ≅ X) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (φ : G'.left ≅ G.left)
    (hw : φ.hom ≫ G.hom = G'.hom ≫ e.hom) (hη : η[G'].left ≫ φ.hom = e.hom ≫ η[G].left)
    {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (hξ : ξ' ≫ e.hom = ξ)
    (hpt : ∀ v, (M'.pt v).left ≫ φ.hom = (M.pt v).left)
    {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ e.hom = z₀) {b : V} {w : epsAt z₀ ⟶ G} {w' : epsAt z ⟶ G'}
    (hww : w'.left ≫ φ.hom = w.left) : M.ValAt z₀ b w → M'.ValAt z b w' := by
  subst hξ hz
  rintro ⟨h, v, ⟨hvt, hve⟩, hvw⟩
  have h' : genPt ξ' ⤳ centre z := specializes_of_iso e h
  change e.hom (genPt ξ') ⤳ e.hom (centre z) at h
  change epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
      (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
      (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt
  change (M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫
      v.left at hve
  change w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw
  have hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left := by
    rw [← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]
  have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
      (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z)) := Over.w v
  have hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) =
      X'.fromSpecStalk (centre z) ≫ e.hom := Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
  have k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ Spec.map (e.hom.stalkMap (centre z)) := by
    rw [specMap_comp, dualMap_algebraMap, ← specMap_comp]
    rfl
  let v' : epsAt (R := X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by
      show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ X'.fromSpecStalk (centre z)
      rw [Category.assoc, hφ, reassoc_of% hv]
      show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _
      rw [← Category.assoc, ← Category.assoc]
      erw [k1]
      erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]
      rfl)
  have hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv := rfl
  refine ⟨h', v', ⟨?_, ?_⟩, ?_⟩
  · have e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left := by
      simp [Hom.one_def]
    have e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
        X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left := by
      rw [hvt]
      simp [Hom.one_def]
    have k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z)))).toRingHom) := by
      rw [specMap_comp, fstHom_dualMap, ← specMap_comp]
      rfl
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left =
        (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left
    rw [hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]
    rfl
  · have k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) := by
      have hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom =
          genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩ :=
        RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)
      rw [specMap_comp, ← dualMap_comp, hg]
    show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left
    rw [(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]
    exact Category.assoc _ _ _
  · have k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) := by
      refine (specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_
      rw [Scheme.stalkClosedPointTo_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm
    rw [(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]
    erw [Category.assoc, Category.assoc]

end Move

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

/- English proof (translation)
Introduce `E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ`. Use `haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso`. Set `φ : t'.G.left ≅ t.G.left` to `asIso k.φ`. Establish `hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom` using `k.cart.1.w`. Establish `hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left` using `eta_comp e.hom k.φ k.cart`.

Establish `hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom` using `by show φ.inv ≫ _ = _ ≫ e.inv`. Rewrite using `[Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]`. Establish `hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left` using `by show _ ≫ φ.inv = e.inv ≫ _`. Rewrite using `[Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]`. Establish `hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left` using `fun v => by show _ ≫ φ.inv = _`.

Rewrite using `[← hpt v, Category.assoc]`. Use `erw [φ.hom_inv_id]`. Conclude with `Category.comp_id _`. Establish `hξ' : ξ ≫ e.symm.hom = ξ'` using `by rw [← hξ]; simp`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨v', hval, hip⟩`. Set `v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G)` to `fun i => Over.homMk ((v' i).left ≫ k.φ) (by`. Establish `h1` using `Over.w (v' i)`. Rewrite using `[Category.assoc, k.cart.1.w, ← Category.assoc, h1]`. Simplify using `[epsAt])`.

Use `⟨v, fun i => ?_, fun p q => ?_⟩` and prove the remaining obligations. Use `valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i) show ((v' i).left ≫ k.φ) ≫ φ.inv = _` and prove the remaining obligations. Simplify using `[φ]`. Conclude with `(GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)`. Introduce and unpack `⟨v, hval, hip⟩`.

Set `v' : Fin r → (epsAt z ⟶ t'.G)` to `fun i => Over.homMk ((v i).left ≫ φ.inv) (by`. Establish `h1` using `Over.w (v i)`. Rewrite using `[Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]`. Simplify using `[epsAt])`. Establish `hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left` using `fun i => by show ((v i).left ≫ φ.inv) ≫ φ.hom = _`.

Simplify using the standard rewrite rules. Use `⟨v', fun i => ?_, fun p q => ?_⟩` and prove the remaining obligations. Conclude with `valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)`. Conclude with `(GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)`.
-/
theorem gramAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ
  haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso
  let φ : t'.G.left ≅ t.G.left := asIso k.φ
  have hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom := k.cart.1.w
  have hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left := eta_comp e.hom k.φ k.cart
  have hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom := by
    show φ.inv ≫ _ = _ ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left := by
    show _ ≫ φ.inv = e.inv ≫ _
    rw [Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]
  have hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left := fun v => by
    show _ ≫ φ.inv = _
    rw [← hpt v, Category.assoc]
    erw [φ.hom_inv_id]
    exact Category.comp_id _
  have hξ' : ξ ≫ e.symm.hom = ξ' := by rw [← hξ]; simp
  constructor
  · rintro ⟨v', hval, hip⟩
    let v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G) := fun i => Over.homMk ((v' i).left ≫ k.φ) (by
      have h1 := Over.w (v' i)
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, h1]
      simp [epsAt])
    refine ⟨v, fun i => ?_, fun p q => ?_⟩
    · refine valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i)
      show ((v' i).left ≫ k.φ) ≫ φ.inv = _
      simp [φ]
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)
  · rintro ⟨v, hval, hip⟩
    let v' : Fin r → (epsAt z ⟶ t'.G) := fun i => Over.homMk ((v i).left ≫ φ.inv) (by
      have h1 := Over.w (v i)
      rw [Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]
      simp [epsAt])
    have hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left := fun i => by
      show ((v i).left ≫ φ.inv) ≫ φ.hom = _
      simp
    refine ⟨v', fun i => ?_, fun p q => ?_⟩
    · exact valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)

end GlobalTheory.CompanionTheory.Ar.GMove
