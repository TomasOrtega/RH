import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FirstOrderPointsCommuteStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SqAdd

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S : Scheme.{0}} {C B : Type} [CommRing C] [CommRing B]

/- English proof (translation)
Use `RingHom.ext fun c => ?_` and prove the remaining obligations. Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem dualMap_comp_algebraMap (φ : C →+* B) :
    (dualMap φ).comp (algebraMap C (DualNumber C)) = (algebraMap B (DualNumber B)).comp φ := by
  refine RingHom.ext fun c => ?_
  apply TrivSqZeroExt.ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Use `RingHom.ext fun c => ?_` and prove the remaining obligations. Simplify using `[dualMap]`.
-/
theorem fst_comp_dualMap (φ : C →+* B) :
    (TrivSqZeroExt.fstHom B B B).toRingHom.comp (dualMap φ) =
      φ.comp (TrivSqZeroExt.fstHom C C C).toRingHom := by
  refine RingHom.ext fun c => ?_
  simp [dualMap]

def epsIdeal (B : Type) [CommRing B] : Ideal (DualNumber B) :=
  RingHom.ker (TrivSqZeroExt.fstHom B B B).toRingHom

/- English proof (translation)
Rewrite using `[pow_two, eq_bot_iff, Ideal.mul_le]`. Introduce `a ha b hb`. Establish `ha' : a.fst = 0` using `ha`. Establish `hb' : b.fst = 0` using `hb`. Rewrite using `[Ideal.mem_bot]`.

Apply the tactic sequence `apply TrivSqZeroExt.ext <;> simp [ha', hb']`.
-/
theorem epsIdeal_sq : epsIdeal B ^ 2 = ⊥ := by
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  have ha' : a.fst = 0 := ha
  have hb' : b.fst = 0 := hb
  rw [Ideal.mem_bot]
  apply TrivSqZeroExt.ext <;> simp [ha', hb']

def redMap (B : Type) [CommRing B] : B →+* DualNumber B ⧸ epsIdeal B :=
  (Ideal.Quotient.mk (epsIdeal B)).comp (algebraMap B (DualNumber B))

/- English proof (translation)
Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)`. Rewrite using `[Ideal.Quotient.eq]`. Express the relevant statement in the definitionally equal form `(TrivSqZeroExt.fstHom B B B).toRingHom _ = 0`. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem mk_eq_redMap_comp :
    Ideal.Quotient.mk (epsIdeal B) = (redMap B).comp (TrivSqZeroExt.fstHom B B B).toRingHom := by
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk (epsIdeal B) a = Ideal.Quotient.mk (epsIdeal B) (algebraMap B (DualNumber B) a.fst)
  rw [Ideal.Quotient.eq]
  change (TrivSqZeroExt.fstHom B B B).toRingHom _ = 0
  simp [TrivSqZeroExt.algebraMap_eq_inl]

def restr (φ : C →+* B) (y : Sp C ⟶ S) :
    Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ epsAt y :=
  Over.homMk (spMap (dualMap φ)) (by
    change spMap _ ≫ spMap _ ≫ y = spMap _ ≫ spMap _ ≫ y
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (dualMap_comp_algebraMap φ))

/- English proof (translation)
Establish `hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B))`. Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Establish `hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) = spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom`. Rewrite using `[← Spec.map_comp]`.

Conclude with `congrArg (fun f => spMap f) mk_eq_redMap_comp`. Establish `hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) = spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Conclude with `congrArg (fun f => spMap f) (fst_comp_dualMap φ)`. Set `T : Over S` to `Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)`.

Set `m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)` to `Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl`. Set `m₂ : T ⟶ Over.mk y` to `Over.homMk (spMap (redMap B) ≫ spMap φ) (by`. Express the relevant statement in the definitionally equal form `(spMap (redMap B) ≫ spMap φ) ≫ y = _`. Rewrite using `[hred]`. Simplify using `[T])`.

Establish `c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G)`. Rewrite using `[MonObj.comp_one, MonObj.comp_one]`. Establish `c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left = (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left` using `congrArg CommaMorphism.left c`. Rewrite using `[c']`. Establish `tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left` using `tv`.

Rewrite using `[← tv']`. Express the relevant statement in the definitionally equal form `spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _`. Rewrite using `[hmk]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% hfst]`.
-/
theorem red_restr (G : Over S) [GrpObj G] (φ : C →+* B) (y : Sp C ⟶ S) (v : epsAt y ⟶ G) (tv : IsTanAt G y v) :
    spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ (restr φ y ≫ v).left =
      spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
        (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left := by
  have hred : spMap (redMap B) = spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (algebraMap B (DualNumber B)) := by
    rw [← Spec.map_comp]; rfl
  have hmk : spMap (Ideal.Quotient.mk (epsIdeal B)) =
      spMap (redMap B) ≫ spMap (TrivSqZeroExt.fstHom B B B).toRingHom := by
    rw [← Spec.map_comp]
    exact congrArg (fun f => spMap f) mk_eq_redMap_comp
  have hfst : spMap (TrivSqZeroExt.fstHom B B B).toRingHom ≫ spMap (dualMap φ) =
      spMap φ ≫ spMap (TrivSqZeroExt.fstHom C C C).toRingHom := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => spMap f) (fst_comp_dualMap φ)
  let T : Over S := Over.mk (spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
    spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y)
  let m₁ : T ⟶ Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) :=
    Over.homMk (spMap (Ideal.Quotient.mk (epsIdeal B))) rfl
  let m₂ : T ⟶ Over.mk y := Over.homMk (spMap (redMap B) ≫ spMap φ) (by
    change (spMap (redMap B) ≫ spMap φ) ≫ y = _
    rw [hred]
    simp [T])
  have c : m₁ ≫ (1 : _ ⟶ G) = m₂ ≫ (1 : _ ⟶ G) := by
    rw [MonObj.comp_one, MonObj.comp_one]
  have c' : spMap (Ideal.Quotient.mk (epsIdeal B)) ≫
      (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      (spMap (redMap B) ≫ spMap φ) ≫ (1 : Over.mk y ⟶ G).left := congrArg CommaMorphism.left c
  rw [c']
  have tv' : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ v.left = (1 : Over.mk y ⟶ G).left := tv
  rw [← tv']
  change spMap (Ideal.Quotient.mk (epsIdeal B)) ≫ spMap (dualMap φ) ≫ v.left = _
  rw [hmk]
  simp only [Category.assoc]
  rw [reassoc_of% hfst]

/- English proof (translation)
Introduce `z _` and use `by change k (p z) ∈ U exact h (show p z ∈ (⊤ : Y.Opens) from trivial)`.
-/
theorem top_le_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ k ⁻¹ᵁ U) :
    ⊤ ≤ (p ≫ k) ⁻¹ᵁ U := fun z _ => by
  change k (p z) ∈ U
  exact h (show p z ∈ (⊤ : Y.Opens) from trivial)

/- English proof (translation)
Substitute `e` using the available equality. Establish `hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens)` using `by simp`. Establish `hp : p.appTop = p.appLE ⊤ ⊤ hle` using `Scheme.Hom.app_eq_appLE ..`. Establish `: k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h'`. Rewrite using `[hp]`.

Conclude with `Scheme.Hom.appLE_comp_appLE ..`. Rewrite using `[← this]`. Both sides reduce to the same expression.
-/
theorem appTop_appLE {X Y Z : Scheme.{0}} (p : X ⟶ Y) (k : Y ⟶ Z) (k' : X ⟶ Z) (e : k' = p ≫ k) (U : Z.Opens)
    (h : ⊤ ≤ k ⁻¹ᵁ U) (h' : ⊤ ≤ k' ⁻¹ᵁ U) (s : Γ(Z, U)) :
    p.appTop.hom ((k.appLE U ⊤ h).hom s) = (k'.appLE U ⊤ h').hom s := by
  subst e
  have hle : (⊤ : X.Opens) ≤ p ⁻¹ᵁ (⊤ : Y.Opens) := by simp
  have hp : p.appTop = p.appLE ⊤ ⊤ hle := Scheme.Hom.app_eq_appLE ..
  have : k.appLE U ⊤ h ≫ p.appTop = (p ≫ k).appLE U ⊤ h' := by
    rw [hp]
    exact Scheme.Hom.appLE_comp_appLE ..
  rw [← this]
  rfl

/- English proof (translation)
Establish `hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left` using `congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm`. Establish `hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left = spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left` using `congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm`. Establish `hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U` using `top_le_comp (spMap (dualMap φ)) v.left U hv`. Establish `hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U` using `top_le_comp (spMap (dualMap φ)) w.left U hw`. Establish `hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U`.

Rewrite using `[hmul]`. Conclude with `top_le_comp _ _ U hvw`. Establish `hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U`. Rewrite using `[hone]`. Conclude with `top_le_comp _ _ U h1`.

Establish `key` using `GlobalTheory.T.first_order_points_commute S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B) epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s`. Rewrite using `[map_add, map_add, appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s, appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s, appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s, appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw …`. Conclude with `key`.
-/
theorem tan_local (G : Over S) [GrpObj G] [IsLocalRing B] (φ : C →+* B) (y : Sp C ⟶ S) (v w : epsAt y ⟶ G)
    (tv : IsTanAt G y v) (tw : IsTanAt G y w) (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U)
    (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U) (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)) :
    (spMap (dualMap φ)).appTop.hom
        (((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s) =
      (spMap (dualMap φ)).appTop.hom ((v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s) := by
  have hmul : ((restr φ y ≫ v) * (restr φ y ≫ w)).left = spMap (dualMap φ) ≫ (v * w).left :=
    congrArg CommaMorphism.left (MonObj.comp_mul (restr φ y) v w).symm
  have hone : (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left =
      spMap (dualMap φ) ≫ (1 : epsAt y ⟶ G).left :=
    congrArg CommaMorphism.left (MonObj.comp_one (restr φ y)).symm
  have hxv : ⊤ ≤ (restr φ y ≫ v).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) v.left U hv
  have hxw : ⊤ ≤ (restr φ y ≫ w).left ⁻¹ᵁ U := top_le_comp (spMap (dualMap φ)) w.left U hw
  have hxvw : ⊤ ≤ ((restr φ y ≫ v) * (restr φ y ≫ w)).left ⁻¹ᵁ U := by
    rw [hmul]; exact top_le_comp _ _ U hvw
  have hx1 : ⊤ ≤ (1 : Over.mk (spMap (algebraMap B (DualNumber B)) ≫ spMap φ ≫ y) ⟶ G).left ⁻¹ᵁ U := by
    rw [hone]; exact top_le_comp _ _ U h1
  have key := GlobalTheory.T.first_order_points_commute S G B (spMap φ ≫ y) (DualNumber B) (algebraMap B (DualNumber B)) (epsIdeal B)
    epsIdeal_sq (restr φ y ≫ v) (restr φ y ≫ w) (red_restr G φ y v tv) (red_restr G φ y w tw) U hxv hxw hxvw hx1 s
  rw [map_add, map_add,
    appTop_appLE (spMap (dualMap φ)) _ _ hmul U hvw hxvw s,
    appTop_appLE (spMap (dualMap φ)) _ _ hone U h1 hx1 s,
    appTop_appLE (spMap (dualMap φ)) v.left (restr φ y ≫ v).left rfl U hv hxv s,
    appTop_appLE (spMap (dualMap φ)) w.left (restr φ y ≫ w).left rfl U hw hxw s]
  exact key

/- English proof (translation)
Simplify using `[dualMap]`.
-/
theorem dualMap_fst (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).fst = φ a.fst := by
  simp [dualMap]

/- English proof (translation)
Simplify using `[dualMap]`.
-/
theorem dualMap_snd (φ : C →+* B) (a : DualNumber C) : (dualMap φ a).snd = φ a.snd := by
  simp [dualMap]

/- English proof (translation)
Establish `h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r = algebraMap C (Localization.AtPrime q) r') → r = r'`. Introduce `r r' hr`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_localization _ fun q hq => ?_` and prove the remaining obligations. Rewrite using `[map_sub, hr q, sub_self]`.

Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Conclude with `h0 _ _ fun q _ => by`. Rewrite using `[← dualMap_fst, ← dualMap_fst, h q]`. Conclude with `h0 _ _ fun q _ => by`. Rewrite using `[← dualMap_snd, ← dualMap_snd, h q]`.
-/
theorem dual_eq_of_localization (a b : DualNumber C)
    (h : ∀ (q : Ideal C) [q.IsMaximal], dualMap (algebraMap C (Localization.AtPrime q)) a =
      dualMap (algebraMap C (Localization.AtPrime q)) b) : a = b := by
  have h0 : ∀ r r' : C, (∀ (q : Ideal C) [q.IsMaximal], algebraMap C (Localization.AtPrime q) r =
      algebraMap C (Localization.AtPrime q) r') → r = r' := by
    intro r r' hr
    rw [← sub_eq_zero]
    refine eq_zero_of_localization _ fun q hq => ?_
    rw [map_sub, hr q, sub_self]
  apply TrivSqZeroExt.ext
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_fst, ← dualMap_fst, h q]
  · exact h0 _ _ fun q _ => by
      rw [← dualMap_snd, ← dualMap_snd, h q]

/- English proof (translation)
Establish `hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom` using `(Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective`. Use `hinj (dual_eq_of_localization _ _ fun q _ => ?_)` and prove the remaining obligations. Establish `e` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))`. Establish `e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q)) ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) = (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))). …` using `fun c => (congrArg (fun f => f.hom c) e).symm`. Rewrite using `[e', e', h q]`.
-/
theorem gamma_eq_of_localization (a b : Γ(Sp (DualNumber C), ⊤))
    (h : ∀ (q : Ideal C) [q.IsMaximal], (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom a =
      (spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom b) : a = b := by
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom :=
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).commRingCatIsoToRingEquiv.injective
  refine hinj (dual_eq_of_localization _ _ fun q _ => ?_)
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (dualMap (algebraMap C (Localization.AtPrime q))))
  have e' : ∀ c : Γ(Sp (DualNumber C), ⊤), dualMap (algebraMap C (Localization.AtPrime q))
        ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber C))).hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (Localization.AtPrime q)))).hom
        ((spMap (dualMap (algebraMap C (Localization.AtPrime q)))).appTop.hom c) := fun c =>
    (congrArg (fun f => f.hom c) e).symm
  rw [e', e', h q]

/- English proof (translation)
Introduce `S G _ C _ y v w tv tw U hv hw hvw h1 s`. Conclude with `gamma_eq_of_localization _ _ fun q _ => tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s`.
-/
theorem tan_mul_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (C : Type) [CommRing C] (y : Sp C ⟶ S)
    (v w : epsAt y ⟶ G), IsTanAt G y v → IsTanAt G y w →
    ∀ (U : G.left.Opens) (hv : ⊤ ≤ v.left ⁻¹ᵁ U) (hw : ⊤ ≤ w.left ⁻¹ᵁ U) (hvw : ⊤ ≤ (v * w).left ⁻¹ᵁ U)
      (h1 : ⊤ ≤ (1 : epsAt y ⟶ G).left ⁻¹ᵁ U) (s : Γ(G.left, U)),
      ((v * w).left.appLE U ⊤ hvw).hom s + ((1 : epsAt y ⟶ G).left.appLE U ⊤ h1).hom s =
        (v.left.appLE U ⊤ hv).hom s + (w.left.appLE U ⊤ hw).hom s := by
  intro S G _ C _ y v w tv tw U hv hw hvw h1 s
  exact gamma_eq_of_localization _ _ fun q _ =>
    tan_local G (algebraMap C (Localization.AtPrime q)) y v w tv tw U hv hw hvw h1 s

end GlobalTheory.CompanionTheory.Ar.SqAdd
