import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatGlueLatIffDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.GlueVecLattice

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {u : D.what₂.Word}

/- English proof (translation)
Rewrite using `[vA_add, vA_smul, mA_mulVec_vA]`.
-/
theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

/- English proof (translation)
Take `⟨a, ha⟩` from `h1`. Use `(mem_glueLat _).2 ⟨_, h2, a, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _`. Rewrite using `[ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_of_coords {L₀ : Lat X} {x₀ x : X.V} {t : D.host.E}
    (h1 : t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (h2 : Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ := by
  obtain ⟨a, ha⟩ := h1
  refine (mem_glueLat _).2 ⟨_, h2, a, ?_⟩
  change _ = _ + algebraMap (𝓞 D.host.E) D.host.E a • _
  rw [ha, map_sub, map_smul, smul_add, smul_smul, mul_assoc, mul_inv_cancel₀ (Tu_ne_zero u), mul_one]
  abel

/- English proof (translation)
Take `⟨x₁, hx₁, a, ha, e⟩` from `(mem_hat_glueLat _).1 hy`. Rewrite `e` using `[vA_flat]`. Take `⟨e1, e2⟩` from `flat_inj h e`. Establish `e3 : a = inc D (t * Tu D u)`. Rewrite using `[RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]`.

Use `⟨(inc_mem_iff _).1 (e3 ▸ ha), (inc_mem_hat_iff hL _).1 ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `vA X (x - (t * Tu D u) • x₀) ∈ _`. Establish `e4 : vA X (x - (t * Tu D u) • x₀) = x₁`. Rewrite using `[sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]`. Rewrite using `[e4]` and apply the resulting hypothesis.
-/
theorem coords_of_mem_hat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ x : X.V}
    {t : D.host.E} (hy : vA Y (ι x + t • z) ∈ hat (Formalism.L2.Herm.crdLat Y (glueLat Y X ι z u L₀ x₀))) :
    t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
      Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ := by
  obtain ⟨x₁, hx₁, a, ha, e⟩ := (mem_hat_glueLat _).1 hy
  rw [vA_flat] at e
  obtain ⟨e1, e2⟩ := flat_inj h e
  have e3 : a = inc D (t * Tu D u) := by
    rw [RingHom.map_mul, e2, mul_assoc, inc_inv_mul, mul_one]
  refine ⟨(inc_mem_iff _).1 (e3 ▸ ha), (inc_mem_hat_iff hL _).1 ?_⟩
  change vA X (x - (t * Tu D u) • x₀) ∈ _
  have e4 : vA X (x - (t * Tu D u) • x₀) = x₁ := by
    rw [sub_eq_add_neg, ← neg_smul, vA_add, vA_smul, RingHom.map_neg, ← e3, e1, neg_smul, add_neg_cancel_right]
  rwa [e4]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩`.
-/
theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

/- English proof (translation)
Rewrite using `[flatSp, Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, rfl⟩, b, hb, rfl⟩`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hb`. Conclude with `⟨x, t, rfl⟩`.

Introduce and unpack `⟨x, t, rfl⟩`. Conclude with `⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩`.
-/
theorem mem_flatSp (y : Y.V) : y ∈ flatSp Y X ι z ↔ ∃ (x : X.V) (t : D.host.E), y = ι x + t • z := by
  rw [flatSp, Submodule.mem_sup]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
    exact ⟨x, t, rfl⟩
  · rintro ⟨x, t, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, _, Submodule.mem_span_singleton.2 ⟨t, rfl⟩, rfl⟩

/- English proof (translation)
Use `Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)` and prove the remaining obligations. Establish `e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) = L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Conclude with `⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Express the relevant statement in the definitionally equal form `Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀`. Rewrite using `[LinearEquiv.apply_symm_apply]` and apply the resulting hypothesis. Rewrite using `[e]`.

Conclude with `hL.fg.map _`.
-/
theorem glueLat_fg {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) : (glueLat Y X ι z u L₀ x₀).FG := by
  refine Submodule.FG.sup (Submodule.FG.map _ ?_) (Submodule.fg_span_singleton _)
  have e : L₀.comap ((Formalism.L2.Herm.crd X).toLinearMap.restrictScalars (𝓞 D.host.E)) =
      L₀.map ((Formalism.L2.Herm.crd X).symm.toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    ext x
    constructor
    · intro hx
      exact ⟨_, hx, (Formalism.L2.Herm.crd X).symm_apply_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      change Formalism.L2.Herm.crd X ((Formalism.L2.Herm.crd X).symm y) ∈ L₀
      rwa [LinearEquiv.apply_symm_apply]
  rw [e]
  exact hL.fg.map _

/- English proof (translation)
Establish `h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V)`. Introduce `x`. Take `⟨y, rfl⟩` from `(Formalism.L2.Herm.crd X).symm.surjective x`. Establish `hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E))` using `hL.span_eq_top ▸ Submodule.mem_top`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Conclude with `Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)`. Consider the case `zero => rw [map_zero, map_zero]`. Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add, map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul, map_smul]`. Conclude with `Submodule.smul_mem _ c ha`. Use `le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_` and prove the remaining obligations. Take `⟨x, -, a, rfl⟩` from `(mem_glueLat y).1 hy`.

Use `(mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, smul_add, smul_smul]`. Normalize the expressions using the abelian group laws. Take `⟨x, t, rfl⟩` from `(mem_flatSp y).1 hy`. Use `add_mem (h1 x) (Submodule.smul_mem _ t ?_)` and prove the remaining obligations.

Establish `h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V)` using `Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)`. Establish `h3` using `Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))`. Rewrite `h3` using `[add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul]`. Then use the resulting hypothesis.
-/
theorem span_glueLat {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) = flatSp Y X ι z := by
  have h1 : ∀ x : X.V, ι x ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) := by
    intro x
    obtain ⟨y, rfl⟩ := (Formalism.L2.Herm.crd X).symm.surjective x
    have hy : y ∈ Submodule.span D.host.E (L₀ : Set (Fin X.rank → D.host.E)) := hL.span_eq_top ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem y hy =>
      exact Submodule.subset_span ((mem_glueLat _).2 ⟨_, by rwa [LinearEquiv.apply_symm_apply], 0, by simp⟩)
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul, map_smul]; exact Submodule.smul_mem _ c ha
  refine le_antisymm (Submodule.span_le.2 fun y hy => ?_) fun y hy => ?_
  · obtain ⟨x, -, a, rfl⟩ := (mem_glueLat y).1 hy
    refine (mem_flatSp _).2 ⟨x + (a : D.host.E) • x₀, a * (Tu D u)⁻¹, ?_⟩
    rw [map_add, map_smul, smul_add, smul_smul]
    abel
  · obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
    refine add_mem (h1 x) (Submodule.smul_mem _ t ?_)
    have h2 : (Tu D u)⁻¹ • z + ι x₀ ∈ Submodule.span D.host.E (glueLat Y X ι z u L₀ x₀ : Set Y.V) :=
      Submodule.subset_span ((mem_glueLat _).2 ⟨0, by simp, 1, by simp⟩)
    have h3 := Submodule.smul_mem _ (Tu D u) (sub_mem h2 (h1 x₀))
    rwa [add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (Tu_ne_zero u), one_smul] at h3

/- English proof (translation)
Use `⟨glueLat_fg hL x₀, span_glueLat hL x₀, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, t, rfl⟩` from `(mem_flatSp y).1 hy`. Establish `key` using `mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)`. Rewrite `key` using `[← vA_flat]`. Prove the components needed by the constructor for the conclusion.

Introduce `hm x' hx'`. Rewrite using `[← inc_mem_iff, ← hA_vA]`. Conclude with `key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')`. Introduce `H`. Establish `h1` using `coords_of_mem_hat h hL (key.2 (hA_mem_of_forall ?_))`.

Conclude with `mem_of_coords h1.1 h1.2`. Introduce and unpack `_ ⟨x', hx', rfl⟩`. Express the relevant statement in the definitionally equal form `hA Y (vA Y x') _ ∈ _`. Rewrite using `[hA_vA, inc_mem_iff]`. Conclude with `H x' hx'`.
-/
theorem isSDIn_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) := by
  refine ⟨glueLat_fg hL x₀, span_glueLat hL x₀, fun y hy => ?_⟩
  obtain ⟨x, t, rfl⟩ := (mem_flatSp y).1 hy
  have key := mem_hat_glueLat_iff_dual h hg (vA X x) (inc D t)
  rw [← vA_flat] at key
  constructor
  · intro hm x' hx'
    rw [← inc_mem_iff, ← hA_vA]
    exact key.1 (vA_mem_hat Y hm) _ (vA_mem_hat Y hx')
  · intro H
    have h1 := coords_of_mem_hat h hL (key.2 (hA_mem_of_forall ?_))
    · exact mem_of_coords h1.1 h1.2
    · rintro _ ⟨x', hx', rfl⟩
      change hA Y (vA Y x') _ ∈ _
      rw [hA_vA, inc_mem_iff]
      exact H x' hx'

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Establish `h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀`. Rewrite using `[zero_smul, add_zero]`.

Conclude with `hx`. Establish `h2` using `((mem_iff_coords h hL x 0).1 h1).2`. Rewrite `h2` using `[zero_mul, zero_smul, sub_zero]`. Then use the resulting hypothesis. Introduce `hy`. Take `⟨x, rfl⟩` from `(Formalism.L2.Herm.crd X).surjective y`.

Conclude with `⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩`.
-/
theorem capX_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) (x₀ : X.V) :
    capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : ι x + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
      rw [zero_smul, add_zero]; exact hx
    have h2 := ((mem_iff_coords h hL x 0).1 h1).2
    rwa [zero_mul, zero_smul, sub_zero] at h2
  · intro hy
    obtain ⟨x, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y
    exact ⟨x, (mem_glueLat (ι x)).2 ⟨x, hy, 0, by simp⟩, rfl⟩

/- English proof (translation)
Introduce `a`. Establish `e : a • z = ι 0 + a • z` using `by rw [map_zero, zero_add]`. Rewrite using `[e, mem_iff_coords h hL, ← inc_mem_hat_iff hL, ← inc_mem_iff, ← inc_mem_iff]`. Express the relevant statement in the definitionally equal form `_ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _`. Rewrite using `[zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]`.

Generalize the expression as in `inc D a = b`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Establish `h3` using `hg.pair _ h2`. Rewrite `h3` using `[hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu]`.

Establish `h4` using `mul_mem (cjA_mem h1) hg.norm`. Rewrite `h4` using `[RingHom.map_mul, cjA_inc_Tu]`. Rewrite using `[← cjA_mem_iff]`. Use `neg_mem (add_mem h3 h4) using 1` and compare the differences between its conclusion and the goal. Take the linear combination `(-(cjA D b)) * inc_inv_mul u`.

Introduce `hb`. Use `⟨mul_mem hb (inc_Tu_mem u), ?_⟩` and prove the remaining obligations. Rewrite using `[← neg_mul, ← smul_smul]`. Conclude with `smul_mem_hat (neg_mem hb) hg.mul_mem`.
-/
theorem isPrim_glueLat (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V}
    (hg : IsGlueVec X u L₀ (vA X x₀)) : IsPrim Y z (glueLat Y X ι z u L₀ x₀) := by
  intro a
  have e : a • z = ι 0 + a • z := by rw [map_zero, zero_add]
  rw [e, mem_iff_coords h hL, ← inc_mem_hat_iff hL, ← inc_mem_iff, ← inc_mem_iff]
  change _ ∧ vA X (0 - (a * Tu D u) • x₀) ∈ _ ↔ _
  rw [zero_sub, ← neg_smul, vA_smul, RingHom.map_neg, RingHom.map_mul]
  generalize inc D a = b
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := hg.pair _ h2
    rw [hA_smul_right, RingHom.map_neg, RingHom.map_mul, cjA_inc_Tu] at h3
    have h4 := mul_mem (cjA_mem h1) hg.norm
    rw [RingHom.map_mul, cjA_inc_Tu] at h4
    rw [← cjA_mem_iff]
    convert neg_mem (add_mem h3 h4) using 1
    linear_combination (-(cjA D b)) * inc_inv_mul u
  · intro hb
    refine ⟨mul_mem hb (inc_Tu_mem u), ?_⟩
    rw [← neg_mul, ← smul_smul]
    exact smul_mem_hat (neg_mem hb) hg.mul_mem

/- English proof (translation)
Introduce `_ _ _ _ _ _ h _ x₀ hL hg` and use `⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL hg, capX_glueLat h hL x₀⟩`.
-/
theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL hg, capX_glueLat h hL x₀⟩

end GlobalTheory.GlueVecLattice

end
