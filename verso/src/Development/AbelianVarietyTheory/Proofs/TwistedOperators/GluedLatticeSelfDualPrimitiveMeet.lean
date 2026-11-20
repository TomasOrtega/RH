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
Rewrite the conclusion using the stated equalities.
-/
theorem vA_flat (x : X.V) (t : D.host.E) :
    vA Y (ι x + t • z) = mA Y X ι *ᵥ vA X x + inc D t • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.
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
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
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
Supply the required witnesses or components.
-/
theorem mem_iff_coords (h : IsLine Y X ι z u) {L₀ : Lat X} (hL : Submodule.IsLattice D.host.E L₀) {x₀ : X.V} (x : X.V)
    (t : D.host.E) : ι x + t • z ∈ glueLat Y X ι z u L₀ x₀ ↔
      t * Tu D u ∈ (algebraMap (𝓞 D.host.E) D.host.E).range ∧
        Formalism.L2.Herm.crd X (x - (t * Tu D u) • x₀) ∈ L₀ :=
  ⟨fun hy => coords_of_mem_hat h hL (vA_mem_hat Y hy), fun hy => mem_of_coords hy.1 hy.2⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
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
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Proceed by induction.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Replace the chosen expression with an arbitrary variable. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Take a linear combination of the given relations to obtain the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem glueLat_selfDual_prim_cap : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V),
    IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsLattice D.host.E L₀ → IsGlueVec X u L₀ (vA X x₀) →
      IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) ∧ IsPrim Y z (glueLat Y X ι z u L₀ x₀) ∧
        capX Y X ι (glueLat Y X ι z u L₀ x₀) = L₀ :=
  fun _ _ _ _ _ _ h _ x₀ hL hg => ⟨isSDIn_glueLat h hL hg, isPrim_glueLat h hL hg, capX_glueLat h hL x₀⟩

end GlobalTheory.GlueVecLattice

end
