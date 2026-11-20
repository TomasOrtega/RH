import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

namespace GlobalTheory.Desc.BCChart

def ev {T : Scheme.{0}} {K : Type} [CommRing K] (f : Sp K ⟶ T) (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (u : Γ(T, O)) : K :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((f.appLE O ⊤ h).hom u)

/- English proof (translation)
Substitute using the available equality. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.
-/
theorem ev_comp {T T' : Scheme.{0}} {K : Type} [CommRing K] (s : Sp K ⟶ T') (g : T' ⟶ T) {O : T.Opens}
    {O' : T'.Opens} (e : O' ≤ g ⁻¹ᵁ O) (h : ⊤ ≤ s ⁻¹ᵁ O') {g' : Sp K ⟶ T} (hg : s ≫ g = g')
    (h' : ⊤ ≤ g' ⁻¹ᵁ O) (u : Γ(T, O)) : ev g' O h' u = ev s O' h ((g.appLE O O' e).hom u) := by
  subst hg
  unfold ev
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem appLE_top_top {A B : Scheme.{0}} (f : A ⟶ B) : f.appLE ⊤ ⊤ le_top = f.appTop := by
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  congr 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem ev_spMap {T : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (θ : A →+* B) (f : Sp A ⟶ T)
    (O : T.Opens) (h : ⊤ ≤ f ⁻¹ᵁ O) (h' : ⊤ ≤ (spMap θ ≫ f) ⁻¹ᵁ O) (u : Γ(T, O)) :
    ev (spMap θ ≫ f) O h' u = θ (ev f O h u) := by
  rw [ev_comp (spMap θ) f h le_top rfl]
  unfold ev
  rw [appLE_top_top, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem fromSpecStalk_top' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U := by
  intro z _
  have hz : X.fromSpecStalk x z ⤳ x := by
    have : X.fromSpecStalk x z ∈ Set.range (X.fromSpecStalk x) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact hz.mem_open U.2 hx

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem fromSpecStalk_appLE' {X : Scheme.{0}} (x : X) (U : X.Opens) (hx : x ∈ U) :
    (X.fromSpecStalk x).appLE U ⊤ (fromSpecStalk_top' x U hx) =
      X.presheaf.germ U x hx ≫ (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv := by
  rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
  simp only [Category.assoc, ← Functor.map_comp]
  have e : ((homOfLE le_top).op ≫ (homOfLE (fromSpecStalk_top' x U hx)).op :
      Opposite.op (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤) = 𝟙 _ := rfl
  rw [e, CategoryTheory.Functor.map_id, Category.comp_id]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem fnOf_eq_ev {X : Scheme.{0}} [IsIntegral X] (O : X.Opens) (hO : genericPoint X ∈ O) (u : Γ(X, O)) :
    fnOf O hO u = ev (gp X) O (fromSpecStalk_top' _ O hO) u := by
  unfold ev gp
  rw [fromSpecStalk_appLE' (genericPoint X) O hO, CommRingCat.comp_apply]
  change _ = (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom _
  rw [Iso.inv_hom_id_apply]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Equip the data with the indicated structure. Extract witnesses or component facts from the available result. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_tensor_fnOf : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (U : X.Opens), IsAffineOpen U → ∀ hg : genericPoint X ∈ U, letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra; letI := ρ.toAlgebra; ∃ β : Γ(X, U) ⊗[R] R₁ →+ Y.functionField, Function.Injective β ∧ (∀ b r, β (b ⊗ₜ[R] r) = θ (GlobalTheory.Cartier.fnOf U hg b) * GlobalTheory.Desc.cst q r) ∧ Set.range β = {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  intro R R₁ _ _ ρ X Y V _ _ p q i _ φ θ H hP U hU hg
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨l, hl1, hl2⟩ := hP
  let W : V.Opens := φ ⁻¹ᵁ U ⊓ (i ≫ q) ⁻¹ᵁ ⊤
  let O : Y.Opens := i ''ᵁ W
  have hmemW : ∀ z : V, z ∈ W ↔ φ z ∈ U := fun z => ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩
  have hmemO : ∀ y : Y, y ∈ O ↔ ∃ z : V, φ z ∈ U ∧ i z = y := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz.1, rfl⟩
    · rintro ⟨z, hz, rfl⟩; exact ⟨z, (hmemW z).2 hz, rfl⟩
  let pt : Sp Y.functionField := IsLocalRing.closedPoint Y.functionField
  have hz1 : i (l pt) = genericPoint Y := by
    rw [← Scheme.Hom.comp_apply, hl1]
    exact Scheme.fromSpecStalk_closedPoint
  have hz2 : φ (l pt) = genericPoint X := by
    rw [← Scheme.Hom.comp_apply, hl2, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecStalk_closedPoint (x := genericPoint X) ▸ congrArg _ (Subsingleton.elim _ _)
  have hO : genericPoint Y ∈ O := (hmemO _).2 ⟨l pt, hz2 ▸ hg, hz1⟩
  let e := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens p (i ≫ q) φ H U hU
  let j : Γ(V, W) →+* Γ(Y, O) := (i.appIso W).inv.hom
  have hj : ∀ s, j ((i.appIso W).hom.hom s) = s := fun s => Iso.hom_inv_id_apply _ _
  have hj' : ∀ s, (i.appIso W).hom.hom (j s) = s := fun s => Iso.inv_hom_id_apply _ _
  refine ⟨((fnOf O hO).comp (j.comp e.toRingHom)).toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (i.appIso W).hom.hom (fnOf_injective O hO hab)
    simp only [RingHom.comp_apply, hj'] at h1
    exact e.injective h1
  · intro b r
    have hlW : ⊤ ≤ l ⁻¹ᵁ W := by
      intro z _
      have hz : z = pt := Subsingleton.elim _ _
      subst hz
      exact (hmemW _).2 (hz2 ▸ hg)
    have hC : ∀ y : Γ(V, W), fnOf O hO (j y) = ev l W hlW y := by
      intro y
      rw [fnOf_eq_ev]
      refine (ev_comp l i (O := O) (O' := W) (i.preimage_image_eq W).ge hlW hl1 _ _).trans ?_
      congr 1
      rw [← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
      have : (homOfLE (le_refl W)).op = 𝟙 (Opposite.op W) := rfl
      erw [this, CategoryTheory.Functor.map_id]
      rfl
    have hX : ⊤ ≤ (spMap θ ≫ gp X) ⁻¹ᵁ U := fun z _ => fromSpecStalk_top' (genericPoint X) U hg (Set.mem_univ (spMap θ z))
    have hYq : ⊤ ≤ (gp Y ≫ q) ⁻¹ᵁ ⊤ := fun _ _ => trivial
    show fnOf O hO (j (e (b ⊗ₜ[R] r))) = _
    rw [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.eTens_tmul, map_mul, map_mul, hC, hC]
    congr 1
    · rw [← ev_comp l φ inf_le_left hlW hl2 hX, ev_spMap θ (gp X) U (fromSpecStalk_top' _ U hg), ← fnOf_eq_ev]
    · unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX cst
      rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, fnOf_eq_ev ⊤ trivial, ← appLE_top_top,
        ← ev_comp l (i ≫ q) le_top hlW (by rw [← Category.assoc, hl1]) hYq,
        ← ev_comp (gp Y) q le_top (fromSpecStalk_top' _ ⊤ trivial) rfl hYq]
  · ext v
    simp only [Set.mem_range, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, rfl⟩ z hz
      exact regAt_fnOf ((hmemO _).2 ⟨z, hz, rfl⟩) hO _
    · intro hv
      obtain ⟨s, hs⟩ := exists_fnOf_eq hO fun y hy => by
        obtain ⟨z, hz, rfl⟩ := (hmemO y).1 hy
        exact hv z hz
      refine ⟨e.symm ((i.appIso W).hom.hom s), ?_⟩
      show fnOf O hO (j (e (e.symm ((i.appIso W).hom.hom s)))) = v
      rw [RingEquiv.apply_symm_apply, hj, hs]

end GlobalTheory.Desc.BCChart
