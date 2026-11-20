import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDenominatorRegularStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BaseChangePointsCompatStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Htat.StalkDivisibility

def constSec {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) (d : R) : Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)

section valAt

variable {B C R : Type} [CommRing B] [CommRing C] [CommRing R] {X Y : Scheme.{0}}

/- English proof (translation)
Substitute `e` using the available equality. Both sides reduce to the same expression.
-/
theorem valAt_congr {x y : Spec (CommRingCat.of B) ⟶ X} (e : x = y) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ y ⁻¹ᵁ U) (s : Γ(X, U)) : valAt x U h s = valAt y U h' s := by
  subst e; rfl

/- English proof (translation)
The claim follows from `congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)`.
-/
theorem valAt_res (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

/- English proof (translation)
Simplify using `[valAt]`.
-/
theorem valAt_mul (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

/- English proof (translation)
Simplify using `[valAt]`.
-/
theorem valAt_sub (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

/- English proof (translation)
Simplify using `only [valAt, Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.
-/
theorem valAt_comp (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X) (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U)
    (s : Γ(X, U)) : valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

/- English proof (translation)
Establish `h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop`. Conclude with `(Scheme.Hom.app_eq_appLE _).symm`. Rewrite using `[h]`. Conclude with `congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))`.
-/
theorem specMap_appLE_top (φ : B →+* C) (e) (r : Γ(Spec (CommRingCat.of B), ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom (((Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e).hom r) =
      φ ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom r) := by
  have h : (Spec.map (CommRingCat.ofHom φ)).appLE ⊤ ⊤ e = (Spec.map (CommRingCat.ofHom φ)).appTop := by
    exact (Scheme.Hom.app_eq_appLE _).symm
  rw [h]
  exact congrArg (fun ψ => ψ.hom r) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))

/- English proof (translation)
Establish `e` using `Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)`. Simplify using `only [valAt]`. Rewrite using `[← e]`. Conclude with `specMap_appLE_top κ _ _`.
-/
theorem valAt_spec (κ : B →+* C) (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (Spec.map (CommRingCat.ofHom κ) ≫ x) U h' s = κ (valAt x U h s) := by
  have e := Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom κ)) x U ⊤ ⊤ h (fun _ _ => trivial)
  simp only [valAt]
  rw [← e]
  exact specMap_appLE_top κ _ _

/- English proof (translation)
Establish `e` using `Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h`. Establish `key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤), (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d`. Introduce `y hy e'`. Substitute `hy` using the available equality. Rewrite using `[specMap_appLE_top]`.

Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d`. Rewrite using `[e]`. Conclude with `key _ hx _`.
-/
theorem valAt_const (p : X ⟶ Spec (CommRingCat.of R)) (x : Spec (CommRingCat.of B) ⟶ X) (φ : R →+* B)
    (hx : x ≫ p = Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (d : R) :
    valAt x U h (constSec p U d) = φ d := by
  have e := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  have key : ∀ (y : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R)) (_ : y = Spec.map (CommRingCat.ofHom φ)) (e' : ⊤ ≤ y ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE ⊤ ⊤ e').hom
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d := by
    intro y hy e'
    subst hy
    rw [specMap_appLE_top]
    simp
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
    ((p.appLE ⊤ U (fun _ _ => trivial) ≫ x.appLE U ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) = φ d
  rw [e]
  exact key _ hx _

/- English proof (translation)
The claim follows from `congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d)) (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)`.
-/
theorem constSec_res (p : X ⟶ Spec (CommRingCat.of R)) {U V : X.Opens} (i : V ⟶ U) (d : R) :
    (X.presheaf.map i.op).hom (constSec p U d) = constSec p V d :=
  congrArg (fun ψ => ψ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d))
    (p.appLE_map (U := ⊤) (V := U) (V' := V) (fun _ _ => trivial) i.op)

/- English proof (translation)
Establish `e₁` using `Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl`. Establish `e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤), (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d)`. Introduce `y hy e'`. Substitute `hy` using the available equality. Rewrite using `[Scheme.Hom.comp_appLE]`.

Establish `n` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)`. Establish `n'` using `congrArg (fun ψ => ψ.hom d) n`. Simplify using `only [constSec]`. Express the relevant statement in the definitionally equal form `(p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _`. Conclude with `congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm`.

Rewrite using `[← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression.
-/
theorem app_constSec {R' : Type} [CommRing R'] (p : X ⟶ Spec (CommRingCat.of R)) (p' : Y ⟶ Spec (CommRingCat.of R'))
    (F : Y ⟶ X) (φ : R →+* R') (hF : F ≫ p = p' ≫ Spec.map (CommRingCat.ofHom φ)) (U : X.Opens) (d : R) :
    (F.app U).hom (constSec p U d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
  have e₁ := Scheme.Hom.appLE_comp_appLE F p ⊤ U (F ⁻¹ᵁ U) (fun _ _ => trivial) le_rfl
  have e₂ : ∀ (y : Y ⟶ Spec (CommRingCat.of R)) (_ : y = p' ≫ Spec.map (CommRingCat.ofHom φ)) (e' : F ⁻¹ᵁ U ≤ y ⁻¹ᵁ ⊤),
      (y.appLE ⊤ (F ⁻¹ᵁ U) e').hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom d) = constSec p' (F ⁻¹ᵁ U) (φ d) := by
    intro y hy e'
    subst hy
    rw [Scheme.Hom.comp_appLE]
    have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    have n' := congrArg (fun ψ => ψ.hom d) n
    simp only [constSec]
    change (p'.appLE _ _ _).hom (((Spec.map (CommRingCat.ofHom φ)).appTop).hom _) = _
    exact congrArg (p'.appLE ⊤ (F ⁻¹ᵁ U) (fun _ _ => trivial)).hom n'.symm
  rw [← e₂ _ hF (fun _ _ => trivial), ← e₁, Scheme.Hom.app_eq_appLE]
  rfl

/- English proof (translation)
Set `_` to `(r.stalkMap z).hom.toAlgebra`. Establish `: Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)` using `Flat.stalkMap r z`. Establish `: IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z))` using `inferInstanceAs (IsLocalHom (r.stalkMap z).hom)`. Establish `: Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)` using `Module.FaithfullyFlat.of_flat_of_isLocalHom`. Rewrite using `[← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}), Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]`.

Conclude with `h`.
-/
theorem dvd_of_stalkMap_dvd (r : Y ⟶ X) [Flat r] (z : Y) {a b : X.presheaf.stalk (r z)}
    (h : (r.stalkMap z).hom a ∣ (r.stalkMap z).hom b) : a ∣ b := by
  let _ := (r.stalkMap z).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) := Flat.stalkMap r z
  have : IsLocalHom (algebraMap (X.presheaf.stalk (r z)) (Y.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (r.stalkMap z).hom)
  have : Module.FaithfullyFlat (X.presheaf.stalk (r z)) (Y.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.mem_span_singleton, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk z) (Ideal.span {a}),
    Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  exact h

/- English proof (translation)
Introduce `y _`. Establish `: Subsingleton (Spec (CommRingCat.of K))` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Establish `: Nonempty (Spec (CommRingCat.of L))` using `inferInstanceAs (Nonempty (PrimeSpectrum L))`. Take `⟨w⟩` from `this`. Establish `hw` using `h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)`.

Rewrite using `[Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]`. Simplify using `using hw`.
-/
theorem top_le_of_spec_comp {K L : Type} [Field K] [Field L] (κ : K →+* L) (x : Spec (CommRingCat.of K) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro y _
  have : Subsingleton (Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have : Nonempty (Spec (CommRingCat.of L)) := inferInstanceAs (Nonempty (PrimeSpectrum L))
  obtain ⟨w⟩ := this
  have hw := h (show w ∈ (⊤ : (Spec (CommRingCat.of L)).Opens) from trivial)
  rw [Subsingleton.elim y (Spec.map (CommRingCat.ofHom κ) w)]
  simpa using hw

end valAt

/- English proof (translation)
Introduce `R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg`. Take `⟨U', hgU', s', hs'⟩` from `hreg`. Take `⟨d, hd0, U, hgU, s, hs⟩` from `GlobalTheory.T.exists_denominator_regular R T Γ f (F g')`. Establish `hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R')))` using `Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)`. Establish `hF : Flat F` using `MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ`.

Establish `hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R'))` using `hbc.cart.w`. Set `W' : Γ'.G.left.Opens` to `(F ⁻¹ᵁ U) ⊓ U'`. Establish `hgW' : g' ∈ W'` using `⟨hgU, hgU'⟩`. Set `i₁ : W' ⟶ F ⁻¹ᵁ U` to `homOfLE inf_le_left`. Set `i₂ : W' ⟶ U'` to `homOfLE inf_le_right`.

Establish `key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) = constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s'`. Use `sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)` and prove the remaining obligations. Establish `h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U)` using `fun x hx => (h hx).1`. Establish `h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U'` using `fun x hx => (h hx).2`. Establish `hpt` using `GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t`.

Establish `h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U`. Rewrite using `[← hpt]`. Conclude with `h₁`. Establish `h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U` using `top_le_of_spec_comp κ _ U h₃`. Establish `hw' : (Γ'.pt t).left ≫ Γ'.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R')))` using `Over.w (Γ'.pt t)`.

Rewrite using `[valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂, valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁, valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]`. Establish `: κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d)` using `congrArg (fun ψ => ψ d) hκ`. Rewrite using `[this, sub_self]`. Establish `hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣ Γ.G.left.presheaf.germ U (F g') hgU s`. Apply `dvd_of_stalkMap_dvd F g'` to reduce the goal to its premises.

Use `⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩` and prove the remaining obligations. Establish `e₁` using `Scheme.Hom.germ_stalkMap_apply F U g' hgU s`. Establish `e₂` using `Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)`. Rewrite `e₂` using `[app_constSec _ _ F _ hsq]`. Establish `e₃` using `Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)`.

Establish `e₄` using `Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))`. Rewrite `e₄` using `[constSec_res]`. Rewrite `e₃` using `[key, map_mul]`. Conclude with `e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))`. Take `⟨x, hx⟩` from `hdvd`.

Take `⟨W, hgW, s₀, rfl⟩` from `Γ.G.left.presheaf.exists_germ_eq x`. Set `P : Γ.G.left.Opens` to `U ⊓ W`. Establish `hgP : F g' ∈ P` using `⟨hgU, hgW⟩`. Set `j₁ : P ⟶ U` to `homOfLE inf_le_left`. Set `j₂ : P ⟶ W` to `homOfLE inf_le_right`.

Establish `hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀)`. Rewrite using `[hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]`. Take `⟨V, hV, iU, iP, hres⟩` from `TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP`. Use `⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩` and prove the remaining obligations. Establish `hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U` using `fun x hx => iU.le (h hx)`.

Establish `hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P` using `fun x hx => iP.le (h hx)`. Establish `hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W` using `fun x hx => (iP ≫ j₂).le (h hx)`. Establish `hw : (Γ.pt t).left ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))` using `Over.w (Γ.pt t)`. Establish `hK : algebraMap R (FractionRing R) d ≠ 0`. Simplify using `using hd0`.

Use `mul_left_cancel₀ hK ?_` and prove the remaining obligations. Establish `e₁` using `congrArg (valAt (Γ.pt t).left V h) hres`. Rewrite `e₁` using `[valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw, valAt_res _ j₂ hPt hWt]`. Rewrite using `[valAt_res _ (iP ≫ j₂) h hWt]`. Conclude with `e₁.symm`.
-/
theorem regularAt_of_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hbc hfl κ hκ f g' hreg
  obtain ⟨U', hgU', s', hs'⟩ := hreg
  obtain ⟨d, hd0, U, hgU, s, hs⟩ := GlobalTheory.T.exists_denominator_regular R T Γ f (F g')
  have hφ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hfl)
  have hF : Flat F := MorphismProperty.of_isPullback (P := @Flat) hbc.cart.flip hφ
  have hsq : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) := hbc.cart.w
  let W' : Γ'.G.left.Opens := (F ⁻¹ᵁ U) ⊓ U'
  have hgW' : g' ∈ W' := ⟨hgU, hgU'⟩
  let i₁ : W' ⟶ F ⁻¹ᵁ U := homOfLE inf_le_left
  let i₂ : W' ⟶ U' := homOfLE inf_le_right
  have key : (Γ'.G.left.presheaf.map i₁.op).hom ((F.app U).hom s) =
      constSec Γ'.G.hom W' (algebraMap R R' d) * (Γ'.G.left.presheaf.map i₂.op).hom s' := by
    refine sub_eq_zero.mp (PositivityTheory.HtPt.Twhopf.sec_inj R' T Γ' W' _ fun t h => ?_)
    have h₁ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ (F ⁻¹ᵁ U) := fun x hx => (h hx).1
    have h₂ : ⊤ ≤ (Γ'.pt t).left ⁻¹ᵁ U' := fun x hx => (h hx).2
    have hpt := GlobalTheory.T.base_change_points_compat R T Γ R' Γ' F hbc κ hκ t
    have h₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom κ) ≫ (Γ.pt t).left) ⁻¹ᵁ U := by
      rw [← hpt]; exact h₁
    have h₄ : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_spec_comp κ _ U h₃
    have hw' : (Γ'.pt t).left ≫ Γ'.G.hom =
        Spec.map (CommRingCat.ofHom (algebraMap R' (FractionRing R'))) := Over.w (Γ'.pt t)
    rw [valAt_sub, valAt_mul, valAt_res _ i₁ h h₁, valAt_res _ i₂ h h₂, hs' t h₂,
      valAt_const _ _ (algebraMap R' (FractionRing R')) hw', ← valAt_comp _ F U h₁,
      valAt_congr hpt U h₁ h₃, valAt_spec κ _ U h₄ h₃, hs t h₄, map_mul]
    have : κ (algebraMap R _ d) = algebraMap R' _ (algebraMap R R' d) := congrArg (fun ψ => ψ d) hκ
    rw [this, sub_self]
  have hdvd : Γ.G.left.presheaf.germ U (F g') hgU (constSec Γ.G.hom U d) ∣
      Γ.G.left.presheaf.germ U (F g') hgU s := by
    apply dvd_of_stalkMap_dvd F g'
    refine ⟨Γ'.G.left.presheaf.germ W' g' hgW' ((Γ'.G.left.presheaf.map i₂.op).hom s'), ?_⟩
    have e₁ := Scheme.Hom.germ_stalkMap_apply F U g' hgU s
    have e₂ := Scheme.Hom.germ_stalkMap_apply F U g' hgU (constSec Γ.G.hom U d)
    rw [app_constSec _ _ F _ hsq] at e₂
    have e₃ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' ((F.app U).hom s)
    have e₄ := Γ'.G.left.presheaf.germ_res_apply i₁ g' hgW' (constSec Γ'.G.hom (F ⁻¹ᵁ U) (algebraMap R R' d))
    rw [constSec_res] at e₄
    rw [key, map_mul] at e₃
    exact e₁.trans (e₃.symm.trans (by rw [e₄, ← e₂]))
  obtain ⟨x, hx⟩ := hdvd
  obtain ⟨W, hgW, s₀, rfl⟩ := Γ.G.left.presheaf.exists_germ_eq x
  let P : Γ.G.left.Opens := U ⊓ W
  have hgP : F g' ∈ P := ⟨hgU, hgW⟩
  let j₁ : P ⟶ U := homOfLE inf_le_left
  let j₂ : P ⟶ W := homOfLE inf_le_right
  have hP : Γ.G.left.presheaf.germ U (F g') hgU s = Γ.G.left.presheaf.germ P (F g') hgP
      (constSec Γ.G.hom P d * (Γ.G.left.presheaf.map j₂.op).hom s₀) := by
    rw [hx, map_mul, TopCat.Presheaf.germ_res_apply, ← constSec_res _ j₁, TopCat.Presheaf.germ_res_apply]
  obtain ⟨V, hV, iU, iP, hres⟩ := TopCat.Presheaf.germ_eq _ _ hgU hgP _ _ hP
  refine ⟨V, hV, (Γ.G.left.presheaf.map (iP ≫ j₂).op).hom s₀, fun t h => ?_⟩
  have hU : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := fun x hx => iU.le (h hx)
  have hPt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ P := fun x hx => iP.le (h hx)
  have hWt : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ W := fun x hx => (iP ≫ j₂).le (h hx)
  have hw : (Γ.pt t).left ≫ Γ.G.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := Over.w (Γ.pt t)
  have hK : algebraMap R (FractionRing R) d ≠ 0 := by
    simpa using hd0
  refine mul_left_cancel₀ hK ?_
  have e₁ := congrArg (valAt (Γ.pt t).left V h) hres
  rw [valAt_res _ iU h hU, hs t hU, valAt_res _ iP h hPt, valAt_mul, valAt_const _ _ _ hw,
    valAt_res _ j₂ hPt hWt] at e₁
  rw [valAt_res _ (iP ≫ j₂) h hWt]
  exact e₁.symm

end PositivityTheory.HtPt.Htat.StalkDivisibility

/- English proof (translation)
The claim follows from `@PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange`.
-/
theorem PositivityTheory.HtPt.Htat.bt_reg_descent : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → Module.Flat R R' → ∀ κ : FractionRing R →+* FractionRing R', κ.comp (algebraMap R _) = (algebraMap R' _).comp (algebraMap R R') → ∀ (f : T → FractionRing R) (g' : Γ'.G.left), Γ'.RegularAt (fun t => κ (f t)) g' → Γ.RegularAt f (F g') :=
  @PositivityTheory.HtPt.Htat.StalkDivisibility.regularAt_of_baseChange
