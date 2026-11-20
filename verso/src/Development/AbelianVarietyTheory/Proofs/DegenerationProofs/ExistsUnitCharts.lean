import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.CrdCalc

variable {R : Type} [CommRing R] {X : Scheme.{0}}

def valHom (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.comp (x.appLE U ⊤ h).hom

/- English proof (translation)
Unfold `valR`. Rewrite using `[dif_pos h]`. Both sides reduce to the same expression.
-/
theorem valR_eq (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR x U f = valHom x U h f := by
  unfold valR
  rw [dif_pos h]
  rfl

/- English proof (translation)
Simplify using `only [valR_eq x U h, map_mul]`.
-/
theorem valR_mul (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f g : Γ(X, U)) :
    valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_eq x U h, map_mul]

/- English proof (translation)
Establish `hU : ⊤ ≤ x ⁻¹ᵁ U` using `h.trans (x.preimage_mono e)`. Rewrite using `[valR_eq x V h, valR_eq x U hU]`. Use `Scheme.Hom.map_appLE x h (homOfLE e).op` as an intermediate fact. Express the relevant statement in the definitionally equal form `(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem valR_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V (resG X e f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono e)
  rw [valR_eq x V h, valR_eq x U hU]
  have := Scheme.Hom.map_appLE x h (homOfLE e).op
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    ((X.presheaf.map (homOfLE e).op ≫ x.appLE V ⊤ h).hom f) = _
  rw [this]
  rfl

/- English proof (translation)
Establish `h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U` using `fun y _ => h (Set.mem_univ ((spMap φ) y))`. Use `⟨h', fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[valR_eq _ U h', valR_eq x U h]`. Establish `e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop`. Conclude with `(Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm`.

Establish `n` using `Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)`. Express the relevant statement in the definitionally equal form `((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f = (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f`. Rewrite using `[e, Category.assoc, n]`.
-/
theorem valR_spMap {R' : Type} [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U ∧ ∀ f, valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun y _ => h (Set.mem_univ ((spMap φ) y))
  refine ⟨h', fun f => ?_⟩
  rw [valR_eq _ U h', valR_eq x U h]
  have e : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    exact (Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl).symm
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  change ((spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).hom).hom f =
    (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom ≫ CommRingCat.ofHom φ).hom f
  rw [e, Category.assoc, n]

/- English proof (translation)
Rewrite using `[valR_eq x U h]`. Establish `e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f)` using `isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _`. Rewrite using `[e]`. Establish `b` using `Scheme.basicOpen_appLE x ⊤ U h f`. Prove the components needed by the constructor for the conclusion.

Introduce `hu`. Rewrite `b` using `[Scheme.basicOpen_of_isUnit _ hu]`. Conclude with `b.le.trans inf_le_right`. Introduce `hu`. Rewrite `b` using `[inf_eq_left.2 hu]`.

Use `RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_` and prove the remaining obligations. Conclude with `(Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)`.
-/
theorem isUnit_valR_iff (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    IsUnit (valR x U f) ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen f := by
  rw [valR_eq x U h]
  have e : IsUnit (valHom x U h f) ↔ IsUnit ((x.appLE U ⊤ h).hom f) :=
    isUnit_map_iff (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv _
  rw [e]
  have b := Scheme.basicOpen_appLE x ⊤ U h f
  constructor
  · intro hu
    rw [Scheme.basicOpen_of_isUnit _ hu] at b
    exact b.le.trans inf_le_right
  · intro hu
    rw [inf_eq_left.2 hu] at b
    refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
    exact (Scheme.mem_basicOpen _ _ y hy).1 (b.ge hy)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h (Set.mem_univ _), fun h => ((IsLocalRing.closed_point_mem_iff (R := R) (U := x ⁻¹ᵁ U)).1 h).ge⟩`.
-/
theorem top_le_iff [IsLocalRing R] (x : Sp R ⟶ X) (U : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint R) ∈ U :=
  ⟨fun h => h (Set.mem_univ _), fun h =>
    ((IsLocalRing.closed_point_mem_iff (R := R) (U := x ⁻¹ᵁ U)).1 h).ge⟩

/- English proof (translation)
Establish `hh : ⊤ ≤ x ⁻¹ᵁ (H.U l ⊓ H.U l')` using `fun y hy => ⟨h hy, h' hy⟩`. Use `⟨Units.map (valHom x _ hh).toMonoidHom (H.g l l'), fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[← valR_res x (inf_le_left : H.U l ⊓ H.U l' ≤ H.U l) hh, ← valR_res x (inf_le_right : H.U l ⊓ H.U l' ≤ H.U l') hh]`. Use `s.compat l l'` as an intermediate fact. Express the relevant statement in the definitionally equal form `valR x _ ((X.presheaf.map _).hom _) = _`.

Rewrite using `[this, valR_mul x _ hh, valR_eq x _ hh]`. Both sides reduce to the same expression.
-/
theorem exists_unit_charts (H : LB X) (x : Sp R ⟶ X) (l l' : H.ι) (h : ⊤ ≤ x ⁻¹ᵁ H.U l)
    (h' : ⊤ ≤ x ⁻¹ᵁ H.U l') :
    ∃ c : Rˣ, ∀ s : H.Sec, valR x (H.U l) (s.f l) = c * valR x (H.U l') (s.f l') := by
  have hh : ⊤ ≤ x ⁻¹ᵁ (H.U l ⊓ H.U l') := fun y hy => ⟨h hy, h' hy⟩
  refine ⟨Units.map (valHom x _ hh).toMonoidHom (H.g l l'), fun s => ?_⟩
  rw [← valR_res x (inf_le_left : H.U l ⊓ H.U l' ≤ H.U l) hh,
    ← valR_res x (inf_le_right : H.U l ⊓ H.U l' ≤ H.U l') hh]
  have := s.compat l l'
  change valR x _ ((X.presheaf.map _).hom _) = _
  rw [this, valR_mul x _ hh, valR_eq x _ hh]
  rfl

variable {H : LB X} {J : Type} {s : J → H.Sec}

/- English proof (translation)
Establish `: x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i` using `by rw [hH.cover]; trivial`. Take `⟨l, hl⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩`.
-/
theorem crd_exists [IsLocalRing R] (hH : H.IsLB) (s : J → H.Sec) (x : Sp R ⟶ X) : ∃ v, Crd H s x v := by
  have : x (IsLocalRing.closedPoint R) ∈ ⨆ i, H.U i := by rw [hH.cover]; trivial
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 this
  exact ⟨_, l, 1, (top_le_iff x _).2 hl, fun _ => rfl⟩

/- English proof (translation)
Take `⟨l, c, hl, hv⟩` from `h`. Take `⟨l', c', hl', hv'⟩` from `h'`. Take `⟨u, hu⟩` from `exists_unit_charts H x l' l hl' hl`. Use `⟨c' * u * c⁻¹, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]`.
-/
theorem crd_unique {x : Sp R ⟶ X} {v v' : J → R} (h : Crd H s x v) (h' : Crd H s x v') :
    ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨l', c', hl', hv'⟩ := h'
  obtain ⟨u, hu⟩ := exists_unit_charts H x l' l hl' hl
  refine ⟨c' * u * c⁻¹, fun j => ?_⟩
  rw [hv, hv', hu, Units.val_mul, Units.val_mul, _root_.mul_assoc, Units.inv_mul_cancel_left, _root_.mul_assoc]

/- English proof (translation)
Take `⟨l, c, hl, hv⟩` from `h`. Rewrite using `[hv, Units.isUnit_units_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `hu`. Conclude with `((isUnit_valR_iff x _ hl _).1 hu).trans (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))`.

Introduce `hu`. Take `⟨k, hk⟩` from `TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)`. Establish `hk'` using `(top_le_iff x _).2 hk`. Establish `hU : ⊤ ≤ x ⁻¹ᵁ H.U k` using `hk'.trans (x.preimage_mono (X.basicOpen_le _))`. Take `⟨u, hu⟩` from `exists_unit_charts H x l k hl hU`.

Rewrite using `[hu, Units.isUnit_units_mul]`. Conclude with `(isUnit_valR_iff x _ hU _).2 hk'`.
-/
theorem crd_isUnit_iff [IsLocalRing R] {x : Sp R ⟶ X} {v : J → R} (j : J) (h : Crd H s x v) :
    IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j) := by
  obtain ⟨l, c, hl, hv⟩ := h
  rw [hv, Units.isUnit_units_mul]
  constructor
  · intro hu
    exact ((isUnit_valR_iff x _ hl _).1 hu).trans
      (x.preimage_mono (le_iSup (fun k => X.basicOpen ((s j).f k)) l))
  · intro hu
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 ((top_le_iff x _).1 hu)
    have hk' := (top_le_iff x _).2 hk
    have hU : ⊤ ≤ x ⁻¹ᵁ H.U k := hk'.trans (x.preimage_mono (X.basicOpen_le _))
    obtain ⟨u, hu⟩ := exists_unit_charts H x l k hl hU
    rw [hu, Units.isUnit_units_mul]
    exact (isUnit_valR_iff x _ hU _).2 hk'

/- English proof (translation)
Take `⟨l, c, hl, hv⟩` from `h`. Take `⟨h₁, h₂⟩` from `valR_spMap φ x _ hl`. Use `⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[h₂, hv, map_mul]`.

Both sides reduce to the same expression.
-/
theorem crd_map {R' : Type} [CommRing R'] (φ : R →+* R') {x : Sp R ⟶ X} {v : J → R} (h : Crd H s x v) :
    Crd H s (spMap φ ≫ x) (fun j => φ (v j)) := by
  obtain ⟨l, c, hl, hv⟩ := h
  obtain ⟨h₁, h₂⟩ := valR_spMap φ x _ hl
  refine ⟨l, Units.map φ.toMonoidHom c, h₁, fun j => ?_⟩
  beta_reduce
  rw [h₂, hv, map_mul]
  rfl

/- English proof (translation)
Take `⟨l, c', hl, hv⟩` from `h`. Conclude with `⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩`.
-/
theorem crd_smul {x : Sp R ⟶ X} {v : J → R} (c : Rˣ) (h : Crd H s x v) :
    Crd H s x (fun j => (c : R) * v j) := by
  obtain ⟨l, c', hl, hv⟩ := h
  exact ⟨l, c * c', hl, fun j => by beta_reduce; rw [hv, Units.val_mul, _root_.mul_assoc]⟩

/- English proof (translation)
Take `⟨l, c, hl, hv⟩` from `h`. Establish `hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l)` using `fun y hy => ⟨hW hy, hl hy⟩`. Use `congrArg (valR x (W ⊓ H.U l)) (hr l)` as an intermediate fact. Rewrite `this` using `[valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh]`. Rewrite using `[hv, hv, this, mul_left_comm]`.
-/
theorem crd_ratio {x : Sp R ⟶ X} {v : J → R} {i j : J} {W : X.Opens} {r : Γ(X, W)} (h : Crd H s x v)
    (hr : IsRatio (s j) (s i) W r) (hW : ⊤ ≤ x ⁻¹ᵁ W) : v j = valR x W r * v i := by
  obtain ⟨l, c, hl, hv⟩ := h
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ H.U l) := fun y hy => ⟨hW hy, hl hy⟩
  have := congrArg (valR x (W ⊓ H.U l)) (hr l)
  rw [valR_mul x _ hh, valR_res x _ hh, valR_res x _ hh, valR_res x _ hh] at this
  rw [hv, hv, this, mul_left_comm]

/- English proof (translation)
Introduce `_ _ _ s hH` and use `⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩, fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩`.
-/
theorem crd_calculus : (∀ (X : Scheme.{0}) (H : LB X) (J : Type) (s : J → H.Sec), H.IsLB → (∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Sp R ⟶ X), (∃ v, Crd H s x v) ∧ (∀ v v', Crd H s x v → Crd H s x v' → ∃ c : Rˣ, ∀ j, v' j = (c : R) * v j) ∧ ∀ v j, Crd H s x v → (IsUnit (v j) ↔ ⊤ ≤ x ⁻¹ᵁ Out.nonzeroLocus (s j))) ∧ (∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ X) (v : J → R), Crd H s x v → Crd H s (spMap φ ≫ x) (fun j => φ (v j))) ∧ (∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (c : Rˣ), Crd H s x v → Crd H s x (fun j => (c : R) * v j)) ∧ ∀ (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : J → R) (i j : J) (W : X.Opens) (r : Γ(X, W)), Crd H s x v → IsRatio (s j) (s i) W r → ⊤ ≤ x ⁻¹ᵁ W → v j = valR x W r * v i) :=
  fun _ _ _ s hH =>
    ⟨fun _ _ _ x => ⟨crd_exists hH s x, fun _ _ => crd_unique, fun _ j => crd_isUnit_iff j⟩,
      fun _ _ _ _ φ _ _ => crd_map φ, fun _ _ _ _ c => crd_smul c, fun _ _ _ _ _ _ _ _ => crd_ratio⟩

end GlobalTheory.ZH.CrdCalc
end
