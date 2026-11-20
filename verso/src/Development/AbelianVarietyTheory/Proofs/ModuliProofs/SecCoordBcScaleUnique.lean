import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjectiveRepresentationPullbackCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.Coord
open GlobalTheory.ZM.RepBC

/- English proof (translation)
The claim follows from `hL.cover.ge`.
-/
theorem le_iSup_chart {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) : (⊤ : Y.Opens) ≤ iSup L.U := hL.cover.ge

/- English proof (translation)
Take `⟨w, hw⟩` from `glue_unit ⊤ L.U (fun _ => le_top) (le_iSup_chart hL) (fun j => t.s j * (t'.s j)⁻¹) (fun i j y hy => by`. Rewrite using `[← gm_res (𝟙 Y) y (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) hy, ← gm_res (𝟙 Y) y (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) hy]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, ht i j, ht' i j, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])`. Conclude with `⟨w, fun j => by rw [hw j, inv_mul_cancel_right]⟩`.
-/
theorem exists_global_unit {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) {t t' : L.Gen} (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ j, t.s j = res (le_top : L.U j ≤ ⊤) w * t'.s j := by
  obtain ⟨w, hw⟩ := glue_unit ⊤ L.U (fun _ => le_top) (le_iSup_chart hL) (fun j => t.s j * (t'.s j)⁻¹) (fun i j y hy => by
    rw [← gm_res (𝟙 Y) y (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) hy,
      ← gm_res (𝟙 Y) y (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) hy]
    congr 1
    rw [map_mul, map_mul, map_inv, map_inv, ht i j, ht' i j, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  exact ⟨w, fun j => by rw [hw j, inv_mul_cancel_right]⟩

/- English proof (translation)
Establish `h` using `congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Conclude with `r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)`.
-/
theorem appLE_spec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (e : (⊤ : (Sp R').Opens) ≤ spMap φ ⁻¹ᵁ ⊤)
    (a : R) : ((spMap φ).appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom (φ a) := by
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  refine Eq.trans ?_ h.symm
  exact r_self (X := Sp R') (U := ⊤) le_rfl (((spMap φ).app ⊤).hom _)

variable {X : Scheme.{0}} {M : LB X} {I : Type} {th : I → M.Sec} {R : Type} [CommRing R] {x : Sp R ⟶ X} {v : I → R}

/- English proof (translation)
Take `⟨τ, hτ, h⟩` from `h`. Use `⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩` and prove the remaining obligations. Establish `hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j` using `fun _ hy => le_pull M x j (e hy)`. Establish `h0` using `congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))`. Rewrite `h0` using `[map_mul, appLE_appLE _ _ _ _ e, appLE_r]`.

Use `h0.trans ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← appLE_spec φ le_top]`. Conclude with `(r_appLE (spMap φ) _ _ _).symm`.
-/
theorem baseChange (h : SecCoord M th x v) {R' : Type} [CommRing R'] (φ : R →+* R') :
    SecCoord M th (spMap φ ≫ x) (fun i => φ (v i)) := by
  obtain ⟨τ, hτ, h⟩ := h
  refine ⟨LB.pullGen M _ _ τ (spMap φ), ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen M _ _ τ hτ _, fun i j e => ?_⟩
  have hle : (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun _ hy => le_pull M x j (e hy)
  have h0 := congrArg ((spMap φ).appLE _ _ hle).hom (h i j (pull_le M x j))
  rw [map_mul, appLE_appLE _ _ _ _ e, appLE_r] at h0
  refine h0.trans ?_
  congr 1
  rw [← appLE_spec φ le_top]
  exact (r_appLE (spMap φ) _ _ _).symm

/- English proof (translation)
Take `⟨τ, hτ, h⟩` from `h`. Set `w : Γ(Sp R, ⊤)ˣ` to `Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u`. Use `⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩` and prove the remaining obligations. Establish `e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) = res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w)` using `Units.ext ((rr _ _ _).trans (rr _ _ _).symm)`. Simplify using `only [map_mul, map_inv]`.

Rewrite using `[hτ j j', e1, mul_left_comm]`. Rewrite using `[h i j e, map_mul, map_mul]`. Establish `e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) = (res (le_top : (M.pull x).U j ≤ ⊤) w).val` using `rfl`. Rewrite using `[e1]`. Use `show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)`.

Rewrite using `[_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]`.
-/
theorem scale (h : SecCoord M th x v) (u : Rˣ) : SecCoord M th x (fun i => u * v i) := by
  obtain ⟨τ, hτ, h⟩ := h
  let w : Γ(Sp R, ⊤)ˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toMonoidHom u
  refine ⟨⟨fun j => (res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹ * τ.s j⟩, fun j j' => ?_, fun i j e => ?_⟩
  · have e1 : res (inf_le_left : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j ≤ ⊤) w) =
        res (inf_le_right : (M.pull x).U j ⊓ (M.pull x).U j' ≤ _) (res (le_top : (M.pull x).U j' ≤ ⊤) w) :=
      Units.ext ((rr _ _ _).trans (rr _ _ _).symm)
    simp only [map_mul, map_inv]
    rw [hτ j j', e1, mul_left_comm]
  · rw [h i j e, map_mul, map_mul]
    have e1 : resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom u) =
      (res (le_top : (M.pull x).U j ≤ ⊤) w).val := rfl
    rw [e1]
    show _ = _ * (((res (le_top : (M.pull x).U j ≤ ⊤) w)⁻¹).val * (τ.s j).val)
    rw [_root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul]

/- English proof (translation)
Take `⟨τ, hτ, h⟩` from `h`. Take `⟨τ', hτ', h'⟩` from `h'`. Establish `hL` using `pull_isLB hM x`. Take `⟨w, hw⟩` from `exists_global_unit hL hτ hτ'`. Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩` and prove the remaining obligations.

Establish `key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) = w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i)`. Apply `(Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)` to reduce the goal to its premises. Introduce `j`. Establish `e` using `(h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))`. Rewrite `e` using `[hw j]`.

Use `show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _`. Rewrite using `[map_mul]`. Apply `(Units.mul_left_inj (τ'.s j)).1` to reduce the goal to its premises. Use `e.trans ?_` and prove the remaining obligations. Use `show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _`.

Expand and normalize the polynomial expressions, which then agree. Use `congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key` as an intermediate fact. Rewrite `this` using `[map_mul]`. Simplify using `using this`.
-/
theorem unique (hM : M.IsLB) (h : SecCoord M th x v) {v' : I → R} (h' : SecCoord M th x v') :
    ∃ u : Rˣ, ∀ i, v' i = u * v i := by
  obtain ⟨τ, hτ, h⟩ := h
  obtain ⟨τ', hτ', h'⟩ := h'
  have hL := pull_isLB hM x
  obtain ⟨w, hw⟩ := exists_global_unit hL hτ hτ'
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, fun i => ?_⟩
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v' i) =
      w.val * (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (v i) := by
    apply (Sp R).sheaf.eq_of_locally_eq' (M.pull x).U ⊤ (fun _ => homOfLE le_top) (le_iSup_chart hL)
    intro j
    have e := (h' i j (pull_le M x j)).symm.trans (h i j (pull_le M x j))
    rw [hw j] at e
    show resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _ = resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) _
    rw [map_mul]
    apply (Units.mul_left_inj (τ'.s j)).1
    refine e.trans ?_
    show _ * (resG (Sp R) (le_top : (M.pull x).U j ≤ ⊤) w.val * (τ'.s j).val) = _
    ring
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom key
  rw [map_mul] at this
  simpa using this

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ hM h` and use `⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩`.
-/
theorem secCoord_bc_scale_unique : ∀ (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R] (x : Sp R ⟶ X) (v : I → R), M.IsLB → SecCoord M th x v → (∀ (R' : Type) [CommRing R'] (φ : R →+* R'), SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) ∧ (∀ u : Rˣ, SecCoord M th x (fun i => u * v i)) ∧ ∀ v', SecCoord M th x v' → ∃ u : Rˣ, ∀ i, v' i = u * v i :=
  fun _ _ _ _ _ _ _ _ hM h => ⟨fun _ _ φ => baseChange h φ, scale h, fun _ h' => unique hM h h'⟩

end GlobalTheory.ZM.Coord
end
