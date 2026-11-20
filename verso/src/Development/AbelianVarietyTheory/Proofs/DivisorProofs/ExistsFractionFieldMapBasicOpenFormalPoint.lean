import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.HeatV

/- English proof (translation)
Introduce `E _ _ _ H R _ _ t c hc Ω _ _ φ x' hx hinj`. Establish `e1 : ∀ y : Γ(Sp R, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((x'.appTop).hom ((t.G.hom.appTop).hom y)) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y)`. Introduce `y`. Establish `n` using `congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n`.

Rewrite using `[← n, show Spec.map (CommRingCat.ofHom φ) = x' ≫ t.G.hom from hx.symm, Scheme.Hom.comp_appTop]`. Both sides reduce to the same expression. Establish `e2 : ∀ y : Γ(Sp R, ⊤), ((η[t.G]).left.appTop).hom ((t.G.hom.appTop).hom y) = y`. Introduce `y`. Establish `w : (η[t.G]).left ≫ t.G.hom = 𝟙 (Sp R)` using `by simpa using Over.w η[t.G]`.

Use `congrArg (fun k => (Scheme.Hom.appTop k).hom y) w` as an intermediate fact. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : t.G.left.Opens)` using `by simp`.

Establish `inj : ∀ r : R, φ r = 0 → r = 0`. Introduce `r hr`. Use `set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r with hy`. Establish `hv : valR x' ⊤ ((t.G.hom.appTop).hom y) = 0`. Unfold `valR`.

Rewrite using `[dif_pos ht]`. Establish `: x'.appLE ⊤ ⊤ ht = x'.appTop` using `Scheme.Hom.appLE_eq_app _`. Rewrite using `[this, e1, hy]`. Simplify using `using hr`. Establish `h0` using `hinj ⊤ _ ht hv`.

Establish `h1` using `e2 y`. Rewrite `h1` using `[h0, map_zero]`. Establish `: (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y = r` using `by simp [hy]`. Rewrite using `[← this, ← h1, map_zero]`. Set `s : Γ(Sp R, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c`.

Set `gg : Γ(Sp R, ⊤) →+* FractionRing Ω` to `(algebraMap Ω (FractionRing Ω)).comp (φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)`. Establish `hu : IsUnit (gg s)`. Rewrite using `[isUnit_iff_ne_zero]`. Simplify using `only [gg, s, RingHom.comp_apply]`. Establish `hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) = c` using `by simp`.

Rewrite using `[hs]`. Introduce `h0`. Conclude with `hc (inj c ((IsFractionRing.injective Ω (FractionRing Ω)) (by simpa using h0)))`. Use `⟨IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu, fun r => ?_⟩` and prove the remaining obligations. Use `show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _`.

Rewrite using `[IsLocalization.Away.lift, IsLocalization.lift_eq]`. Simplify using `[gg]`.
-/
theorem fracIotaBasicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (t : SAB H (Sp R)) (c : R), c ≠ 0 → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω] (φ : R →+* Ω) (x' : Sp Ω ⟶ t.G.left), x' ≫ t.G.hom = spMap φ → (∀ O (f : Γ(t.G.left, O)), ⊤ ≤ x' ⁻¹ᵁ O → valR x' O f = 0 → f = 0) → ∃ iota : Γ(Sp R, (GlobalTheory.HeatV.bo R c).1) →+* (FractionRing Ω), ∀ r, iota (GlobalTheory.HeatV.resV R c r) = (algebraMap Ω (FractionRing Ω)) (φ r) := by
  intro E _ _ _ H R _ _ t c hc Ω _ _ φ x' hx hinj
  have e1 : ∀ y : Γ(Sp R, ⊤), (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom
      ((x'.appTop).hom ((t.G.hom.appTop).hom y)) = φ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y) := by
    intro y
    have n := congrArg (fun k => k.hom y) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at n
    rw [← n, show Spec.map (CommRingCat.ofHom φ) = x' ≫ t.G.hom from hx.symm, Scheme.Hom.comp_appTop]
    rfl
  have e2 : ∀ y : Γ(Sp R, ⊤), ((η[t.G]).left.appTop).hom ((t.G.hom.appTop).hom y) = y := by
    intro y
    have w : (η[t.G]).left ≫ t.G.hom = 𝟙 (Sp R) := by simpa using Over.w η[t.G]
    have := congrArg (fun k => (Scheme.Hom.appTop k).hom y) w
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    simp
  have ht : ⊤ ≤ x' ⁻¹ᵁ (⊤ : t.G.left.Opens) := by simp
  have inj : ∀ r : R, φ r = 0 → r = 0 := by
    intro r hr
    set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r with hy
    have hv : valR x' ⊤ ((t.G.hom.appTop).hom y) = 0 := by
      unfold valR
      rw [dif_pos ht]
      have : x'.appLE ⊤ ⊤ ht = x'.appTop := Scheme.Hom.appLE_eq_app _
      rw [this, e1, hy]
      simpa using hr
    have h0 := hinj ⊤ _ ht hv
    have h1 := e2 y
    rw [h0, map_zero] at h1
    have : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom y = r := by simp [hy]
    rw [← this, ← h1, map_zero]
  let s : Γ(Sp R, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c
  let gg : Γ(Sp R, ⊤) →+* FractionRing Ω :=
    (algebraMap Ω (FractionRing Ω)).comp (φ.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom)
  have hu : IsUnit (gg s) := by
    rw [isUnit_iff_ne_zero]
    simp only [gg, s, RingHom.comp_apply]
    have hs : (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) = c := by simp
    rw [hs]
    intro h0
    exact hc (inj c ((IsFractionRing.injective Ω (FractionRing Ω)) (by simpa using h0)))
  refine ⟨IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu, fun r => ?_⟩
  show IsLocalization.Away.lift (S := Γ(Sp R, (Sp R).basicOpen s)) s hu
    (algebraMap Γ(Sp R, ⊤) Γ(Sp R, (Sp R).basicOpen s) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = _
  rw [IsLocalization.Away.lift, IsLocalization.lift_eq]
  simp [gg]

end GlobalTheory.HeatV
