import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

def sc {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sc_apply {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) (a : R) :
    sc f U a = constFn f U a := rfl

def valR {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) : Γ(X, U) →+* O :=
  (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.comp (a.appLE U ⊤ h).hom

/- English proof (translation)
Introduce `x _`. Establish `hs : (x : Sp O) ⤳ IsLocalRing.closedPoint O` using `(PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum O).2.ne_top)`. Conclude with `hs.mem_open V.2 h`.
-/
theorem top_le_of_closedPoint {O : Type} [CommRing O] [IsLocalRing O] (V : (Sp O).Opens)
    (h : IsLocalRing.closedPoint O ∈ V) : ⊤ ≤ V := by
  intro x _
  have hs : (x : Sp O) ⤳ IsLocalRing.closedPoint O :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum O).2.ne_top)
  exact hs.mem_open V.2 h

/- English proof (translation)
Establish `e : (a.appLE U ⊤ h).hom b = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (valR a U h b)`. Simplify using `[valR]`. Establish `e2` using `Scheme.basicOpen_appLE a ⊤ U h b`. Rewrite `e2` using `[e, basicOpen_eq_of_affine]`. Establish `: a (IsLocalRing.closedPoint O) ∈ X.basicOpen b ↔ IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b` using `Iff.rfl`.

Rewrite using `[this]`. Establish `e3 : (IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b) ↔ (IsLocalRing.closedPoint O ∈ (PrimeSpectrum.basicOpen (valR a U h b)))`. Rewrite using `[e2]`. Conclude with `⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩`. Rewrite using `[e3]`.

Express the relevant statement in the definitionally equal form `_ ↔ (valR a U h b) ∉ IsLocalRing.maximalIdeal O`. Simplify using `[IsLocalRing.mem_maximalIdeal]`.
-/
theorem valR_isUnit_iff {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (b : Γ(X, U)) :
    IsUnit (valR a U h b) ↔ a (IsLocalRing.closedPoint O) ∈ X.basicOpen b := by
  have e : (a.appLE U ⊤ h).hom b = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (valR a U h b) := by
    simp [valR]
  have e2 := Scheme.basicOpen_appLE a ⊤ U h b
  rw [e, basicOpen_eq_of_affine] at e2
  have : a (IsLocalRing.closedPoint O) ∈ X.basicOpen b ↔ IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b := Iff.rfl
  rw [this]
  have e3 : (IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b) ↔ (IsLocalRing.closedPoint O ∈ (PrimeSpectrum.basicOpen (valR a U h b))) := by
    rw [e2]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [e3]
  change _ ↔ (valR a U h b) ∉ IsLocalRing.maximalIdeal O
  simp [IsLocalRing.mem_maximalIdeal]

/- English proof (translation)
Simplify using `only [valR, RingHom.comp_apply]`. Use `congr 1`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.map_appLE]`.
-/
theorem valR_res {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR a V h ((X.presheaf.map (homOfLE hVU).op).hom f) = valR a U h' f := by
  simp only [valR, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/- English proof (translation)
Establish `key : ∀ (g : Sp O ⟶ Sp R) (_ : g = spMap ρ) (e : ⊤ ≤ g ⁻¹ᵁ ⊤), (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ρ r`. Introduce and unpack `_ rfl e`. Establish `e1 : (spMap ρ).appLE ⊤ ⊤ e = (spMap ρ).appTop` using `Scheme.Hom.appLE_eq_app (f := spMap ρ) (U := ⊤)`. Establish `e2` using `Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)`. Rewrite using `[e1]`.

Establish `e3 : ((spMap ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (ρ r)` using `(congrArg (fun q => q.hom r) e2).symm`. Rewrite using `[e3]`. Simplify using the standard rewrite rules. Establish `e1` using `Scheme.Hom.appLE_comp_appLE a π ⊤ U ⊤ (fun _ _ => trivial) h`. Rewrite using `[← key (a ≫ π) hρ (by simpa using fun _ _ => trivial)]`.

Simplify using `only [valR, sc, RingHom.comp_apply]`. Use `congr 1`. Rewrite using `[← CommRingCat.comp_apply, e1]`.
-/
theorem valR_sc {O R : Type} [CommRing O] [CommRing R] {X : Scheme.{0}} (a : Sp O ⟶ X) (π : X ⟶ Sp R) (ρ : R →+* O)
    (hρ : a ≫ π = spMap ρ) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) (r : R) : valR a U h (sc π U r) = ρ r := by
  have key : ∀ (g : Sp O ⟶ Sp R) (_ : g = spMap ρ) (e : ⊤ ≤ g ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ρ r := by
    rintro _ rfl e
    have e1 : (spMap ρ).appLE ⊤ ⊤ e = (spMap ρ).appTop := Scheme.Hom.appLE_eq_app (f := spMap ρ) (U := ⊤)
    have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)
    rw [e1]
    have e3 : ((spMap ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (ρ r) :=
      (congrArg (fun q => q.hom r) e2).symm
    rw [e3]
    simp
  have e1 := Scheme.Hom.appLE_comp_appLE a π ⊤ U ⊤ (fun _ _ => trivial) h
  rw [← key (a ≫ π) hρ (by simpa using fun _ _ => trivial)]
  simp only [valR, sc, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, e1]

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
