import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.PerFactor
import ReciprocityTheory.CommutativeAlgebra.PowerSeriesPresentations.PresentationStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOfPoint

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

variable {R : Type} [CommRing R] [IsDomain R]

/- English proof (translation)
Establish `e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R` using `by simp`. Rewrite using `[e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]`. Use `congr 1`. Apply `Units.ext` to reduce the goal to its premises. Use `congrArg (fun q => q.hom (w : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this`. Conclude with `this.symm`.
-/
theorem gm_jK_unitOn (w : Rˣ) (z : (TK R).left) :
    gm (toUnit (TK R)).left z ⊤ (unitOn w) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)) := by
  have e : (toUnit (TK R)).left = 𝟙 _ ≫ jK R := by simp
  rw [e, ← gm_pull (𝟙 _) (jK R) z ⊤ trivial]
  congr 1
  apply Units.ext
  have := congrArg (fun q => q.hom (w : R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

/- English proof (translation)
Take `⟨u, hu, hv⟩` from `h`. Set `ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ` to `unitOn w⁻¹`. Use `⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩` and prove the remaining obligations. Use `show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)`. Rewrite using `[map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]`.

Conclude with `mul_left_comm _ _ _`. Rewrite using `[hv z J hJ]`. Establish `hm` using `hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left`. Use `show _ = _ * gm _ z _ (res le_top ρ * u.s _)`. Use `erw [MonoidHom.map_mul, gm_res _ z le_top hm]`.

Establish `e3 : gm (toUnit (TK R)).left z ⊤ ρ = (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹`. Rewrite using `[← gm_jK_unitOn, ← MonoidHom.map_inv]`. Conclude with `congrArg _ (MonoidHom.map_inv _ _)`. Establish `e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) = unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)` using `MonoidHom.map_mul _ _ _`. Rewrite using `[e3, e4, MonoidHom.map_mul]`.

Establish `: val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _)` using `rfl`. Rewrite using `[this, _root_.mul_assoc, mul_inv_cancel_left]`. Both sides reduce to the same expression.
-/
theorem tauCoord_mul_unit {Q : Data R} {a b : Q.X} {k : (FractionRing R)ˣ} (h : Q.TauCoord a b k) (w : Rˣ) :
    Q.TauCoord a b (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := by
  obtain ⟨u, hu, hv⟩ := h
  let ρ : Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ := unitOn w⁻¹
  refine ⟨⟨fun j => res le_top ρ * u.s j⟩, fun i j => ?_, fun z J hJ => ?_⟩
  · show res _ (res le_top ρ * u.s i) = _ * res _ (res le_top ρ * u.s j)
    rw [map_mul, map_mul, InhTate.res_res, InhTate.res_res, hu i j]
    exact mul_left_comm _ _ _
  · rw [hv z J hJ]
    have hm := hJ.mem (lamPts (Q.c a) (Q.c b)) (toUnit (TK R)).left
    show _ = _ * gm _ z _ (res le_top ρ * u.s _)
    erw [MonoidHom.map_mul, gm_res _ z le_top hm]
    have e3 : gm (toUnit (TK R)).left z ⊤ ρ =
        (gm (𝟙 _) z ⊤ (unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w)))⁻¹ := by
      rw [← gm_jK_unitOn, ← MonoidHom.map_inv]
      exact congrArg _ (MonoidHom.map_inv _ _)
    have e4 : unitOn (k * Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) =
        unitOn k * unitOn (Units.map (algebraMap R (FractionRing R) : R →* FractionRing R) w) := MonoidHom.map_mul _ _ _
    rw [e3, e4, MonoidHom.map_mul]
    have : val u (toUnit (TK R)).left z J = gm (toUnit (TK R)).left z _ (u.s _) := rfl
    rw [this, _root_.mul_assoc, mul_inv_cancel_left]
    rfl

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut

namespace GlobalTheory.PolDeg.Taut

end GlobalTheory.PolDeg.Taut
