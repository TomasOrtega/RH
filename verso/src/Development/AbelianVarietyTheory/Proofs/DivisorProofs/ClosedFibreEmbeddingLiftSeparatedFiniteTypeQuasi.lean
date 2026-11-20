import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR M G' _ _ hG E`. Establish `: IsNoetherianRing R` using `hR.1`. Establish `: Smooth G'.hom` using `hG.smooth`. Establish `: IsSeparated G'.hom` using `hG.separated`. Establish `: QuasiCompact G'.hom` using `hG.quasiCompact`.

Establish `: IsProper M.π` using `M.proper`. Establish `: IsLocallyNoetherian M.S` using `LocallyOfFiniteType.isLocallyNoetherian M.π`. Establish `: IsLocallyNoetherian G'.left` using `LocallyOfFiniteType.isLocallyNoetherian G'.hom`. Establish `: IsProper (PSpace.str R E.N)` using `isProper_str R E.N`. Use `set φ := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over`.

Establish `hφ : φ ≫ pullback.snd (PSpace.str R E.N) M.π = E.H.ι ≫ G'.hom` using `pullback.lift_snd _ _ _`. Establish `h1 : IsSeparated (φ ≫ pullback.snd (PSpace.str R E.N) M.π)` using `by rw [hφ]; infer_instance`. Establish `h2 : LocallyOfFiniteType (φ ≫ pullback.snd (PSpace.str R E.N) M.π)` using `by rw [hφ]; infer_instance`. Establish `h3 : QuasiCompact (φ ≫ pullback.snd (PSpace.str R E.N) M.π)` using `by rw [hφ]; infer_instance`. Conclude with `⟨IsSeparated.of_comp φ (pullback.snd _ _), locallyOfFiniteType_of_comp φ (pullback.snd _ _), QuasiCompact.of_comp φ (pullback.snd _ _)⟩`.
-/
theorem emb_lift_sep_loft_qc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G',
    IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  intro R _ _ _ hR M G' _ _ hG E
  have : IsNoetherianRing R := hR.1
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : IsProper M.π := M.proper
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : IsProper (PSpace.str R E.N) := isProper_str R E.N
  set φ := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over
  have hφ : φ ≫ pullback.snd (PSpace.str R E.N) M.π = E.H.ι ≫ G'.hom := pullback.lift_snd _ _ _
  have h1 : IsSeparated (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h2 : LocallyOfFiniteType (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h3 : QuasiCompact (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  exact ⟨IsSeparated.of_comp φ (pullback.snd _ _), locallyOfFiniteType_of_comp φ (pullback.snd _ _),
    QuasiCompact.of_comp φ (pullback.snd _ _)⟩

end GlobalTheory.Mum
