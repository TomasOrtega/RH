import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupEndomorphismUniqueOfThickeningAc
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.NeTopOfAdmissibleBase
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.Mum.Two

/- English proof (translation)
Use `forall_congr' fun χ => ?_` and prove the remaining obligations. Establish `: (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial) (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val = t.left.appTop.hom (charUnit S X' χ).val`. Rewrite using `[Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]`. Both sides reduce to the same expression. Rewrite using `[← this, Units.ext_iff]`.
-/
theorem torusHomOf_iff_appTop {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (h : X' → X)
    (t : splitTorus S X ⟶ splitTorus S X') : TorusHomOf h t ↔
      ∀ χ, t.left.appTop.hom (charUnit S X' χ).val = (charUnit S X (h χ)).val := by
  refine forall_congr' fun χ => ?_
  have : (res (fun x _ => show t.left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
      (pullU t.left ⊤ (charUnit S X' χ)) : Γ((splitTorus S X).left, ⊤)ˣ).val =
      t.left.appTop.hom (charUnit S X' χ).val := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [← this, Units.ext_iff]

/- English proof (translation)
Use `(splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)` and prove the remaining obligations. Take `⟨χ, rfl⟩` from `Multiplicative.ofAdd.surjective χ`. Rewrite using `[splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht, (torusHomOf_iff_appTop _ _).1 ht']`.
-/
theorem torusHomOf_unique {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {h : X' → X}
    {t t' : splitTorus S X ⟶ splitTorus S X'} (ht : TorusHomOf h t) (ht' : TorusHomOf h t') : t = t' := by
  refine (splitTorusPointsEquiv S X' _).injective (MonoidHom.ext fun χ => Units.ext ?_)
  obtain ⟨χ, rfl⟩ := Multiplicative.ofAdd.surjective χ
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, (torusHomOf_iff_appTop _ _).1 ht,
    (torusHomOf_iff_appTop _ _).1 ht']

/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂`. Establish `: IsNoetherianRing R` using `hR.1.1`. Establish `: Smooth G.hom` using `hG.smooth`. Establish `: GeometricallyConnected G.hom` using `hG.geomConnected`. Establish `: IsSeparated G.hom` using `hG.separated`.

Use `GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_` and prove the remaining obligations. Take `⟨t, ht, j₁⟩` from `i₁ e`. Take `⟨t', ht', j₂⟩` from `i₂ e`. Establish `htt : t = t'` using `torusHomOf_unique ht ht'`. Use `(U.gt e).i_hom` as an intermediate fact.

Conclude with `GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _ ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))`.
-/
theorem hom_eq_of_over₀_onTorus : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G), ∀ (g g' : G ⟶ G) (b : D'.toPre.P.A ⟶ D.toPre.P.A) (h : D.toPre.X → D'.toPre.X), IsMonHom g → IsMonHom g' → Over₀ U'.toUnifPre U.toUnifPre g b → Over₀ U'.toUnifPre U.toUnifPre g' b → OnTorus U'.toUnifPre U.toUnifPre g h → OnTorus U'.toUnifPre U.toUnifPre g' h → g = g' := by
  intro R _ _ _ hR D A G _ _ hG U D' A' U' g g' b h hg hg' q₁ q₂ i₁ i₂
  have : IsNoetherianRing R := hR.1.1
  have : Smooth G.hom := hG.smooth
  have : GeometricallyConnected G.hom := hG.geomConnected
  have : IsSeparated G.hom := hG.separated
  refine GlobalTheory.AbelianPartIso.hom_eq_of_map_eq (IsLocalRing.maximalIdeal_le_jacobson _) G g g' fun e => ?_
  obtain ⟨t, ht, j₁⟩ := i₁ e
  obtain ⟨t', ht', j₂⟩ := i₂ e
  have htt : t = t' := torusHomOf_unique ht ht'
  have := (U.gt e).i_hom
  exact GlobalTheory.LinearUnifIso.hom_ext_torus (U.gt e) (U'.gt e) GlobalTheory.globalFns_holds _ _
    ((q₁ e).trans (q₂ e).symm) (j₁.trans (htt ▸ j₂.symm))

end GlobalTheory.Mum.Two
