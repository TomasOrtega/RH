import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsPowGrpSplitTorus
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace TorusOfCharMap

variable {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X']

/- English proof (translation)
The claim follows from `(splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => h χ.toAdd)`.
-/
theorem ext_chV {Z : Over S} {a b : Z ⟶ splitTorus S X} (h : ∀ χ, chV a χ = chV b χ) : a = b :=
  (splitTorusPointsEquiv S X Z).injective (MonoidHom.ext fun χ => h χ.toAdd)

/- English proof (translation)
Use `ext1`. Rewrite using `[chV_val]`. Conclude with `SplitTorusPow.torusMap_char ρ χ`.
-/
theorem chV_torusMap (ρ : X' →+ X) (χ : X') :
    chV (SplitTorusPow.torusMap S ρ) χ = charUnit S X (ρ χ) := by
  ext1
  rw [chV_val]
  exact SplitTorusPow.torusMap_char ρ χ

/- English proof (translation)
Unfold `chV`. Rewrite using `[SplitTorusPow.points_comp_torusMap]`. Both sides reduce to the same expression.
-/
theorem chV_comp_torusMap (ρ : X' →+ X) {Z : Over S} (s : Z ⟶ splitTorus S X) (χ : X') :
    chV (s ≫ SplitTorusPow.torusMap S ρ) χ = chV s (ρ χ) := by
  unfold chV
  rw [SplitTorusPow.points_comp_torusMap]
  rfl

/- English proof (translation)
Use `ext_chV fun χ => ?_` and prove the remaining obligations. Rewrite using `[← Category.id_comp (SplitTorusPow.torusMap S ρ ≫ _), ← Category.assoc, chV_comp_torusMap, chV_comp_torusMap, ← Category.id_comp (SplitTorusPow.torusMap S (ρ.comp σ)), chV_comp_torusMap]`. Both sides reduce to the same expression.
-/
theorem torusMap_comp {X'' : Type} [AddCommGroup X''] (ρ : X' →+ X) (σ : X'' →+ X') :
    SplitTorusPow.torusMap S ρ ≫ SplitTorusPow.torusMap S σ = SplitTorusPow.torusMap S (ρ.comp σ) := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S ρ ≫ _), ← Category.assoc, chV_comp_torusMap,
    chV_comp_torusMap, ← Category.id_comp (SplitTorusPow.torusMap S (ρ.comp σ)), chV_comp_torusMap]
  rfl

/- English proof (translation)
Use `ext_chV fun χ => ?_` and prove the remaining obligations. Rewrite using `[← Category.id_comp (SplitTorusPow.torusMap S _), chV_comp_torusMap]`. Both sides reduce to the same expression.
-/
theorem torusMap_id : SplitTorusPow.torusMap S (AddMonoidHom.id X) = 𝟙 _ := by
  refine ext_chV fun χ => ?_
  rw [← Category.id_comp (SplitTorusPow.torusMap S _), chV_comp_torusMap]
  rfl

end TorusOfCharMap

/- English proof (translation)
Introduce `S X _ X' _ ρ`. Establish `key : ∀ τ : splitTorus S X ⟶ splitTorus S X', (∀ χ, chV τ χ = charUnit S X (ρ χ)) → τ = SplitTorusPow.torusMap S ρ` using `fun τ h => TorusOfCharMap.ext_chV fun χ => (h χ).trans (TorusOfCharMap.chV_torusMap ρ χ).symm`. Use `⟨⟨_, TorusOfCharMap.chV_torusMap ρ⟩, fun τ h => ?_⟩` and prove the remaining obligations. Take `rfl` from `key τ h`. Use `⟨SplitTorusPow.isMonHom_torusMap ρ, fun hb => ?_, fun Z s χ => TorusOfCharMap.chV_comp_torusMap ρ s χ⟩` and prove the remaining obligations.

Set `e : X' ≃+ X` to `AddEquiv.ofBijective ρ hb`. Use `⟨⟨SplitTorusPow.torusMap S e.symm.toAddMonoidHom, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[TorusOfCharMap.torusMap_comp]`. Use `TorusOfCharMap.torusMap_id (S := S) (X := X)` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Conclude with `e.apply_symm_apply x`. Rewrite using `[TorusOfCharMap.torusMap_comp]`. Use `TorusOfCharMap.torusMap_id (S := S) (X := X')` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Conclude with `e.symm_apply_apply x`.
-/
theorem splitTorus_map_of_charHom : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] (X' : Type) [AddCommGroup X'] (ρ : X' →+ X), (∃ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ))) ∧ ∀ (τ : splitTorus S X ⟶ splitTorus S X'), (∀ χ, chV τ χ = charUnit S X (ρ χ)) → IsMonHom τ ∧ (Function.Bijective ρ → IsIso τ) ∧ ∀ (Z : Over S) (s : Z ⟶ splitTorus S X) (χ : X'), chV (s ≫ τ) χ = chV s (ρ χ) := by
  intro S X _ X' _ ρ
  have key : ∀ τ : splitTorus S X ⟶ splitTorus S X', (∀ χ, chV τ χ = charUnit S X (ρ χ)) →
      τ = SplitTorusPow.torusMap S ρ := fun τ h =>
    TorusOfCharMap.ext_chV fun χ => (h χ).trans (TorusOfCharMap.chV_torusMap ρ χ).symm
  refine ⟨⟨_, TorusOfCharMap.chV_torusMap ρ⟩, fun τ h => ?_⟩
  obtain rfl := key τ h
  refine ⟨SplitTorusPow.isMonHom_torusMap ρ, fun hb => ?_, fun Z s χ => TorusOfCharMap.chV_comp_torusMap ρ s χ⟩
  let e : X' ≃+ X := AddEquiv.ofBijective ρ hb
  refine ⟨⟨SplitTorusPow.torusMap S e.symm.toAddMonoidHom, ?_, ?_⟩⟩
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X)
    ext x
    exact e.apply_symm_apply x
  · rw [TorusOfCharMap.torusMap_comp]
    convert TorusOfCharMap.torusMap_id (S := S) (X := X')
    ext x
    exact e.symm_apply_apply x

end GlobalTheory
