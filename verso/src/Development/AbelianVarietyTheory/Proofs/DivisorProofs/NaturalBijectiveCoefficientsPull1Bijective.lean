import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.BC

/- English proof (translation)
Introduce `hb`. Set `β : ∀ T, F'.obj T →+* F.obj T` to `fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom`. Establish `hαβ : ∀ T (b : F'.obj T), α T (β T b) = b` using `fun T b ↦ (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b`. Establish `hβα : ∀ T (b : F.obj T), β T (α T b) = b` using `fun T b ↦ (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b`. Establish `natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b)`.

Introduce `T T' a b`. Apply `(hb T').1` to reduce the goal to its premises. Rewrite using `[hαβ, nat, hαβ]`. Establish `smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b`. Introduce `T r b`.

Apply `(hb T).1` to reduce the goal to its premises. Rewrite using `[hαβ, smul, hαβ]`. Set `m` to `GlobalTheory.Obs.BC.natCoef α nat smul`. Set `n` to `GlobalTheory.Obs.BC.natCoef β natβ smulβ`. Establish `left : ∀ c, n.pull1 (m.pull1 c) = c`.

Introduce `c`. Take `⟨f, rfl⟩` from `H1.mk_surjective F c`. Rewrite using `[CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `T T' φ`. Conclude with `hβα T' _`. Establish `right : ∀ c, m.pull1 (n.pull1 c) = c`. Introduce `c`. Take `⟨f, rfl⟩` from `H1.mk_surjective F' c`.

Rewrite using `[CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]`. Use `congr 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Use function extensionality and compare the values at `T T' φ`. Conclude with `hαβ T' _`.

Conclude with `⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩`.
-/
theorem natCoef_pull1_bijective (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F F' : C ⥤ CommAlgCat.{0} R)
    (α : ∀ T, F.obj T →+* F'.obj T)
    (nat : ∀ {T T' : C} (a : T ⟶ T') (b : F.obj T), α T' (mp F a b) = mp F' a (α T b))
    (smul : ∀ T (r : R) (b : F.obj T), α T (r • b) = r • α T b) :
    (∀ T, Function.Bijective (α T)) → Function.Bijective (GlobalTheory.Obs.BC.natCoef α nat smul).pull1 := by
  intro hb
  let β : ∀ T, F'.obj T →+* F.obj T := fun T ↦ (RingEquiv.ofBijective (α T) (hb T)).symm.toRingHom
  have hαβ : ∀ T (b : F'.obj T), α T (β T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).apply_symm_apply b
  have hβα : ∀ T (b : F.obj T), β T (α T b) = b := fun T b ↦
    (RingEquiv.ofBijective (α T) (hb T)).symm_apply_apply b
  have natβ : ∀ {T T' : C} (a : T ⟶ T') (b : F'.obj T), β T' (mp F' a b) = mp F a (β T b) := by
    intro T T' a b
    apply (hb T').1
    rw [hαβ, nat, hαβ]
  have smulβ : ∀ T (r : R) (b : F'.obj T), β T (r • b) = r • β T b := by
    intro T r b
    apply (hb T).1
    rw [hαβ, smul, hαβ]
  let m := GlobalTheory.Obs.BC.natCoef α nat smul
  let n := GlobalTheory.Obs.BC.natCoef β natβ smulβ
  have left : ∀ c, n.pull1 (m.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hβα T' _
  have right : ∀ c, m.pull1 (n.pull1 c) = c := by
    intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective F' c
    rw [CoefMap.pullCohomologyOne_class, CoefMap.pullCohomologyOne_class]
    congr 1
    refine Subtype.ext ?_
    funext T T' φ
    exact hαβ T' _
  exact ⟨Function.LeftInverse.injective left, Function.RightInverse.surjective right⟩

end GlobalTheory.Obs.BC
