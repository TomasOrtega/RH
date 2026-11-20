import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory

open TorusNil TorusLocal in

/- English proof (translation)
Use `set t := torusPt R A (AddMonoidAlgebra.of R A) with ht`. Establish `h1 : t ≫ f = t ≫ g`. Use `pt_ext_of_quotients (fun n : ℕ => (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A))) eq_zero_of_forall_mem_map_pow fun n => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc _ t]`. Conclude with `comp_eq_of_pullback_map_eq (hn n) _ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _ (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by`.

Rewrite using `[← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_map_of_mem _ ha))))`. Use the proof step `(by rw [← Spec.map_comp]; rfl)`. Use `isIso_torusPt_of R A` as an intermediate fact. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]`.
-/
theorem splitTorus_hom_ext_of_forall_pow (R : Type) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R)))
    (hB : IsSeparated B.hom) (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B)
    (hn : ∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f =
      (Over.pullback (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) : f = g := by
  set t := torusPt R A (AddMonoidAlgebra.of R A) with ht
  have h1 : t ≫ f = t ≫ g := by
    refine pt_ext_of_quotients (fun n : ℕ =>
      (IsLocalRing.maximalIdeal R ^ (n + 1)).map (algebraMap R (AddMonoidAlgebra R A)))
      eq_zero_of_forall_mem_map_pow fun n => ?_
    rw [← Category.assoc, ← Category.assoc _ t]
    exact comp_eq_of_pullback_map_eq (hn n) _
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift _
        (algebraMap R (AddMonoidAlgebra R A ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1)).map
          (algebraMap R (AddMonoidAlgebra R A)))) (fun a ha => by
          rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
          exact Ideal.mem_map_of_mem _ ha))))
      (by rw [← Spec.map_comp]; rfl)
  have := isIso_torusPt_of R A
  apply Over.OverMorphism.ext
  rw [← cancel_epi t.left, ← Over.comp_left, h1, ← Over.comp_left]

end GlobalTheory

open GlobalTheory in
/- English proof (translation)
The claim follows from `GlobalTheory.splitTorus_hom_ext_of_forall_pow`.
-/
example : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (A : Type) [AddCommGroup A] (B : Over (Spec (CommRingCat.of R))), IsSeparated B.hom → ∀ (f g : splitTorus (Spec (CommRingCat.of R)) A ⟶ B), (∀ n : ℕ, (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map f = (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (n + 1)))))).map g) → f = g := GlobalTheory.splitTorus_hom_ext_of_forall_pow
