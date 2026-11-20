import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

/- English proof (translation)
Introduce `k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp`. Establish `hN : IsLocallyNoetherian (Sp k)` using `inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))`. Establish `h₁` using `(GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp`. Conclude with `(GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁`.
-/
theorem relAmple_of_finite_etale_isogeny : ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ ψ : A ⟶ B, IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → ∀ (L : LB A.left) (M : LB B.left), L.IsLB → M.IsLB → LBIso L (M.pull ψ.left) → Out.RelAmple A L → Out.RelAmple B M := by
  intro k _ _ A B _ _ hA hB ψ _ hf he hs L M hL hM hiso hamp
  have hN : IsLocallyNoetherian (Sp k) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of k)))
  have h₁ := (GlobalTheory.relAmple_finite_pow_iso (Sp k) A A (𝟙 A) L 1 one_pos hA hA hL
    (by simpa using (inferInstance : IsFinite (𝟙 A.left)))).2.2.2 (M.pull ψ.left) (LB.isLB_pull hM ψ.left) hiso hamp
  exact (GlobalTheory.relAmple_finite_pow_iso (Sp k) A B ψ M 1 one_pos hA hB hM hf).2.2.1 inferInstance hs h₁

end GlobalTheory.SS
