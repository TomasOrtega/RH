import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPartialSumCompMonHomEqPartialSum.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.partialSum_comp_monHom_eq_partialSum : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  first | exact @GlobalTheory.MumProd.PsumMap.psum_comp_hom | exact GlobalTheory.MumProd.PsumMap.psum_comp_hom | (intros; apply GlobalTheory.MumProd.PsumMap.psum_comp_hom <;> assumption)
