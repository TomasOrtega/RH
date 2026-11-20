import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
/- English proof (citation)
Apply `GlobalTheory.TwistLoc.exists_basis_off_prime` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUniformizationProofs%2FExistsTwistBasisOffPrime.lean&line=331#L331)
-/
theorem _root_.GlobalTheory.T.exists_twist_basis_off_prime : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), (∃ W : (Spec (CommRingCat.of R)).Opens, genericPoint (Spec (CommRingCat.of R)) ∈ W ∧ Nonempty (PsiOn D W)) → ∀ (p : Ideal R) [p.IsPrime] (k : ℕ), 1 ≤ k → ∀ α : D.X, ∃ b : Fin (k ^ D.P.g) → D.SecB k α, ∀ (R' : Type) [CommRing R'] (f : R →+* R'), (∀ s ∉ p, IsUnit (f s)) → ∀ b' : Fin (k ^ D.P.g) → LB.Sec (LB.LinComb D.P.L (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i) (DegPre.famε k)), (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) → IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b' := by
  first | exact @GlobalTheory.TwistLoc.exists_basis_off_prime | exact GlobalTheory.TwistLoc.exists_basis_off_prime | (intros; apply GlobalTheory.TwistLoc.exists_basis_off_prime <;> assumption)
