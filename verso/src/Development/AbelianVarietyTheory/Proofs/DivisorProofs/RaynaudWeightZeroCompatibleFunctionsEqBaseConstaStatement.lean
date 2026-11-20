import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudWeightZeroCompatibleFunctionsEqBaseConsta
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Heat.AbConstGlob.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRaynaudWeightZeroCompatibleFunctionsEqBaseConsta.lean&line=70#L70)
-/
theorem _root_.GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  first | exact @GlobalTheory.Heat.AbConstGlob.main | exact GlobalTheory.Heat.AbConstGlob.main | (intros; apply GlobalTheory.Heat.AbConstGlob.main <;> assumption)
