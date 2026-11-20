import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationExtendStalkOfIso
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDerivationExtendStalkOfIso.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_derivation_stalk_extend_of_app : ∀ (X X' : Scheme.{0}) (f : X' ⟶ X) [IsIso f] (U : X.affineOpens) (d : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (x : X') (hx : x ∈ f ⁻¹ᵁ U.1), ∃ δ : Derivation ℤ (X'.presheaf.stalk x) (X'.presheaf.stalk x), ∀ r, δ ((X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom r)) = (X'.presheaf.germ (f ⁻¹ᵁ U.1) x hx).hom ((f.app U.1).hom (d r)) := by
  first | exact @GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | exact GlobalTheory.StalkDer.derivation_extend_stalk_of_iso | (intros; apply GlobalTheory.StalkDer.derivation_extend_stalk_of_iso <;> assumption)
