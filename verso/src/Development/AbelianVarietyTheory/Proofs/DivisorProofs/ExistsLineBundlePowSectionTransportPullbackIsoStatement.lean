import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionTransportPullbackIso
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundlePowSectionTransportPullbackIso.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.exists_lineBundlePowSection_transport_pullbackIso : ∀ {X X' : Scheme.{0}} (L : LB X) (L' : LB X') (f : X' ⟶ X) (w : LB.Iso L' (L.pull f)), L.IsLB → L'.IsLB → w.IsGen → ∀ (N : ℕ) (t : H0 L' N), ∃ s : SecK L f N, ∀ (Z : Scheme.{0}) (p : Z ⟶ X') (z : Z) J J', Good L z J → Good L' z J' → sval s p z J = (gw w p z (J (p ≫ f)) (J' p) ^ N).val * sval t p z J' := by
  first | exact @GlobalTheory.Mum.exists_secK_of_iso_pull | exact GlobalTheory.Mum.exists_secK_of_iso_pull | (intros; apply GlobalTheory.Mum.exists_secK_of_iso_pull <;> assumption)
