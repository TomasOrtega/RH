import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechOneCochainToPosetCochainCoboundaryExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCapFBijective
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KS (rsT IsCoc IsCob)
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechCmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechOneCochainToPosetCochainCoboundaryExists.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.exists_d0_eq_toPos_of_isCob : ∀ (I : Type) [Finite I] (X : Scheme.{0}) (R : Type) [CommRing R] (s : X ⟶ Sp R) (U : I → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hinf : ∀ V W : X.Opens, IsAffineOpen V → IsAffineOpen W → IsAffineOpen (V ⊓ W)), ∀ c : GlobalTheory.KS.C1 U, IsCob U c → ∃ g, d0 (capF s U hU hinf) g = toPos s U hU hinf c := by
  first | exact @GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | exact GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists | (intros; apply GlobalTheory.CechCmp.cechOneCochainToPosetCochain_coboundary_exists <;> assumption)
