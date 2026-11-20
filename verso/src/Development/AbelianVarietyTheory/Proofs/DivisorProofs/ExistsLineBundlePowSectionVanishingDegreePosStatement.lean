import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePos
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLineBundlePowSectionVanishingDegreePos.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB → 0 < interNum k (GlobalTheory.structureModule C) ![L] → ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | exact GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | (intros; apply GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos <;> assumption)
