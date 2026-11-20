import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMixedArchIntegralAdditiveAndDiagonal.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.mixedArchIntegral_additive_and_diagonal : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q), mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧ ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q, mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  first | exact @GlobalTheory.MixAdd.mixArch_add_diag | exact GlobalTheory.MixAdd.mixArch_add_diag | (intros; apply GlobalTheory.MixAdd.mixArch_add_diag <;> assumption)
