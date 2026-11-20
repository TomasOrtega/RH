import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MongeAmpereIntersectionPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordUShimOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMongeAmpereIntersectionPolynomial.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.monge_ampere_intersection_polynomial : GlobalTheory.Published.GoodChernNumbers → ∀ {F : Type} [Field F] [NumberField F] {Y : GlobalTheory.ProjVar.Var F} {e : ℕ} {M : Man e} (I : ManIs M Y), Y.dim = e → ∀ {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i σ, (GlobalTheory.TrueGeo.cxSt F).Met Y σ (Δ i)) (t : ι → ℝ) (P : M.Pot), I.FormOf m t P → M.int (fun _ => P) (fun _ _ => 1) = Y.interPoly Δ ((∑ i, MvPolynomial.C (t i) * MvPolynomial.X i) ^ e) := by
  first | exact @GlobalTheory.ChernWeilLine.int_topPow_eq_interPoly | exact GlobalTheory.ChernWeilLine.int_topPow_eq_interPoly | (intros; apply GlobalTheory.ChernWeilLine.int_topPow_eq_interPoly <;> assumption)
