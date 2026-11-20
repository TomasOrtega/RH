import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsArithmeticNefModelOfAmple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullWIsConj
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.AmpleKaehler
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsArithmeticNefModelOfAmple.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.exists_arithmetic_nef_model_of_ample : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv), Y.ample Δ → ∃ (q : ℕ+) (Z : TrueGeo.Model Y) (L : HermLB Z.p) (r : (L.B.pull Z.j).ι → Y.Fnˣ), Presents ((q : ℕ) • Δ) (L.B.pull Z.j) r ∧ ArInt.NefFib L ∧ ∀ σ : F →+* ℂ, (pullW Z L σ).IsSmooth (Y.an σ) ∧ (pullW Z L σ).StrictPos (Y.an σ) := by
  first | exact @GlobalTheory.AmpleModelPos.exists_model_strictPos | exact GlobalTheory.AmpleModelPos.exists_model_strictPos | (intros; apply GlobalTheory.AmpleModelPos.exists_model_strictPos <;> assumption)
