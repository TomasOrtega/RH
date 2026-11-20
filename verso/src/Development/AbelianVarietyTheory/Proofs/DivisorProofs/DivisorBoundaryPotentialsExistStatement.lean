import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorBoundaryPotentialsExist
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry TopologicalSpace Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.CurvInterp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDivisorBoundaryPotentialsExist.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.divisor_boundary_potentials_exist : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (m : ℕ) (C : Fin m → Closeds Y.X) (n : Fin m → Pts Y (I.ε a) → ℝ), Y.dim = e → (∀ y : Y.X, LSncAt Y.X C y) → (∀ i, IsDivNorm (Y.an (I.ε a)) (C i) (n i)) → ∃ (L : Fin m → LocPot (M.X a)) (t : Fin m → M.X a → M.X a → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary (M.A a) L t (fun i => {z | under (I.pt a z) ∈ C i}) ∧ ∀ i z, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (L i) (t i) z = n i (I.pt a z) := by
  first | exact @GlobalTheory.DivSec.isBoundary_of_divNorm | exact GlobalTheory.DivSec.isBoundary_of_divNorm | (intros; apply GlobalTheory.DivSec.isBoundary_of_divNorm <;> assumption)
