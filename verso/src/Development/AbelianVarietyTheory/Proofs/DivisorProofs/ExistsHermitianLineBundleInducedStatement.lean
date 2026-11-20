import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLineBundleInduced
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHermitianLineBundleInduced.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.exists_hermitian_line_bundle_induced : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (V : Cover Y) (A : Adl C Y) (B : LB V.X) (r : (B.pull V.j).ι → V.G.functionFieldˣ), B.IsLB → V.FinInd A B r → (∀ σ, C.mSmooth Y σ A.D (A.m σ)) → ConjInv A → ∃ L : HermLB V.p, V.Induces A L 1 := by
  first | exact @GlobalTheory.Mean4O.HermCover.exists_hermLB_induces | exact GlobalTheory.Mean4O.HermCover.exists_hermLB_induces | (intros; apply GlobalTheory.Mean4O.HermCover.exists_hermLB_induces <;> assumption)
