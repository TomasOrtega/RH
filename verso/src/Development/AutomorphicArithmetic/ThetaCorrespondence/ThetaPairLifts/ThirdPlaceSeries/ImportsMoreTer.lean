import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisTail
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility

set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.Pass.ResidualSpan
/- English proof (translation)
Introduce `D hRb _ i r ρ hr π hπ hd`. Establish `hHG : HG D.nd D.naut i` using `⟨π, (D.Zgood_tie i π).1 hπ⟩`. Establish `hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))` using `GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd`. Establish `hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π))`. Use `⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩` and prove the remaining obligations.

Introduce `x w hw B σ hB hσ`. Establish `e2` using `congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hd σ)`. Rewrite `e2` using `[Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map]`. Rewrite using `[heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]`. Use `(e2.trans ?_).symm` and prove the remaining obligations.

Use `congr 1`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `h` using `hRb.2 i hHG _ hrb`. Unfold `ResSpan`.

Use `h using 3` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Use `first`. Consider the case `rfl`. Consider the case `(ext a b; simp [mapM, rhoO, redRep, mapRep])`.
-/
theorem main_alt_alt : _root_.GlobalTheory.Pass.ResidueStatement := by
  intro D hRb _ i r ρ hr π hπ hd
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have h := hRb.2 i hHG _ hrb
  unfold ResSpan
  convert h using 3
  funext g
  first
    | rfl
    | (ext a b; simp [mapM, rhoO, redRep, mapRep])
end GlobalTheory.Pass.ResidualSpan
end
