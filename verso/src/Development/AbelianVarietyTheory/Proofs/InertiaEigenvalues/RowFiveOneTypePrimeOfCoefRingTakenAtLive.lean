import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlobalObjectsEveryFamilyWildStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualAbsIrredGoodPointOfResidualIrred
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.OrthogonalDesignFromSize

/- English proof (translation)
Introduce `hC D hN9 hT i k hk hHG r ρ hr π hπ hd _`. Establish `hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t` using `D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd`. Establish `hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)))` using `GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd`. Establish `hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π))`. Use `⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩` and prove the remaining obligations.

Introduce `x w hw B σ hB hσ`. Establish `e2` using `congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i))) (charpoly_of_decomp D i r ρ π hd σ)`. Rewrite `e2` using `[Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map]`. Rewrite using `[heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]`. Use `(e2.trans ?_).symm` and prove the remaining obligations.

Use `congr 1`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hirr` using `(hN9 i hHG _ hrb).1`. Establish `hpos : 0 < D.R.r`.

Use `D.R.two_le_m` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers. Establish `habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤` using `GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _ fun W hW => hirr W fun g _ x hx => hW g x hx`. Establish `hlive : Live D.nd i` using `⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩`.

Take `⟨r₀, ρ₀, hr₀, hw⟩` from `hT i hlive`. Take `⟨S, hS, hg⟩` from `GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec`. Conclude with `⟨S, hS, hg.2 ⟨k, hk⟩⟩`.
-/
theorem main : GlobalTheory.TwSys.Cheb → ∀ D : D7, AutomorphicSideWildInertia.ResidualIrreducibleGood D → TakenAll D → TypePrimeCongruences.TypePrimeWildIdempotentChoice D := by
  intro hC D hN9 hT i k hk hHG r ρ hr π hπ hd _
  have hdec : ∃ e, GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.IsDecomp (t := D.R.t) (r π) (ρ π) (D.nd.chi i) e := hd
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
  have hirr := (hN9 i hHG _ hrb).1
  have hpos : 0 < D.R.r := by
    have := D.R.two_le_m
    unfold Ranks.r
    omega
  have habs : AbsIrrSub (mapRep (IsLocalRing.residue (D.nd.O i)) (ρ π)) ⊤ :=
    GlobalTheory.ResAbsIrrGood.absIrrSub_top_of_irred (D.naut.kFbar i) hpos _
      fun W hW => hirr W fun g _ x hx => hW g x hx
  have hlive : Live D.nd i := ⟨π, hπ, r π, ρ π, hr π, hdec, habs⟩
  obtain ⟨r₀, ρ₀, hr₀, hw⟩ := hT i hlive
  obtain ⟨S, hS, hg⟩ := GlobalTheory.T.exists_globalObjects_every_family_wild hC D.nd i r₀ ρ₀ hr₀ hw r ρ hr π hπ hdec
  exact ⟨S, hS, hg.2 ⟨k, hk⟩⟩

end GlobalTheory.OrthogonalDesignFromSize
