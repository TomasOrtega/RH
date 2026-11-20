import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelwiseEquivalenceIsEquivalence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBisimplicialShuffleOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyCompShuffleHomotopicIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlexanderWhitneyHomotopyFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BisimplicialAlexanderWhitneyHomotopyEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EilenbergZilberHomotopyEquivalence

noncomputable section
open CategoryTheory Limits Opposite AlgebraicTopology

namespace GlobalTheory.EZ
universe u v

/- English proof (translation)
Take `⟨G, h0, hG⟩` from `GlobalTheory.T.exists_bisimplicial_shuffle_operators`. Take `⟨H, hH⟩` from `GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG`. Take `⟨K, hK⟩` from `GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG`. Conclude with `GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK`.
-/
theorem ez_nat {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (Y : SimplicialObject (SimplicialObject C)) :
    ∃ e : HomotopyEquiv (diagCx Y) (tot Y), ∀ n : ℕ, e.hom.f n = awF Y n := by
  obtain ⟨G, h0, hG⟩ := GlobalTheory.T.exists_bisimplicial_shuffle_operators
  obtain ⟨H, hH⟩ := GlobalTheory.T.alexanderWhitney_comp_shuffle_homotopic_id G h0 hG
  obtain ⟨K, hK⟩ := GlobalTheory.T.alexander_whitney_homotopy_formula G h0 hG
  exact GlobalTheory.T.bisimplicialAlexanderWhitney_homotopyEquiv Y G H K h0 hG hH hK

variable (R : Type) [CommRing R]

/- English proof (translation)
The claim follows from `GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)`.
-/
theorem ez (X : SimplicialObject GlobalTheory.EtC.Spc) :
    ∃ e : HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X),
      ∀ n : ℕ, e.hom.f (-(n : ℤ)) = awZ R X n :=
  GlobalTheory.T.eilenberg_zilber_homotopy_equivalence R X (ez_nat _)

def ezEquiv (X : SimplicialObject GlobalTheory.EtC.Spc) :
    HomotopyEquiv ((GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X)) (totChains R X) := (ez R X).choose

def awChains (X : SimplicialObject GlobalTheory.EtC.Spc) : (GlobalTheory.EtC.chains R).obj (GlobalTheory.EtC.bidiag.obj X) ⟶ totChains R X :=
  (ezEquiv R X).hom

/- English proof (translation)
The claim follows from `(ez R X).choose_spec n`.
-/
theorem awChains_f (X : SimplicialObject GlobalTheory.EtC.Spc) (n : ℕ) : (awChains R X).f (-(n : ℤ)) = awZ R X n :=
  (ez R X).choose_spec n

/- English proof (translation)
The claim follows from `GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k`.
-/
theorem pull_awChains_bijective (X : SimplicialObject GlobalTheory.EtC.Spc) (I : GlobalTheory.EtC.Cx R) (k : ℤ) :
    Function.Bijective (GlobalTheory.EtC.cpull (awChains R X) I k) :=
  GlobalTheory.EtC.LevelCmp.cpull_bij_of_heq (ezEquiv R X) I k

end GlobalTheory.EZ
