import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
import Development.AutomorphicArithmetic.WhittakerHecke.CentralCharGaloisInvariantOfConjInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

open UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.cenEx_of :
    CenEx := by
  intro E _ _ _ hE P hP
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentChar (GlobalTheory.CuspRep.CG.mk P)
  obtain ⟨χ, hχ⟩ := UpperTheory.ConvolutionTheory.RankTwoDescent.A.normChar_of_inv hE ω (UpperTheory.centralChar_galois_invariant_of_conjInv E P ω hω hP)
  refine ⟨χ, fun f hf z g => ?_⟩
  have h1 := (GlobalTheory.CuspRep.CuspSub.hasCentral_iff (π := P) (ω := ω)).2 hω z f hf
  have h2 := congrFun (congrArg Subtype.val h1) g
  rw [GlobalTheory.CuspRep.scalar_comm, ← hχ z]
  exact h2
