import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.NormChar
import Development.AutomorphicArithmetic.WhittakerHecke.CentralCharGaloisInvariantOfConjInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

open UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ _ hE P hP`. Take `⟨ω, hω⟩` from `GlobalTheory.CuspRep.Central.exists_hasCentChar (GlobalTheory.CuspRep.CG.mk P)`. Take `⟨χ, hχ⟩` from `UpperTheory.ConvolutionTheory.RankTwoDescent.A.normChar_of_inv hE ω (UpperTheory.centralChar_galois_invariant_of_conjInv E P ω hω hP)`. Use `⟨χ, fun f hf z g => ?_⟩` and prove the remaining obligations. Establish `h1` using `(GlobalTheory.CuspRep.CuspSub.hasCentral_iff (π := P) (ω := ω)).2 hω z f hf`.

Establish `h2` using `congrFun (congrArg Subtype.val h1) g`. Rewrite using `[GlobalTheory.CuspRep.scalar_comm, ← hχ z]`. Conclude with `h2`.
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
