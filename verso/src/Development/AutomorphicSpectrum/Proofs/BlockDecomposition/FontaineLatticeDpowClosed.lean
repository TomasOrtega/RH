import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeDpowClosedOfHyp

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHc

/- English proof (translation)
Use `Ideal.Quotient.subsingleton_iff.2 ?_` and prove the remaining obligations. Rewrite using `[pow_zero, Ideal.span_singleton_one]`.
-/
theorem subsingleton_Bk_zero (l : ℕ) [Fact l.Prime] : Subsingleton (Lat.Bk l 0) := by
  refine Ideal.Quotient.subsingleton_iff.2 ?_
  rw [pow_zero, Ideal.span_singleton_one]

/- English proof (translation)
Introduce `l _ M k`. Break down `Nat.eq_zero_or_pos k with rfl | hk` into its components or cases. Introduce `x _ n haveI := subsingleton_Bk_zero l`. Conclude with `⟨0, Subsingleton.elim _ _⟩`. Conclude with `GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)`.
-/
theorem hc_k : ∀ (l : ℕ) [Fact l.Prime] (M k : ℕ),
    Lat.DPClosed (Lat.ι (Lat.fk l k) (xi0 l) l M) (Lat.γB (Lat.fk l k) (xi0 l)) := by
  intro l _ M k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · intro x _ n
    haveI := subsingleton_Bk_zero l
    exact ⟨0, Subsingleton.elim _ _⟩
  · exact GlobalTheory.CompanionTheory.LatDP.dpClosed _ _ l M k (GlobalTheory.CompanionTheory.LatCHyp.hyp_k l k hk)

end GlobalTheory.CompanionTheory.LatCHc
