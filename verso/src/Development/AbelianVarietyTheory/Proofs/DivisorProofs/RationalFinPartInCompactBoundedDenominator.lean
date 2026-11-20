import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StdCharAnnihilatorOpenSubgroupFinPartCompact
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntegralOfMemIntAE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSchwartzAOfIsSchwartzBruhat
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.BoundedDen

/- English proof (translation)
Take `⟨e, he, hc, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `: (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2`. Use function extensionality and compare the values at `z`. Conclude with `((he z).2).symm`. Rewrite using `[this]`.

Conclude with `continuous_snd.comp hc`.
-/
theorem continuous_finPart (D : D7) : Continuous (finPart D) := by
  obtain ⟨e, he, hc, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have : (finPart D : AE D → Af D.host.F ⊗[D.host.F] D.host.E) = fun z => (e z).2 := by
    funext z; exact ((he z).2).symm
  rw [this]
  exact continuous_snd.comp hc

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D K hK`. Set `U : AddSubgroup (AE D)` to `(intAE D).comap (finPart D).toAddMonoidHom`. Establish `hU : IsOpen (U : Set (AE D))` using `(GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)`. Take `⟨n, hn⟩` from `GlobalTheory.CondBound.exists_small D K hK U hU`. Use `⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩` and prove the remaining obligations.

Establish `h` using `hn k hk`. Establish `h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D`. Establish `e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) = finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k)`. Rewrite using `[map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]`. Rewrite using `[e]`.

Conclude with `h`. Take `⟨y, hy⟩` from `GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2`. Establish `e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E)` using `hy.symm`. Rewrite using `[e2]`. Conclude with `NumberField.RingOfIntegers.isIntegral_coe y`.
-/
theorem bounded_den : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E,
    finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  intro D K hK
  let U : AddSubgroup (AE D) := (intAE D).comap (finPart D).toAddMonoidHom
  have hU : IsOpen (U : Set (AE D)) :=
    (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage (continuous_finPart D)
  obtain ⟨n, hn⟩ := GlobalTheory.CondBound.exists_small D K hK U hU
  refine ⟨n.factorial, Nat.factorial_pos n, fun k hk x hx => ?_⟩
  have h := hn k hk
  have h2 : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) ∈ intAE D := by
    have e : finPart D (incA D (((n.factorial : ℕ) : D.host.E) * x)) =
        finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 ((n.factorial : ℕ) : Af D.host.F)) * k) := by
      rw [map_mul (incA D), map_mul (finPart D), map_mul (finPart D), hx, GlobalTheory.CondBound.finPart_r]
    rw [e]; exact h
  obtain ⟨y, hy⟩ := GlobalTheory.FinalJoin.CondTest.integral_of_mem_intAE h2
  have e2 : (((n.factorial : ℕ) : D.host.E) * x) = (y : D.host.E) := hy.symm
  rw [e2]
  exact NumberField.RingOfIntegers.isIntegral_coe y

end GlobalTheory.BoundedDen
