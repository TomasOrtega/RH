import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TmulSumEqZeroOfPureTensorFunctionZeroStatement

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem polMatch_zero_iff_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM Φ
  constructor
  · rintro ⟨T, hX, m, m', f, φ, f', φ', h1, h1', hΦ, h0, he⟩
    refine ⟨T, hX, m, f, φ, h1, hΦ, ?_⟩
    rw [he]
    exact GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M'.vac (fun v => (hM.triple.geo.hM'.vac v).2.1) hM.triple.geo.hM'.std R.p' Rf.Pi Rf.p' T m' f' φ'
      (fun j => (h1' j).2.2) h0.symm
  · rintro ⟨T, hX, m, f, φ, h1, hΦ, hz⟩
    refine ⟨T, hX, m, 0, f, φ, Fin.elim0, Fin.elim0, h1, fun j => j.elim0, hΦ, ?_, ?_⟩
    · simp
    · rw [hz]; simp

end GlobalTheory.PolKer
