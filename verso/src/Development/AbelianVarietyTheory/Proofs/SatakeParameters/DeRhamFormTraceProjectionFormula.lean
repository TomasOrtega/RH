import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.KaehlerOneFormsToExtensionDeRhamMulSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUniqueStatement

set_option autoImplicit false

noncomputable section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

/- English proof (translation)
Introduce `k K L _ _ _ _ _ _ _ _ _ α β`. Take `⟨m, b, ω, rfl⟩` from `(GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β`. Establish `hT` using `(GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]`. Rewrite using `[Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]`.
-/
theorem trDR_projection : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L),
    trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  intro k K L _ _ _ _ _ _ _ _ _ α β
  obtain ⟨m, b, ω, rfl⟩ := (GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β
  have hT := (GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1
  constructor
  · rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]
  · rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]

end GlobalTheory.W1
