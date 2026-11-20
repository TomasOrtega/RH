import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms GlobalTheory.RegSS
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Chain the equalities or inequalities of the calculation. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
private lemma cT_mul_mul_eq_iff_mul_adj_eq_one {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) {J g : Matrix n n A} (hJ : IsUnit J.det) :
    cT s g * J * g = J ↔ g * adj s J g = 1 := by
  rw [mul_eq_one_comm, adj]
  constructor
  · intro h
    calc J⁻¹ * cT s g * J * g = J⁻¹ * (cT s g * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.nonsing_inv_mul _ hJ]
  · intro h
    have key : J * (J⁻¹ * cT s g * J * g) = J := by rw [h, Matrix.mul_one]
    simpa only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ, Matrix.one_mul] using key

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pointsCentraliser_of_commutant_of_adjoint :
    PointsCommutant → PointsAdjoint → PointsCentraliser := by
  intro hC hA F E _ _ _ _ n _ _ σ J γ hreg hAlg hPlus R _ _
  obtain ⟨hinj, hcomm⟩ := hC F E n σ J γ hreg hAlg hPlus R
  refine ⟨hinj, fun u => hA F E n σ J γ hreg R u, fun g => ?_⟩
  have hJ : IsUnit (J.map (inclE (F := F) R)).det := by
    have h := hreg.nondeg.map (inclE (F := F) R)
    rw [RingHom.map_det] at h
    exact h
  have hb : ((bc (inclE (F := F) R) γ : GL n (E ⊗[F] R)) : Matrix n n (E ⊗[F] R)) =
      (γ : Matrix n n E).map (inclE (F := F) R) := rfl
  simp only [centPts, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  unfold UPts UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq,
    Units.ext_iff, Units.val_mul, hb]
  rw [cT_mul_mul_eq_iff_mul_adj_eq_one _ hJ]
  constructor
  · rintro ⟨hunit, hc⟩
    obtain ⟨u, hu⟩ := (hcomm g).1 hc
    have h1 : u * lConj σ J (γ : Matrix n n E) R u = 1 := by
      apply hinj
      rw [map_mul, hA F E n σ J γ hreg R u, hu, map_one, hunit]
    exact ⟨Units.mkOfMulEqOne u _ h1, h1, hu⟩
  · rintro ⟨u, hu, hg⟩
    have hu' : (u : LPts σ J (γ : Matrix n n E) R) * lConj σ J (γ : Matrix n n E) R u = 1 := hu
    refine ⟨?_, (hcomm _).2 ⟨u, hg⟩⟩
    rw [← hg, ← hA F E n σ J γ hreg R, ← map_mul, hu', map_one]

end GlobalTheory.RegSS
