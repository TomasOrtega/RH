import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WHyp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualMeasureExistsUniqueFourierInversionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.Hyp

noncomputable def trxForm {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (x : A.K) : LinearMap.BilinForm F A.K :=
  LinearMap.mk₂ F (fun u b => Algebra.trace F A.K (x * u * b))
    (fun m₁ m₂ n => by simp [mul_add, add_mul])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])
    (fun m n₁ n₂ => by simp [mul_add])
    (fun c m n => by simp [mul_smul_comm, smul_mul_assoc])

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Put the polynomial expressions in normal form. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem selfDual_kx_exists : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ x : A.Kˣ, ∃ ν : Measure A.K, SelfDual ν (Hyp.kx A ψ x) := by
  intro F E _ _ _ _ _ A ψ hψ x
  have hT := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.1
  obtain ⟨hL, -⟩ := hT
  have hsymm : (trxForm A (x : A.K)).IsSymm := by
    refine ⟨fun u b => ?_⟩
    simp only [trxForm, LinearMap.mk₂_apply, RingHom.id_apply]
    ring_nf
  have hleft : ∀ u : A.K, (∀ b, trxForm A (x : A.K) u b = 0) → u = 0 := by
    intro u hu
    have h0 : (x : A.K) * u = 0 := hL _ (fun b => by
      have := hu b
      simpa [trxForm, Algebra.traceForm_apply, mul_assoc] using this)
    have := congrArg (fun t => ((x⁻¹ : A.Kˣ) : A.K) * t) h0
    simpa [← mul_assoc] using this
  have hnd : (trxForm A (x : A.K)).Nondegenerate := by
    refine ⟨hleft, fun b hb => hleft b (fun u => ?_)⟩
    have := hb u
    simp only [trxForm, LinearMap.mk₂_apply] at this ⊢
    rw [show (x : A.K) * b * u = x * u * b by ring]
    exact this
  obtain ⟨⟨μ, hμ, -⟩, -⟩ := GlobalTheory.T.selfDual_measure_exists_unique_fourier_inversion F E ψ hψ A.K (trxForm A (x : A.K)) hsymm hnd
  refine ⟨μ, ?_⟩
  have hk : (fun u b => ψ (trxForm A (x : A.K) u b)) = Hyp.kx A ψ x := by
    funext u b
    simp [trxForm, Hyp.kx, Et.psiK]
  rw [← hk]
  exact hμ

end GlobalTheory.JR.Hyp
