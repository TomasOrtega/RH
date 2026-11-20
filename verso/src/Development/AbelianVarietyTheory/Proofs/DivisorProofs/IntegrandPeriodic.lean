import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.GaugeEx
open scoped Matrix Pointwise

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrand_periodic {f : VA F N → ℂ} (hf : QuasiV ψ f) (x y : Fin N → AF F) (b : Fin N → F) :
    f (x, rat b + y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ (rat b + y)))) = f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
  have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
  have h := hf 0 b (x, y)
  rw [h0, Prod.mk_add_mk, zero_add] at h
  rw [h, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  simp only [symV, dotProduct_add, zero_dotProduct]
  ring

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem invV_heisV_fst (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (u, 0) f) x = invV ψ ν 𝓓 f (x + u) := by
  unfold invV
  congr 1
  funext y
  rw [heisV, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm, Prod.mk_add_mk, add_zero]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_zero]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Introduce a local definition for the expression. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem invV_heisV_snd {ν : Measure (AF F)} (hν : IsCov1 ν) {𝓓 : Set (Fin N → AF F)}
    (hD : IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν)) {f : VA F N → ℂ} (hf : QuasiV ψ f) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * invV ψ ν 𝓓 f x := by
  obtain ⟨hH, hmem, -, -, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (ratSub F N) := by
    refine Set.Countable.to_subtype ((Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun v hv => ?_)
    obtain ⟨ξ, h⟩ := (hmem v).1 hv
    exact ⟨ξ, h.symm⟩
  let P : (Fin N → AF F) → ℂ := fun y => f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))
  have hP : ∀ (g : ratSub F N) (y : Fin N → AF F), P (g +ᵥ y) = P y := by
    rintro ⟨g, hg⟩ y
    obtain ⟨ξ, rfl⟩ := (hmem g).1 hg
    exact integrand_periodic hf x y ξ
  have e1 : invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * ∫ y in 𝓓, P (y + u) ∂(muV N ν) := by
    unfold invV
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [heisV, P, Prod.mk_add_mk, add_zero]
    rw [mul_right_comm, ← AddChar.map_add_eq_mul, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
    congr 2
    simp only [symV, dotProduct_add, zero_dotProduct]
    linear_combination two_mul_invOf (x ⬝ᵥ u)
  rw [e1]
  congr 1
  have hmp : MeasurePreserving (fun y : Fin N → AF F => y + u) (muV N ν) (muV N ν) := measurePreserving_add_right _ u
  have hemb : MeasurableEmbedding (fun y : Fin N → AF F => y + u) := measurableEmbedding_addRight u
  have hD' : IsAddFundamentalDomain (ratSub F N) (u +ᵥ 𝓓) (muV N ν) := hD.vadd_of_comm u
  have e2 : 𝓓 = (fun y : Fin N → AF F => y + u) ⁻¹' (u +ᵥ 𝓓) := by
    ext y
    rw [Set.mem_preimage, add_comm]
    exact Set.vadd_mem_vadd_set_iff.symm
  conv_lhs => rw [e2]
  rw [hmp.setIntegral_preimage_emb hemb P]
  exact hD'.setIntegral_eq hD hP

end GlobalTheory.ThetaTransform

end
