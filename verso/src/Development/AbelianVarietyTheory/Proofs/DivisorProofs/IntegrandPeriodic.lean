import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.GaugeEx
open scoped Matrix Pointwise

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Establish `h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0` using `by funext l; simp [rat]`. Establish `h` using `hf 0 b (x, y)`. Rewrite `h` using `[h0, Prod.mk_add_mk, zero_add]`. Rewrite using `[h, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm]`. Use `congr 2`.

Simplify using `only [symV, dotProduct_add, zero_dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
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
Unfold `invV`. Use `congr 1`. Use function extensionality and compare the values at `y`. Rewrite using `[heisV, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm, Prod.mk_add_mk, add_zero]`. Use `congr 2`.

Simplify using `only [symV, add_dotProduct, dotProduct_zero]`. Expand and normalize the polynomial expressions, which then agree.
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
Take `⟨hH, hmem, -, -, -⟩` from `GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν`. Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: Countable (ratSub F N)`. Use `Set.Countable.to_subtype ((Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun v hv => ?_)` and prove the remaining obligations. Take `⟨ξ, h⟩` from `(hmem v).1 hv`.

Conclude with `⟨ξ, h.symm⟩`. Set `P : (Fin N → AF F) → ℂ` to `fun y => f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))`. Establish `hP : ∀ (g : ratSub F N) (y : Fin N → AF F), P (g +ᵥ y) = P y`. Introduce and unpack `⟨g, hg⟩ y`. Take `⟨ξ, rfl⟩` from `(hmem g).1 hg`.

Conclude with `integrand_periodic hf x y ξ`. Establish `e1 : invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * ∫ y in 𝓓, P (y + u) ∂(muV N ν)`. Unfold `invV`. Rewrite using `[← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `y`. Simplify using `only [heisV, P, Prod.mk_add_mk, add_zero]`. Rewrite using `[mul_right_comm, ← AddChar.map_add_eq_mul, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]`. Use `congr 2`. Simplify using `only [symV, dotProduct_add, zero_dotProduct]`.

Take the linear combination `two_mul_invOf (x ⬝ᵥ u)`. Rewrite using `[e1]`. Use `congr 1`. Establish `hmp : MeasurePreserving (fun y : Fin N → AF F => y + u) (muV N ν) (muV N ν)` using `measurePreserving_add_right _ u`. Establish `hemb : MeasurableEmbedding (fun y : Fin N → AF F => y + u)` using `measurableEmbedding_addRight u`.

Establish `hD' : IsAddFundamentalDomain (ratSub F N) (u +ᵥ 𝓓) (muV N ν)` using `hD.vadd_of_comm u`. Establish `e2 : 𝓓 = (fun y : Fin N → AF F => y + u) ⁻¹' (u +ᵥ 𝓓)`. Use extensionality with `y`. Rewrite using `[Set.mem_preimage, add_comm]`. Conclude with `Set.vadd_mem_vadd_set_iff.symm`.

Use `conv_lhs => rw [e2]`. Rewrite using `[hmp.setIntegral_preimage_emb hemb P]`. Conclude with `hD'.setIntegral_eq hD hP`.
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
