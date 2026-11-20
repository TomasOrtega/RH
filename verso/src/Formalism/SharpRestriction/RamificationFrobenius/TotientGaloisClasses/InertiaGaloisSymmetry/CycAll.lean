import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.InertiaGaloisSymmetry.CycGrp

open NumberField IntermediateField Ideal
open scoped Pointwise

noncomputable section

namespace Formalism.HC.Der

open Formalism.FrobeniusOrbits

variable {φ : Frame} (H : HostRaw φ)

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem I_sqrt_ne_zero : Complex.I * (Real.sqrt H.d : ℂ) ≠ 0 := by
  have h : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
  exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr h).ne')

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem emb_sqd (ψ : H.E →+* ℂ) :
    ψ H.sqd = Complex.I * (Real.sqrt H.d : ℂ) ∨ ψ H.sqd = -(Complex.I * (Real.sqrt H.d : ℂ)) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  have h : ((Real.sqrt H.d : ℝ) : ℂ) ^ 2 = (H.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity), Complex.ofReal_natCast]
  rw [← map_pow, H.sqd_sq, map_neg, map_natCast, mul_pow, Complex.I_sq, h, neg_one_mul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Take a linear combination of the given relations to obtain the conclusion. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem cmType_iff (ψ : H.E →+* ℂ) : ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType := by
  have h0 := I_sqrt_ne_zero H
  show ψ H.sqd = _ ↔ ¬ starRingEnd ℂ (ψ H.sqd) = _
  rw [← conj_apply, conj_sqd, map_neg]
  constructor
  · intro h1 h2
    apply h0
    linear_combination (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2
  · intro h1
    exact (emb_sqd H ψ).resolve_right fun h2 => h1 (by rw [h2, neg_neg])

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cmType : (∀ ψ : H.E →+* ℂ, ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType) ∧ H.cmType.ncard = 2 * φ.ord ∧
    ∀ ψ ∈ H.cmType, ∀ σ : H.E ≃ₐ[ℚ] H.E, ψ.comp (σ : H.E →+* H.E) ∈ H.cmType ↔ H.gal σ ∈ φ.Psi := by
  refine ⟨cmType_iff H, ?_, fun ψ hψ σ => ?_⟩
  · have hinv : Function.Involutive (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) := fun ψ => by
      ext x
      simp
    have h1 : H.cmTypeᶜ = (fun ψ : H.E →+* ℂ => (starRingEnd ℂ).comp ψ) '' H.cmType := by
      ext ψ
      constructor
      · intro h
        refine ⟨_, (cmType_iff H ((starRingEnd ℂ).comp ψ)).mpr ?_, hinv ψ⟩
        have h2 : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp ψ) = ψ := hinv ψ
        rwa [h2]
      · rintro ⟨χ, h2, rfl⟩
        exact (cmType_iff H χ).mp h2
    have h2 := Set.ncard_add_ncard_compl H.cmType
    rw [h1, Set.ncard_image_of_injective _ hinv.injective, Nat.card_eq_fintype_card, Embeddings.card,
      finrank_E] at h2
    omega
  · rw [gal_mem_Psi_iff]
    have h1 : ψ H.sqd = _ := hψ
    show ψ (σ H.sqd) = _ ↔ _
    rw [← h1]
    exact ψ.injective.eq_iff

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Evaluate the decidable proposition. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem ps_root : ∃ a : H.E, a ≠ 0 ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ a = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * a := by
  let χ : (H.E ≃ₐ[ℚ] H.E) →* ℤˣ := φ.chQ.comp H.gal.toMonoidHom
  have hχ : ∀ σ, (H.gal σ).1.1 = χ σ := fun _ => rfl
  have hs : χ H.conj = -1 := by rw [← hχ, gal_conj]; rfl
  have h1 : H.conj ∉ (fixedField χ.ker).fixingSubgroup := by
    rw [fixingSubgroup_fixedField, MonoidHom.mem_ker, hs]
    decide
  rw [IntermediateField.mem_fixingSubgroup_iff] at h1
  push Not at h1
  obtain ⟨x, hx, hne⟩ := h1
  rw [IntermediateField.mem_fixedField_iff] at hx
  have hx' : ∀ σ, χ σ = 1 → σ x = x := fun σ h => hx σ h
  refine ⟨x - H.conj x, fun h => hne (sub_eq_zero.mp h).symm, fun σ => ?_⟩
  rw [hχ, map_sub]
  rcases Int.units_eq_one_or (χ σ) with h | h
  · have h2 := hx' (H.conj⁻¹ * (σ * H.conj)) (by rw [map_mul, map_mul, map_inv, h, one_mul, inv_mul_cancel])
    have h3 : σ (H.conj x) = H.conj x := by
      have h4 := congrArg H.conj h2
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h4
    rw [h, hx' σ h, h3]
    simp
  · have h2 := hx' (H.conj⁻¹ * σ) (by rw [map_mul, map_inv, h, hs, inv_mul_cancel])
    have h3 : σ x = H.conj x := by
      have h4 := congrArg H.conj h2
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel_left] at h4
    have h4 : σ (H.conj x) = x := hx' (σ * H.conj) (by rw [map_mul, h, hs]; decide)
    rw [h, h3, h4]
    simp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hostCore : HostCore H where
  art_surj := art_surj H
  cm := cm H
  conj_iff := conj_iff H
  finrank_E := finrank_E H
  finrank_F := finrank_F H
  mem_F := mem_F H
  art_ch := art_ch H
  ps_d := ps_d H
  frob := frob H
  frob_any := frob_any H
  inertia := inertia H
  decomp := decomp H
  inertia_d := inertia_d H
  decomp_typeI := decomp_typeI H
  decompConj := decompConj H
  unramEF := unramEF H

end Formalism.HC.Der

end
