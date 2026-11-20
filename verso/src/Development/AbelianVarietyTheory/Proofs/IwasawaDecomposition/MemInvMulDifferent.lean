import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsHalfPtIff
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric NumberField GlobalTheory.Mem.Per
open scoped Pointwise nonZeroDivisors

namespace GlobalTheory.Mem.EigenLine

variable {R : Ranks} (H : Host R)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem half_ne_zero :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ≠ 0 := by
  refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
  intro h0
  have hd : differentIdeal (𝓞 H.K) (𝓞 H.E) ≠ ⊥ := differentIdeal_ne_bot
  apply hd
  have := H.𝔟_spec.1
  rw [h0, Ideal.bot_mul] at this
  exact this

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem half_mul_inv :
    ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) * H.AA0 = 1 :=
  mul_inv_cancel₀ (half_ne_zero H)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem inv_mul_different :
    H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) =
      ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) := by
  have h : differentIdeal (𝓞 H.K) (𝓞 H.E) = H.𝔟 * (H.conj • H.𝔟) := H.𝔟_spec.1
  rw [h, FractionalIdeal.coeIdeal_mul, ← mul_assoc, mul_comm H.AA0, half_mul_inv, one_mul]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem mem_inv_mul_different (x : H.E) :
    x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E) ↔
      ∃ b ∈ H.𝔟, x = H.conj ((b : 𝓞 H.E) : H.E) := by
  rw [inv_mul_different, FractionalIdeal.mem_coeIdeal]
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [Ideal.pointwise_smul_def] at hc
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _
      (MulSemiringAction.toRingEquiv _ (𝓞 H.E) H.conj).surjective).1 hc
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨H.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, rfl⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem map_mem_ellLat {LL : Type} [Field LL] [NumberField LL] (embE : H.E →+* LL)
    (g : R.GG) (x : H.E)
    (hx : x ∈ H.AA0 * ((differentIdeal (𝓞 H.K) (𝓞 H.E) : Ideal (𝓞 H.E)) : FractionalIdeal (𝓞 H.E)⁰ H.E)) :
    embE (H.sigmaOf g x) ∈ ellLat H embE g := by
  refine FractionalIdeal.mul_induction_on hx ?_ ?_
  · intro i hi j hj
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    exact Submodule.subset_span ⟨i, hi, b, hb, rfl⟩
  · intro a b ha hb
    rw [map_add, map_add]
    exact Submodule.add_mem _ ha hb

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ellT_eq_ellLat : ∀ (D : D7) (M : IntermediateField ℚ ℂ) [NumberField M] (embE : D.host.E →+* M),
    (∀ x, ((embE x : M) : ℂ) = D.host.φ₀ x) → ∀ τ : D.what₂.Tau,
      ellT D M τ = ellLat D.host embE (D.eTau τ).1 := by
  intro D M _ embE hE τ
  have hτ : ∀ (τ : D.what₂.Tau) x, embT D τ x = ((embE (D.host.sigmaOf (D.eTau τ).1 x) : M) : ℂ) := by
    intro τ x
    rw [hE]
    rfl
  have hM : ∀ τ x, embT D τ x ∈ M := fun τ x => by
    rw [hτ]
    exact Subtype.property _
  let φ : D.host.E →+* M := embE.comp (((D.host.sigmaOf (D.eTau τ).1 : D.host.E →+* D.host.E)).comp
    (D.host.conj : D.host.E →+* D.host.E))
  have hφ : ∀ y, φ y = embE (D.host.sigmaOf (D.eTau τ).1 (D.host.conj y)) := fun _ => rfl
  have hone := half_mul_inv D.host
  apply le_antisymm
  · intro x hx
    rw [GlobalTheory.Glob.mem_ellT_iff hM] at hx
    have key : ∀ z ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) * D.host.AA0,
        x * φ z ∈ ellLat D.host embE (D.eTau τ).1 := by
      intro z hz
      refine FractionalIdeal.mul_induction_on hz ?_ ?_
      · intro i hi j hj
        obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        have hint : IsIntegral ℤ (x * φ j) := by
          refine (isIntegral_algHom_iff (M.val.toRingHom.toIntAlgHom) M.val.injective).1 ?_
          have := hx j hj
          rw [hτ] at this
          exact this
        let c : 𝓞 M := ⟨x * φ j, hint⟩
        have : c • φ (b : D.host.E) ∈ ellLat D.host embE (D.eTau τ).1 :=
          Submodule.smul_mem _ _ (map_mem_ellLat D.host embE _ _
            ((mem_inv_mul_different D.host _).2 ⟨b, hb, rfl⟩))
        convert this using 1
        change x * φ (b * j) = x * φ j * φ b
        rw [map_mul]; ring
      · intro a b ha hb
        rw [map_add, mul_add]
        exact Submodule.add_mem _ ha hb
    have := key 1 (hone ▸ FractionalIdeal.one_mem_one _)
    simpa using this
  · unfold ellLat
    rw [Submodule.span_le]
    rintro x ⟨a, ha, d, hd, rfl⟩
    obtain ⟨b, hb, hab⟩ := (mem_inv_mul_different D.host (a * (d : D.host.E))).1
      (FractionalIdeal.mul_mem_mul ha ((FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩))
    rw [SetLike.mem_coe, GlobalTheory.Glob.mem_ellT_iff hM]
    intro y hy
    have h1 : (b : D.host.E) * y ∈ (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :=
      hone ▸ FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨b, hb, rfl⟩) hy
    obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [← hτ, hab, ← map_mul, ← map_mul, ← hr]
    exact map_isIntegral_int ((embT D τ).comp (D.host.conj : D.host.E →+* D.host.E)) r.isIntegral_coe

end GlobalTheory.Mem.EigenLine
