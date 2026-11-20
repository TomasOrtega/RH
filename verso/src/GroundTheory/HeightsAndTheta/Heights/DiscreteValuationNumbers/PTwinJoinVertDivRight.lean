import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (IsVertDiv mcIdeal mcMap joinCoord midDeg midVar)

noncomputable section

namespace JoinVerticalDivisorRight

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

def midNat (a : K ⊕ K' → ℕ) : K ⊕ (K₂ ⊕ K') → ℕ :=
  Sum.elim (fun k => a (.inl k)) (Sum.elim 0 (fun k => a (.inr k)))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem midNat_injective : Function.Injective (midNat (K := K) (K' := K') (K₂ := K₂)) := by
  intro a b e
  funext l
  rcases l with k | k
  · exact congrFun e (.inl k)
  · exact congrFun e (.inr (.inr k))

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem midVar_injective : Function.Injective (midVar (ι := ι) (ι' := ι') ι₂) := by
  rintro ⟨k | k, i⟩ ⟨l | l, j⟩ h <;> dsimp only [midVar] at h <;> cases h <;> rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Reduce the equality to equality of the corresponding arguments. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem mcMap_rename_midVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord w z)) (rename (midVar ι₂) h) =
      rename (Sum.map id Sum.inr) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    obtain ⟨k | k, i⟩ := v <;> simp [mcMap, midVar, joinCoord]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem rename_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord w z)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker, mcMap_rename_midVar]
  exact map_eq_zero_iff _ (rename_injective _ (Sum.map_injective.mpr ⟨Function.injective_id,
    Sum.inr_injective⟩))

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem weight_mapDomain_midVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (Finsupp.mapDomain (midVar ι₂) d) =
      midNat (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := by
  funext l
  rw [Objects.weight_blockWeight_apply]
  rcases l with k | k | k
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inl k, i⟩
  · change _ = 0
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨k' | k', j⟩, h⟩ <;> dsimp only [midVar] at h <;> cases h
  · change _ = Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)
    rw [Objects.weight_blockWeight_apply]
    exact Finset.sum_congr rfl fun i _ => Finsupp.mapDomain_apply midVar_injective d ⟨.inr k, i⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMultiHomog_rename [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [weight_mapDomain_midVar, hr])

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isMultiHomog_rename' {R : Type} [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R}
    {a : K ⊕ K' → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (midVar ι₂) f) (midNat a) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename hf

/- English proof (translation)
Proceed by induction. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Substitute using the available equality. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.
-/
theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (b : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (midVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) b h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι₂ ι'))) (midNat b)
        (rename (midVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) := isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename (ι₂ := ι₂) hm
    by_cases hb : b = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b hm hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj (fun e => hb (midNat_injective e)),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K₂ ⊕ K'), Sum.elim ι (Sum.elim ι₂ ι') k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (Sum.inr (Sum.inr k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorRight

open JoinVerticalDivisorRight in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem JoinVerticalDivisorRight.proof : JoinVerticalDivisorRight.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨midNat α, midNat β, isMultiHomog_rename' hf, isMultiHomog_rename' hg, ?_⟩, ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · exact hb (.inl k)
    · simp [midNat, midDeg]
    · exact hb (.inr k)
  · rwa [rename_mem_mcIdeal_iff]
  · rwa [rename_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_mem_mcIdeal_iff O x w z h).mpr hh))
    have hO : (Q.comap (rename (midVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (midVar ι₂) u, rename (midVar ι₂) v, ⟨_, isMultiHomog_rename' hu⟩,
      ⟨_, isMultiHomog_rename' hv⟩, huQ, hvQ, ?_⟩
    have := (rename_mem_mcIdeal_iff O x w z _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
