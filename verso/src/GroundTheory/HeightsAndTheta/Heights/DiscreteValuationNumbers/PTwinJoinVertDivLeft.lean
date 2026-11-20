import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerLast
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)

noncomputable section

namespace JoinVerticalDivisorLeft

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

/- English proof (translation)
Apply the tactic sequence `obtain ⟨k | k, i⟩ := p <;> rfl`.
-/
theorem assocVar_fst (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    (assocVar ι₂ p).1 = Sum.map id Sum.inl p.1 := by
  obtain ⟨k | k, i⟩ := p <;> rfl

/- English proof (translation)
The claim follows from `Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩`.
-/
theorem assocBlock_injective :
    Function.Injective (Sum.map id Sum.inl : K ⊕ K' → K ⊕ (K' ⊕ K₂)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on with`. Consider the case `C a => simp [mcMap, MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p n hp`. Simplify using `only [map_mul, rename_X, hp]`.

Use `congr 1`. Simplify using `[mcMap, joinCoord_assocVar, assocVar_fst]`.
-/
theorem mcMap_rename_assocVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord z w)) (rename (assocVar ι₂) h) =
      rename (Sum.map id Sum.inl) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, hp]
    congr 1
    simp [mcMap, joinCoord_assocVar, assocVar_fst]

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Simplify using `only [mcIdeal, RingHom.mem_ker]`. Rewrite using `[mcMap_rename_assocVar]`. Conclude with `map_eq_zero_iff _ (rename_injective _ assocBlock_injective)`.
-/
theorem rename_assocVar_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord z w)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker]
  rw [mcMap_rename_assocVar]
  exact map_eq_zero_iff _ (rename_injective _ assocBlock_injective)

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Apply the tactic sequence `obtain ⟨k | k, i⟩ := p <;> rcases s with l | l | l <;> simp [blockWeight, assocVar, Pi.single_apply]`.
-/
theorem blockWeight_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (p : Σ k : K ⊕ K', Sum.elim ι ι' k) (s : K ⊕ (K' ⊕ K₂)) :
    blockWeight (Sum.elim ι (Sum.elim ι' ι₂)) (assocVar ι₂ p) s =
      Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inl k))
        (Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inr k)) 0) s := by
  obtain ⟨k | k, i⟩ := p <;> rcases s with l | l | l <;> simp [blockWeight, assocVar, Pi.single_apply]

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]), Finsupp.weight_apply]`. Use function extensionality and compare the values at `s`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight_assocVar]`. Apply the tactic sequence `rcases s with l | l | l <;> simp`.
-/
theorem weight_mapDomain_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι' ι₂))) (Finsupp.mapDomain (assocVar ι₂) d) =
      Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
        (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
    Finsupp.weight_apply]
  funext s
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight_assocVar]
  rcases s with l | l | l <;> simp

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Unfold `IsMultiHomog at hf ⊢`. Proceed by induction on `hf using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => simpa using isWeightedHomogeneous_zero R _ _`. Consider the case `add p q hp hq ihp ihq => simpa [map_add] using ihp.add ihq`. Consider the case `monomial d r hr`.

Rewrite using `[rename_monomial]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Substitute `hr` using the available equality. Conclude with `weight_mapDomain_assocVar d`.
-/
theorem isMultiHomog_rename_assocVar' [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [map_add] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    exact weight_mapDomain_assocVar d

/- English proof (translation)
Rewrite `hf`, the goal using `[← Objects.isMultiHomog_iff]`. Conclude with `isMultiHomog_rename_assocVar' hf`.
-/
theorem isMultiHomog_rename_assocVar {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact isMultiHomog_rename_assocVar' hf

omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in

/- English proof (translation)
Proceed by induction on `h using MvPolynomial.induction_on' with`. Consider the case `monomial d r`. Establish `hm : IsMultiHomog (monomial d r : MRing (Sum.elim ι ι') R) (Finsupp.weight (blockWeight (Sum.elim ι ι')) d)` using `isWeightedHomogeneous_monomial _ _ _ rfl`. Establish `hj` using `isMultiHomog_rename_assocVar' (ι₂ := ι₂) hm`. Distinguish the cases in `hc : c = Finsupp.weight (blockWeight (Sum.elim ι ι')) d`.

Substitute `hc` using the available equality. Rewrite using `[IsWeightedHomogeneous.weightedHomogeneousComponent_same hm, IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]`. Establish `hc' : (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0) : K ⊕ (K' ⊕ K₂) → ℕ) ≠ Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k)) (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0)`. Introduce `e`. Apply `hc` to reduce the goal to its premises.

Use function extensionality and compare the values at `k`. Break down `k with k | k` into its components or cases. Conclude with `congrFun e (.inl k)`. Conclude with `congrFun e (.inr (.inl k))`. Rewrite using `[IsWeightedHomogeneous.weightedHomogeneousComponent_ne c hm hc, IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hc', map_zero]`.

Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem rename_weightedHomogeneousComponent [DecidableEq K] [DecidableEq K'] [DecidableEq K₂] {R : Type}
    [CommRing R] (c : K ⊕ K' → ℕ) (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) (weightedHomogeneousComponent (blockWeight (Sum.elim ι ι')) c h) =
      weightedHomogeneousComponent (blockWeight (Sum.elim ι (Sum.elim ι' ι₂)))
        (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0)) (rename (assocVar ι₂) h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have hm : IsMultiHomog (monomial d r : MRing (Sum.elim ι ι') R)
        (Finsupp.weight (blockWeight (Sum.elim ι ι')) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have hj := isMultiHomog_rename_assocVar' (ι₂ := ι₂) hm
    by_cases hc : c = Finsupp.weight (blockWeight (Sum.elim ι ι')) d
    · subst hc
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same hm,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same hj]
    · have hc' : (Sum.elim (fun k => c (.inl k)) (Sum.elim (fun k => c (.inr k)) 0) :
            K ⊕ (K' ⊕ K₂) → ℕ) ≠
          Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
            (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
        intro e
        apply hc
        funext k
        rcases k with k | k
        · exact congrFun e (.inl k)
        · exact congrFun e (.inr (.inl k))
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne c hm hc,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ hj hc', map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Rewrite `hQ`, the goal using `[← Objects.isMultiProjPrime_iff]`. Use `hQ.isPrime` as an intermediate fact. Use `⟨Ideal.comap_isPrime _ Q, fun h hh c => ?_, fun k => ?_⟩` and prove the remaining obligations. Rewrite `hh`, the goal using `[Ideal.mem_comap]`. Rewrite using `[rename_weightedHomogeneousComponent]`.

Conclude with `hQ.multiHomog _ hh _`. Break down `k with k | k` into its components or cases. Take `⟨i, hi⟩` from `hQ.relevant (.inl k)`. Conclude with `⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩`. Take `⟨i, hi⟩` from `hQ.relevant (.inr (.inl k))`.

Conclude with `⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩`.
-/
theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  rw [← Objects.isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh c => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent]
    exact hQ.multiHomog _ hh _
  · rcases k with k | k
    · obtain ⟨i, hi⟩ := hQ.relevant (.inl k)
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩
    · obtain ⟨i, hi⟩ := hQ.relevant (.inr (.inl k))
      exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end JoinVerticalDivisorLeft

open JoinVerticalDivisorLeft in

/- English proof (translation)
Introduce `O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD`. Take `⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩` from `hD`. Use `⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(k | k | k)`. Simplify `hb (.inl k)` using `[assocDeg]`.

Simplify `hb (.inr k)` using `[assocDeg]`. Simplify using `[assocDeg]`. Rewrite using `[rename_assocVar_mem_mcIdeal_iff]` and apply the resulting hypothesis. Rewrite using `[rename_assocVar_mem_mcIdeal_iff]` and apply the resulting hypothesis. Introduce `Q hQ hPQ hQO`.

Establish `hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι` using `ι) (ι' := ι') ι₂)) := fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))`. Establish `hO : (Q.comap (rename (assocVar (ι` using `ι) (ι' := ι') ι₂))).comap (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by`. Rewrite `hQO`, the goal using `[eq_bot_iff]`. Introduce `c hc`. Apply `hQO` to reduce the goal to its premises.

Simplify `hc` using `[Ideal.mem_comap, rename_C]`. Take `⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩` from `hU _ (comap_isMultiProjPrime hQ) hle hO`. Use `⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩, ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩` and prove the remaining obligations. Use `(rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv` as an intermediate fact. Simplify `this` using `only [map_sub, map_mul]`.
-/
theorem JoinVerticalDivisorLeft.proof : JoinVerticalDivisorLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · simpa [assocDeg] using hb (.inl k)
    · simpa [assocDeg] using hb (.inr k)
    · simp [assocDeg]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))
    have hO : (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩,
      ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩
    have := (rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
