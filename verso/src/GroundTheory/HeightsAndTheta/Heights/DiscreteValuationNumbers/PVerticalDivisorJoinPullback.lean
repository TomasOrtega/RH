import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsVerticalDivisorJoinPullback
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

section JoinPullback

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem joinCoords_inl {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (k : K)
    (i : ι k) : joinCoords y y' ⟨Sum.inl k, i⟩ = y ⟨k, i⟩ := rfl

/- English proof (translation)
Simplify using `only [pointConeMap, joinForm, aeval_rename]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [algebraMap_eq]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p v hp`.

Take `⟨k, i⟩` from `v`. Simplify using `[hp, joinCoords_inl]`.
-/
theorem pointConeMap_joinCoords_joinForm {Ω : Type*} [Field Ω] (R : Type*) [CommRing R]
    [Algebra R Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    pointConeMap R (joinCoords y y') (joinForm f) =
      rename (Sum.inl : K → K ⊕ K') (pointConeMap R y f) := by
  simp only [pointConeMap, joinForm, aeval_rename]
  induction f using MvPolynomial.induction_on with
  | C a => simp [algebraMap_eq]
  | add p q hp hq => simp [hp, hq]
  | mul_X p v hp =>
    obtain ⟨k, i⟩ := v
    simp [hp, joinCoords_inl]

/- English proof (translation)
Simplify using `only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]`. Conclude with `map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)`.
-/
theorem joinForm_mem_pointIdeal_iff {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω]
    (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω) (f : MRing ι R) :
    joinForm f ∈ pointIdeal R (joinCoords y y') ↔ f ∈ pointIdeal R y := by
  simp only [pointIdeal, RingHom.mem_ker, pointConeMap_joinCoords_joinForm]
  exact map_eq_zero_iff _ (rename_injective _ Sum.inl_injective)

/- English proof (translation)
Unfold `IsMultiHomog at hf ⊢`. Proceed by induction on `hf using IsWeightedHomogeneous.induction_on with`. Consider the case `zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _`. Consider the case `add p q hp hq ihp ihq => simpa [joinForm, map_add] using ihp.add ihq`. Consider the case `monomial d r hr`.

Simplify using `only [joinForm, rename_monomial]`. Apply `isWeightedHomogeneous_monomial` to reduce the goal to its premises. Substitute `hr` using the available equality. Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]), Finsupp.weight_apply]`. Use function extensionality and compare the values at `s`.

Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]`. Break down `s with k | k` into its components or cases. Simplify using `[Pi.single_apply]`. Simplify using the standard rewrite rules.
-/
theorem isMultiHomog_joinForm [DecidableEq K] [DecidableEq K'] {R : Type*} [CommRing R]
    {f : MRing ι R} {bf : K → ℕ} (hf : IsMultiHomog f bf) :
    IsMultiHomog (joinForm (ι' := ι') f) (Sum.elim bf 0) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa [joinForm] using isWeightedHomogeneous_zero R _ _
  | add p q hp hq ihp ihq => simpa [joinForm, map_add] using ihp.add ihq
  | monomial d r hr =>
    simp only [joinForm, rename_monomial]
    apply isWeightedHomogeneous_monomial
    subst hr
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
      Finsupp.weight_apply]
    funext s
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, blockWeight]
    rcases s with k | k
    · simp [Pi.single_apply]
    · simp

end JoinPullback

/- English proof (translation)
Introduce `O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD`. Use `IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_` and prove the remaining obligations. Take `⟨bf, bg, hf, hg, hb⟩` from `hD.degrees`. Use `⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`.

Break down `s with k | k` into its components or cases. Simplify using `[joinDeg, ← hb]`. Simplify using `[joinDeg]`. Rewrite using `[joinForm_mem_pointIdeal_iff]`. Conclude with `hD.num_not_mem`.

Rewrite using `[joinForm_mem_pointIdeal_iff]`. Conclude with `hD.den_not_mem`. Introduce `W hW hPW hrel hϖ`. Set `φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O` to `rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))`. Establish `hφ : ∀ h, joinForm (ι'` using `ι') h = φ h := fun _ => rfl`.

Establish `hle : pointIdeal O y ≤ W.comap φ`. Introduce `h hh`. Rewrite using `[Ideal.mem_comap, ← hφ]`. Conclude with `hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)`. Establish `hrel' : IsRelevant (W.comap φ)`.

Introduce `k`. Take `⟨i, hi⟩` from `hrel (Sum.inl k)`. Conclude with `⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩`. Establish `hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ`. Rewrite using `[Ideal.mem_comap]`.

Simplify `hϖ` using `[φ, rename_C]`. Take `⟨u, v, hu, hv, huv⟩` from `hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'`. Use `⟨joinForm u, joinForm v, hu, hv, ?_⟩` and prove the remaining obligations. Use `(joinForm_mem_pointIdeal_iff O y y' _).mpr huv` as an intermediate fact. Simplify `this` using `[hφ, map_sub, map_mul]`.
-/
theorem VerticalDivisorJoinPullback.proof : VerticalDivisorJoinPullback.Statement := by
  intro O _ _ _ ϖ Ω _ _ K _ _ ι _ K' _ _ ι' _ y y' b f g hD
  refine IsVerticalDivisor.of_unit_off_special ?_ ?_ ?_ ?_
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine ⟨Sum.elim bf 0, Sum.elim bg 0, isMultiHomog_joinForm hf, isMultiHomog_joinForm hg, ?_⟩
    funext s
    rcases s with k | k
    · simp [joinDeg, ← hb]
    · simp [joinDeg]
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.num_not_mem
  · rw [joinForm_mem_pointIdeal_iff]; exact hD.den_not_mem
  · intro W hW hPW hrel hϖ
    let φ : MRing ι O →ₐ[O] MRing (Sum.elim ι ι') O :=
      rename (fun p : (Σ k, ι k) => (⟨Sum.inl p.1, p.2⟩ : Σ s : K ⊕ K', Sum.elim ι ι' s))
    have hφ : ∀ h, joinForm (ι' := ι') h = φ h := fun _ => rfl
    have hle : pointIdeal O y ≤ W.comap φ := by
      intro h hh
      rw [Ideal.mem_comap, ← hφ]
      exact hPW ((joinForm_mem_pointIdeal_iff O y y' h).mpr hh)
    have hrel' : IsRelevant (W.comap φ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (Sum.inl k)
      exact ⟨i, by rw [Ideal.mem_comap]; simpa [φ, rename_X] using hi⟩
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap φ := by
      rw [Ideal.mem_comap]; simpa [φ, rename_C] using hϖ
    obtain ⟨u, v, hu, hv, huv⟩ :=
      hD.unit_off_special (W.comap φ) (Ideal.comap_isPrime φ W) hle hrel' hϖ'
    refine ⟨joinForm u, joinForm v, hu, hv, ?_⟩
    have := (joinForm_mem_pointIdeal_iff O y y' _).mpr huv
    simpa [hφ, map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
