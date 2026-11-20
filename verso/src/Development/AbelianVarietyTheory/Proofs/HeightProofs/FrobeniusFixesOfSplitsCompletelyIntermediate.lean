import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

/- English proof (translation)
Use `𝔭.isPrime` as an intermediate fact. Take `⟨P, hP, hPo, hx⟩` from `hσ`. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P`. Establish `hPm : P.IsMaximal` using `hP.isMaximal hne`. Establish `hq : Ideal.absNorm 𝔭.asIdeal ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `𝔭.ne_bot`. Establish `hfix : σ⁻¹ • P = P`. Use `symm`. Use `hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hxP => ?_` and prove the remaining obligations.

Rewrite using `[Ideal.mem_inv_pointwise_smul_iff]`. Establish `h1` using `P.add_mem (hx x) (P.pow_mem_of_mem hxP _ (Nat.pos_of_ne_zero hq))`. Rewrite `h1` using `[sub_add_cancel]`. Conclude with `h1`. Set `f : (N ≃ₐ[K] N) → Ideal (𝓞 M)` to `fun σ => (σ⁻¹ • P).under (𝓞 M)`.

Establish `hker : ∀ σ τ, σ⁻¹ * τ ∈ M.fixingSubgroup → f σ = f τ`. Introduce `σ τ e`. Establish `e'` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 e`. Use extensionality with `x`. Simplify using `only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]`.

Establish `: (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `e' _ (x : M).2`. Rewrite `this` using `[mul_smul, inv_smul_eq_iff]`. Rewrite using `[this]`.

Establish `hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M)`. Use extensionality with `Q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, rfl⟩`. Use `⟨inferInstance, ⟨?_⟩⟩` and prove the remaining obligations.

Simplify using `only [f]`. Rewrite using `[Ideal.under_under]`. Conclude with `Ideal.LiesOver.over`. Introduce and unpack `⟨hQ, hQo⟩`. Take `⟨P', hP', hPo'⟩` from `(inferInstance : Nonempty (Q.primesOver (𝓞 N)))`.

Establish `: P'.LiesOver 𝔭.asIdeal` using `Ideal.LiesOver.trans P' Q _`. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P' (hPo.over.symm.trans this.over)`. Conclude with `⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩`. Establish `hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) '' {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M)`. Use extensionality with `Q`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, rfl⟩`. Conclude with `⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩`. Introduce and unpack `⟨hQ, hQo⟩`. Conclude with `⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩`.

Rewrite `h` using `[← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr, IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq]`. Set `F : (N ≃ₐ[K] N) ⧸ M.fixingSubgroup → Set.range f` to `Quotient.lift (fun g => ⟨f g, g, rfl⟩) fun a b e => Subtype.ext (hker a b (QuotientGroup.leftRel_apply.1 e))`. Establish `hF : Function.Surjective F`. Introduce and unpack `⟨_, g, rfl⟩`. Conclude with `⟨QuotientGroup.mk g, rfl⟩`.

Establish `hinj : Function.Injective F` using `(hF.bijective_of_nat_card_le h.ge).1`. Establish `h1 : F (QuotientGroup.mk 1) = F (QuotientGroup.mk σ)`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `f 1 = f σ`. Simplify using `only [f]`.

Rewrite using `[hfix, inv_one, one_smul]`. Establish `h2` using `QuotientGroup.eq.1 (hinj h1)`. Rewrite `h2` using `[inv_one, one_mul]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 h2`.
-/
theorem frob_fix_of_ncard_primes_eq_finrank (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M) (σ : N ≃ₐ[K] N) (hσ : GlobalTheory.NT.IsFrob N 𝔭 σ) : ∀ x ∈ M, σ x = x := by
  have := 𝔭.isPrime
  obtain ⟨P, hP, hPo, hx⟩ := hσ
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have hPm : P.IsMaximal := hP.isMaximal hne
  have hq : Ideal.absNorm 𝔭.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact 𝔭.ne_bot
  have hfix : σ⁻¹ • P = P := by
    symm
    refine hPm.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun x hxP => ?_
    rw [Ideal.mem_inv_pointwise_smul_iff]
    have h1 := P.add_mem (hx x) (P.pow_mem_of_mem hxP _ (Nat.pos_of_ne_zero hq))
    rw [sub_add_cancel] at h1
    exact h1
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, σ⁻¹ * τ ∈ M.fixingSubgroup → f σ = f τ := by
    intro σ τ e
    have e' := (IntermediateField.mem_fixingSubgroup_iff _ _).1 e
    ext x
    simp only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]
    have : (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x := by
      apply RingOfIntegers.ext
      exact e' _ (x : M).2
    rw [mul_smul, inv_smul_eq_iff] at this
    rw [this]
  have hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨σ, rfl⟩
      refine ⟨inferInstance, ⟨?_⟩⟩
      simp only [f]
      rw [Ideal.under_under]
      exact Ideal.LiesOver.over
    · rintro ⟨hQ, hQo⟩
      obtain ⟨P', hP', hPo'⟩ := (inferInstance : Nonempty (Q.primesOver (𝓞 N)))
      have : P'.LiesOver 𝔭.asIdeal := Ideal.LiesOver.trans P' Q _
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P'
        (hPo.over.symm.trans this.over)
      exact ⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩
  have hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) ''
      {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M) := by
    ext Q
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      exact ⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩
    · rintro ⟨hQ, hQo⟩
      exact ⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩
  rw [← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr,
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq] at h
  let F : (N ≃ₐ[K] N) ⧸ M.fixingSubgroup → Set.range f :=
    Quotient.lift (fun g => ⟨f g, g, rfl⟩) fun a b e =>
      Subtype.ext (hker a b (QuotientGroup.leftRel_apply.1 e))
  have hF : Function.Surjective F := by
    rintro ⟨_, g, rfl⟩
    exact ⟨QuotientGroup.mk g, rfl⟩
  have hinj : Function.Injective F := (hF.bijective_of_nat_card_le h.ge).1
  have h1 : F (QuotientGroup.mk 1) = F (QuotientGroup.mk σ) := by
    apply Subtype.ext
    change f 1 = f σ
    simp only [f]
    rw [hfix, inv_one, one_smul]
  have h2 := QuotientGroup.eq.1 (hinj h1)
  rw [inv_one, one_mul] at h2
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 h2

end GlobalTheory.SplitCriterion
