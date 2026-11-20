import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
open scoped Pointwise

namespace GlobalTheory.SplitCriterion

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N] [IsGalois K N]

/- English proof (translation)
Use `𝔭.isPrime` as an intermediate fact. Use `𝔭.isMaximal` as an intermediate fact. Establish `hne : P ≠ ⊥` using `Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P`. Establish `: Finite (𝓞 N ⧸ P)` using `Ideal.finiteQuotientOfFreeOfNeBot _ hne`. Establish `: Finite (𝓞 K ⧸ 𝔭.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot`.

Establish `: P.IsMaximal` using `hP.isMaximal hne`. Take `⟨σ, hσ⟩` from `IsArithFrobAt.exists_of_isInvariant (𝓞 K) (N ≃ₐ[K] N) P`. Establish `hu : P.under (𝓞 K) = 𝔭.asIdeal` using `hPo.over.symm`. Use `set q := Ideal.absNorm 𝔭.asIdeal with hq`. Establish `hq' : q = Nat.card (𝓞 K ⧸ 𝔭.asIdeal)` using `by rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Establish `hσ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ q` using `fun x => by`. Use `hσ x` as an intermediate fact. Rewrite `this` using `[hu, ← hq']`. Rewrite using `[← map_pow, Ideal.Quotient.eq]`. Conclude with `this`.

Establish `hσH : σ ∈ H` using `h σ ⟨P, hP, hPo, fun x => by`. Rewrite using `[← Ideal.Quotient.eq, map_pow]`. Conclude with `hσ' x⟩`. Establish `hpow : ∀ (i : ℕ) (x : 𝓞 N), Ideal.Quotient.mk P ((σ ^ i) • x) = Ideal.Quotient.mk P x ^ (q ^ i)`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => intro x`. Rewrite using `[pow_succ', mul_smul, hσ', ih, ← pow_mul, pow_succ]`. Use `letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _`.

Use `letI : Field (𝓞 N ⧸ P) := Ideal.Quotient.field _`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)`. Establish `: Fact p.Prime` using `⟨CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p⟩`. Take `⟨i, hi⟩` from `FiniteField.exists_forall_apply_eq_pow (𝓞 K ⧸ 𝔭.asIdeal) p (𝓞 N ⧸ P) (Ideal.Quotient.stabilizerHom P 𝔭.asIdeal (N ≃ₐ[K] N) ⟨τ, hτ⟩)`. Establish `hτ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (τ • x) = Ideal.Quotient.mk P x ^ (q ^ i)` using `fun x => by`.

Rewrite using `[hq', ← hi, Ideal.Quotient.stabilizerHom_apply]`. Both sides reduce to the same expression. Establish `h1 : σ * τ * (σ ^ i)⁻¹ ∈ H` using `h _ ⟨P, hP, hPo, fun x => by`. Rewrite using `[← Ideal.Quotient.eq, map_pow, mul_smul, mul_smul, hσ', hτ', ← hpow, smul_inv_smul]⟩`. Establish `h2` using `H.mul_mem (H.mul_mem (H.inv_mem hσH) h1) (H.pow_mem hσH i)`.

Simplify `h2` using `[mul_assoc]`.
-/
theorem mem_of_smul_eq (H : Subgroup (N ≃ₐ[K] N)) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ H) (P : Ideal (𝓞 N)) [hP : P.IsPrime] [hPo : P.LiesOver 𝔭.asIdeal]
    (τ : N ≃ₐ[K] N) (hτ : τ • P = P) : τ ∈ H := by
  have := 𝔭.isPrime
  have := 𝔭.isMaximal
  have hne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot P
  have : Finite (𝓞 N ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
  have : Finite (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ 𝔭.ne_bot
  have : P.IsMaximal := hP.isMaximal hne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 K) (N ≃ₐ[K] N) P
  have hu : P.under (𝓞 K) = 𝔭.asIdeal := hPo.over.symm
  set q := Ideal.absNorm 𝔭.asIdeal with hq
  have hq' : q = Nat.card (𝓞 K ⧸ 𝔭.asIdeal) := by rw [hq, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hσ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (σ • x) = Ideal.Quotient.mk P x ^ q := fun x => by
    have := hσ x
    rw [hu, ← hq'] at this
    rw [← map_pow, Ideal.Quotient.eq]
    exact this
  have hσH : σ ∈ H := h σ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow]; exact hσ' x⟩
  have hpow : ∀ (i : ℕ) (x : 𝓞 N), Ideal.Quotient.mk P ((σ ^ i) • x) = Ideal.Quotient.mk P x ^ (q ^ i) := by
    intro i
    induction i with
    | zero => simp
    | succ i ih => intro x; rw [pow_succ', mul_smul, hσ', ih, ← pow_mul, pow_succ]
  letI : Field (𝓞 K ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 N ⧸ P) := Ideal.Quotient.field _
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 K ⧸ 𝔭.asIdeal)
  have : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 K ⧸ 𝔭.asIdeal) p⟩
  obtain ⟨i, hi⟩ := FiniteField.exists_forall_apply_eq_pow (𝓞 K ⧸ 𝔭.asIdeal) p (𝓞 N ⧸ P)
    (Ideal.Quotient.stabilizerHom P 𝔭.asIdeal (N ≃ₐ[K] N) ⟨τ, hτ⟩)
  have hτ' : ∀ x : 𝓞 N, Ideal.Quotient.mk P (τ • x) = Ideal.Quotient.mk P x ^ (q ^ i) := fun x => by
    rw [hq', ← hi, Ideal.Quotient.stabilizerHom_apply]
    rfl
  have h1 : σ * τ * (σ ^ i)⁻¹ ∈ H := h _ ⟨P, hP, hPo, fun x => by
    rw [← Ideal.Quotient.eq, map_pow, mul_smul, mul_smul, hσ', hτ', ← hpow, smul_inv_smul]⟩
  have h2 := H.mul_mem (H.mul_mem (H.inv_mem hσH) h1) (H.pow_mem hσH i)
  simpa [mul_assoc] using h2

/- English proof (translation)
Use `𝔭.isPrime` as an intermediate fact. Establish `hH : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ M.fixingSubgroup` using `fun σ hσ => (IntermediateField.mem_fixingSubgroup_iff _ _).2 (h σ hσ)`. Take `⟨P, hP, hPo⟩` from `(inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 N)))`. Set `f : (N ≃ₐ[K] N) → Ideal (𝓞 M)` to `fun σ => (σ⁻¹ • P).under (𝓞 M)`. Establish `hker : ∀ σ τ, f σ = f τ ↔ σ⁻¹ * τ ∈ M.fixingSubgroup`.

Introduce `σ τ`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 M) (𝓞 N) (N ≃ₐ[M] N) (σ⁻¹ • P) (τ⁻¹ • P) e`. Establish `hg' : τ⁻¹ • P = (g.restrictScalars K) • (σ⁻¹ • P)`.

Rewrite using `[hg]`. Both sides reduce to the same expression. Establish `hgH : g.restrictScalars K ∈ M.fixingSubgroup` using `(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩`. Establish `h1` using `mem_of_smul_eq M.fixingSubgroup 𝔭 hH (σ⁻¹ • P) (σ⁻¹ * τ * g.restrictScalars K) (by`. Rewrite using `[mul_smul, ← hg', mul_smul, smul_inv_smul])`.

Conclude with `(M.fixingSubgroup.mul_mem_cancel_right hgH).1 h1`. Introduce `e`. Establish `e'` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 e`. Use extensionality with `x`. Simplify using `only [f, Ideal.under, Ideal.mem_comap, Ideal.mem_inv_pointwise_smul_iff]`.

Establish `: (σ⁻¹ * τ) • algebraMap (𝓞 M) (𝓞 N) x = algebraMap (𝓞 M) (𝓞 N) x`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Conclude with `e' _ (x : M).2`. Rewrite `this` using `[mul_smul, inv_smul_eq_iff]`. Rewrite using `[this]`.

Establish `hr : Set.range f = 𝔭.asIdeal.primesOver (𝓞 M)`. Use extensionality with `Q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, rfl⟩`. Use `⟨inferInstance, ⟨?_⟩⟩` and prove the remaining obligations.

Simplify using `only [f]`. Rewrite using `[Ideal.under_under]`. Conclude with `Ideal.LiesOver.over`. Introduce and unpack `⟨hQ, hQo⟩`. Take `⟨P', hP', hPo'⟩` from `(inferInstance : Nonempty (Q.primesOver (𝓞 N)))`.

Establish `: P'.LiesOver 𝔭.asIdeal` using `Ideal.LiesOver.trans P' Q _`. Take `⟨g, hg⟩` from `Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 K) (𝓞 N) (N ≃ₐ[K] N) P P' (hPo.over.symm.trans this.over)`. Conclude with `⟨g⁻¹, by simp only [f]; rw [inv_inv, ← hg]; exact hPo'.over.symm⟩`. Establish `hs : (fun Q : HeightOneSpectrum (𝓞 M) => Q.asIdeal) '' {Q | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal} = 𝔭.asIdeal.primesOver (𝓞 M)`. Use extensionality with `Q`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, rfl⟩`. Conclude with `⟨Q.isPrime, ⟨Eq.symm hQ⟩⟩`. Introduce and unpack `⟨hQ, hQo⟩`. Conclude with `⟨⟨Q, hQ, Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q⟩, hQo.over.symm, rfl⟩`.

Rewrite using `[← Set.ncard_image_of_injective _ (fun _ _ e => HeightOneSpectrum.ext e), hs, ← hr, IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq, ← Nat.card_congr (Setoid.quotientKerEquivRange f)]`. Establish `: Setoid.ker f = QuotientGroup.leftRel M.fixingSubgroup`. Use extensionality with `σ τ`. Rewrite using `[Setoid.ker_def, QuotientGroup.leftRel_apply, hker]`. Rewrite using `[this]`.

Both sides reduce to the same expression.
-/
theorem ncard_primes_eq_finrank_of_frob_fix (K N : Type) [Field K] [NumberField K] [Field N] [NumberField N]
    [Algebra K N] [IsGalois K N] (M : IntermediateField K N) (𝔭 : HeightOneSpectrum (𝓞 K))
    (h : ∀ (σ : N ≃ₐ[K] N), GlobalTheory.NT.IsFrob N 𝔭 σ → ∀ x ∈ M, σ x = x) :
    {Q : HeightOneSpectrum (𝓞 M) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 M)) = 𝔭.asIdeal}.ncard
      = Module.finrank K M := by
  have := 𝔭.isPrime
  have hH : ∀ σ, GlobalTheory.NT.IsFrob N 𝔭 σ → σ ∈ M.fixingSubgroup := fun σ hσ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 (h σ hσ)
  obtain ⟨P, hP, hPo⟩ := (inferInstance : Nonempty (𝔭.asIdeal.primesOver (𝓞 N)))
  let f : (N ≃ₐ[K] N) → Ideal (𝓞 M) := fun σ => (σ⁻¹ • P).under (𝓞 M)
  have hker : ∀ σ τ, f σ = f τ ↔ σ⁻¹ * τ ∈ M.fixingSubgroup := by
    intro σ τ
    constructor
    · intro e
      obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 M) (𝓞 N) (N ≃ₐ[M] N)
        (σ⁻¹ • P) (τ⁻¹ • P) e
      have hg' : τ⁻¹ • P = (g.restrictScalars K) • (σ⁻¹ • P) := by
        rw [hg]; rfl
      have hgH : g.restrictScalars K ∈ M.fixingSubgroup :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => g.commutes ⟨x, hx⟩
      have h1 := mem_of_smul_eq M.fixingSubgroup 𝔭 hH (σ⁻¹ • P) (σ⁻¹ * τ * g.restrictScalars K) (by
        rw [mul_smul, ← hg', mul_smul, smul_inv_smul])
      exact (M.fixingSubgroup.mul_mem_cancel_right hgH).1 h1
    · intro e
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
    IntermediateField.finrank_eq_fixingSubgroup_index, Subgroup.index, ← Nat.card_coe_set_eq,
    ← Nat.card_congr (Setoid.quotientKerEquivRange f)]
  have : Setoid.ker f = QuotientGroup.leftRel M.fixingSubgroup := by
    ext σ τ
    rw [Setoid.ker_def, QuotientGroup.leftRel_apply, hker]
  rw [this]
  rfl

end GlobalTheory.SplitCriterion
