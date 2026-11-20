import ReciprocityTheory.GaloisValuations.GlobalEA

noncomputable section

open NumberField IsDedekindDomain Pointwise Polynomial

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual ReciprocityTheory.Hyp

section split

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h x`. Establish `h' : σ • B = B` using `h`. Establish `e` using `ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := B) (x := x)`. Rewrite `e` using `[h']`.

Conclude with `e`. Introduce `h show σ • B = B`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h (σ⁻¹ • x), AlgEquiv.smul_def]`. Rewrite using `[show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]`.
-/
private theorem mem_decompositionSubgroup_iff_galois_valuations {K : Type*} [Field K] [Algebra K Ω] {B : ValuationSubring Ω}
    {σ : Ω ≃ₐ[K] Ω} : σ ∈ B.decompositionSubgroup K ↔ ∀ x, σ x ∈ B ↔ x ∈ B := by
  constructor
  · intro h x
    have h' : σ • B = B := h
    have e := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := B) (x := x)
    rw [h'] at e
    exact e
  · intro h
    show σ • B = B
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h (σ⁻¹ • x), AlgEquiv.smul_def]
    rw [show σ (σ⁻¹ x) = x from AlgEquiv.apply_symm_apply σ x]

/- English proof (translation)
Use `show resGal F L Ω σ ∈ A.decompositionSubgroup F ↔ σ ∈ A.decompositionSubgroup L`. Rewrite using `[mem_decompositionSubgroup_iff_galois_valuations, mem_decompositionSubgroup_iff_galois_valuations]`. Simplify using `only [resGal_apply]`.
-/
theorem resGal_mem_Dec_iff {σ : G L Ω} :
    resGal F L Ω σ ∈ Dec (F := F) A ↔ σ ∈ Dec (F := L) A := by
  show resGal F L Ω σ ∈ A.decompositionSubgroup F ↔ σ ∈ A.decompositionSubgroup L
  rw [mem_decompositionSubgroup_iff_galois_valuations, mem_decompositionSubgroup_iff_galois_valuations]
  simp only [resGal_apply]

variable (F L) in

def decRes (A : ValuationSubring Ω) : Dec (F := L) A →* Dec (F := F) A :=
  ((resGal F L Ω).comp (Dec (F := L) A).subtype).codRestrict (Dec (F := F) A)
    (fun σ => resGal_mem_Dec_iff.mpr σ.2)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem decRes_apply (σ : Dec (F := L) A) : (decRes F L A σ : G F Ω) = resGal F L Ω σ := rfl

/- English proof (translation)
Introduce `σ τ h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `x`. Use `congrArg (fun g : Dec (F := F) A => (g : G F Ω) x) h` as an intermediate fact.

Simplify `this` using `[decRes_apply, resGal_apply]`.
-/
theorem decRes_injective : Function.Injective (decRes F L A) := by
  intro σ τ h
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  have := congrArg (fun g : Dec (F := F) A => (g : G F Ω) x) h
  simpa [decRes_apply, resGal_apply] using this

/- English proof (translation)
Introduce `τ`. Take `⟨σ, hσ⟩` from `MonoidHom.mem_range.mp (h τ.2)`. Use `⟨⟨σ, resGal_mem_Dec_iff.mp (by rw [hσ]; exact τ.2)⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[decRes_apply]`.

Conclude with `hσ`.
-/
theorem decRes_surjective (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Function.Surjective (decRes F L A) := by
  intro τ
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp (h τ.2)
  refine ⟨⟨σ, resGal_mem_Dec_iff.mp (by rw [hσ]; exact τ.2)⟩, ?_⟩
  apply Subtype.ext
  rw [decRes_apply]
  exact hσ

/- English proof (translation)
Use `continuous_induced_rng.2 ?_` and prove the remaining obligations. Establish `hc : Continuous (resGal F L Ω)` using `(isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).continuous`. Establish `e : ((↑) : Dec (F` using `F) A → G F Ω) ∘ decRes F L A = resGal F L Ω ∘ ((↑) : Dec (F := L) A → G L Ω) := by`. Use function extensionality and compare the values at `σ`. Conclude with `decRes_apply σ`.

Rewrite using `[e]`. Conclude with `hc.comp continuous_subtype_val`.
-/
theorem continuous_decRes [IsAlgClosure F Ω] : Continuous (decRes F L A) := by
  refine continuous_induced_rng.2 ?_
  have hc : Continuous (resGal F L Ω) :=
    (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).continuous
  have e : ((↑) : Dec (F := F) A → G F Ω) ∘ decRes F L A =
      resGal F L Ω ∘ ((↑) : Dec (F := L) A → G L Ω) := by
    funext σ
    exact decRes_apply σ
  rw [e]
  exact hc.comp continuous_subtype_val

def decEquiv [IsAlgClosure F Ω] (h : Dec (F := F) A ≤ (resGal F L Ω).range) :
    Dec (F := L) A ≃ₜ* Dec (F := F) A where
  toMulEquiv := MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩
  continuous_toFun := continuous_decRes
  continuous_invFun := by
    have hI : Topology.IsInducing (resGal F L Ω) :=
      (isClosedEmbedding_resGal (F := F) (L := L) (Ω := Ω)).toIsEmbedding.toIsInducing
    refine continuous_induced_rng.2 (hI.continuous_iff.2 ?_)
    convert (continuous_subtype_val : Continuous (fun τ : Dec (F := F) A => (τ : G F Ω))) using 1
    funext τ
    exact congrArg Subtype.val
      ((MulEquiv.ofBijective (decRes F L A) ⟨decRes_injective, decRes_surjective h⟩).apply_symm_apply τ)

/- English proof (translation)
Establish `e : normV v = Ideal.absNorm v.asIdeal`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Establish `h1 : Ideal.absNorm v.asIdeal ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Conclude with `v.isPrime.ne_top`.

Use linear arithmetic over natural numbers and integers.
-/
theorem one_lt_normV (v : HeightOneSpectrum (𝓞 F)) : 1 < normV v := by
  have e : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [e]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

end split

section frob

variable {F L Ω : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Field Ω] [Algebra F L]
  [Algebra F Ω] [Algebra L Ω] [IsScalarTower F L Ω] {A : ValuationSubring Ω}

end frob

section conj

variable {L Ω : Type*} [Field L] [NumberField L] [Field Ω] [Algebra L Ω]

def mapPlace (τ : Ω ≃+* Ω) (A : ValuationSubring Ω) : ValuationSubring Ω :=
  A.comap τ.symm.toRingHom

def conjV (s : L ≃+* L) (w : HeightOneSpectrum (𝓞 L)) : HeightOneSpectrum (𝓞 L) where
  asIdeal := w.asIdeal.comap (RingOfIntegers.mapRingEquiv s.symm : 𝓞 L →+* 𝓞 L)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    refine (Submodule.ne_bot_iff _).mpr ⟨RingOfIntegers.mapRingEquiv s y, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      convert hy using 1
      exact RingOfIntegers.ext (by simp)
    · exact (map_ne_zero_iff _ (RingOfIntegers.mapRingEquiv s).injective).mpr hy0

variable (s : L ≃+* L) (τ : Ω ≃+* Ω) (hτ : ∀ x : L, τ (algebraMap L Ω x) = algebraMap L Ω (s x))

end conj

end ReciprocityTheory.Gal
