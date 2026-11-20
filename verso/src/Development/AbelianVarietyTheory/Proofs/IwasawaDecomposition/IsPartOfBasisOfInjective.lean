import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal

open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Take `⟨ψ, hψ⟩` from `h.exists_dual`. Take `⟨n', b, -⟩` from `h`. Set `π : L →ₗ[ℤ] (Fin m → ℤ)` to `LinearMap.pi fun i => ψ i ∘ₗ f`. Set `s : (Fin m → ℤ) →ₗ[ℤ] L` to `∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)`. Establish `hs : ∀ c, s c = ∑ i, c i • v i` using `fun c => by simp [s, LinearMap.sum_apply]`.

Establish `hπ : ∀ c, π (s c) = c` using `fun c => by`. Use extensionality with `j`. Simplify using `[π, hs, map_sum, hψ]`. Set `K` to `LinearMap.ker π`. Take `⟨n, bK'⟩` from `Submodule.basisOfPid b (K.map f)`.

Set `bK` to `bK'.map (Submodule.equivMapOfInjective f hf K).symm`. Establish `hinj : Function.Injective (s.coprod K.subtype)`. Use `(injective_iff_map_eq_zero _).2 ?_` and prove the remaining obligations. Introduce and unpack `⟨c, k⟩ h0`. Establish `h1 : s c + (k : L) = 0` using `by simpa using h0`.

Establish `h2 : π (k : L) = 0` using `k.2`. Establish `h3 : c = 0` using `by simpa [h2, hπ] using congrArg π h1`. Substitute `h3` using the available equality. Establish `h4 : (k : L) = 0` using `by simpa using h1`. Conclude with `Prod.ext rfl (Subtype.ext h4)`.

Establish `hsurj : Function.Surjective (s.coprod K.subtype)` using `fun x => ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩`. Set `E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L` to `LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩`. Use `⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩` and prove the remaining obligations. Establish `h1 : E (Pi.single i 1, 0) = v i`. Express the relevant statement in the definitionally equal form `(s.coprod K.subtype) (Pi.single i 1, 0) = v i`.

Simplify using `[hs, Pi.single_apply]`. Simplify using `using h1`.
-/
theorem isPartOfBasis_of_injective {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m : ℕ} (f : L →ₗ[ℤ] L')
    (hf : Function.Injective f) {v : Fin m → L} (h : IsPartOfBasis fun i => f (v i)) : IsPartOfBasis v := by
  classical
  obtain ⟨ψ, hψ⟩ := h.exists_dual
  obtain ⟨n', b, -⟩ := h
  let π : L →ₗ[ℤ] (Fin m → ℤ) := LinearMap.pi fun i => ψ i ∘ₗ f
  let s : (Fin m → ℤ) →ₗ[ℤ] L := ∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hs : ∀ c, s c = ∑ i, c i • v i := fun c => by simp [s, LinearMap.sum_apply]
  have hπ : ∀ c, π (s c) = c := fun c => by
    ext j
    simp [π, hs, map_sum, hψ]
  let K := LinearMap.ker π
  obtain ⟨n, bK'⟩ := Submodule.basisOfPid b (K.map f)
  let bK := bK'.map (Submodule.equivMapOfInjective f hf K).symm
  have hinj : Function.Injective (s.coprod K.subtype) := by
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨c, k⟩ h0
    have h1 : s c + (k : L) = 0 := by simpa using h0
    have h2 : π (k : L) = 0 := k.2
    have h3 : c = 0 := by simpa [h2, hπ] using congrArg π h1
    subst h3
    have h4 : (k : L) = 0 := by simpa using h1
    exact Prod.ext rfl (Subtype.ext h4)
  have hsurj : Function.Surjective (s.coprod K.subtype) := fun x =>
    ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩
  let E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩
  have h1 : E (Pi.single i 1, 0) = v i := by
    change (s.coprod K.subtype) (Pi.single i 1, 0) = v i
    simp [hs, Pi.single_apply]
  simpa using h1

/- English proof (translation)
Introduce `O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h`. Establish `hmem : ∀ i, γ i ∈ balForms bar X₁` using `fun i => by`. Use `⟨fun y z => ?_, fun a y z => ?_⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hr y`. Take `⟨z, rfl⟩` from `hr z`.

Conclude with `(h.mem i).1 y z`. Take `⟨y, rfl⟩` from `hr y`. Take `⟨z, rfl⟩` from `hr z`. Simplify `(h.mem i).2 a y z` using `only [pull_apply, map_smul]`. Establish `hinj : Function.Injective (pullBal bar r)` using `fun β β' e => Subtype.ext (LinearMap.ext₂ fun a b => by`.

Take `⟨a, rfl⟩` from `hr a`. Take `⟨b, rfl⟩` from `hr b`. Conclude with `LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)`. Use `⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis, (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩` and prove the remaining obligations. Take `⟨y, rfl⟩` from `hr y`.

Conclude with `h.nonneg i y`.
-/
theorem isCone_of_pull : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X X₁ : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X₁), Function.Surjective r → IsCone bar φ (fun i => pull r (γ i)) →
    IsCone bar φ γ := by
  intro O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h
  have hmem : ∀ i, γ i ∈ balForms bar X₁ := fun i => by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      exact (h.mem i).1 y z
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      simpa only [pull_apply, map_smul] using (h.mem i).2 a y z
  have hinj : Function.Injective (pullBal bar r) := fun β β' e =>
    Subtype.ext (LinearMap.ext₂ fun a b => by
      obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      exact LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)
  refine ⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis,
    (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩
  obtain ⟨y, rfl⟩ := hr y
  exact h.nonneg i y

end GlobalTheory.PolFan
