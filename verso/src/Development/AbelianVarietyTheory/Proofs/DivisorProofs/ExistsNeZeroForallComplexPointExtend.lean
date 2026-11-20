import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues

open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `revert h0`. Proceed by induction on `s, hs using Topology.IsConstructible.induction_of_isTopologicalBasis _ (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)) with`. Consider the case `isCompact_basis i => exact PrimeSpectrum.isCompact_basicOpen _`. Consider the case `sdiff i t ht`. Introduce `h0`.

Simplify using `only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_exists, not_not] at h0`. Use `⟨i, fun hi => h0.1 (by simp [hi]), fun p hp => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, not_exists, not_not]`. Use `⟨hp, fun j hj => ?_⟩` and prove the remaining obligations. Establish `hj0 : j = 0` using `by simpa using h0.2 j hj`.

Simplify using `[hj0]`. Consider the case `union s hs t ht Hs Ht`. Introduce and unpack `(h0 | h0)`. Take `⟨q, hq, hsub⟩` from `Hs h0`. Conclude with `⟨q, hq, fun p hp => Or.inl (hsub p hp)⟩`.

Take `⟨q, hq, hsub⟩` from `Ht h0`. Conclude with `⟨q, hq, fun p hp => Or.inr (hsub p hp)⟩`.
-/
theorem exists_basicOpen_subset_of_isConstructible_of_bot_mem {B : Type*} [CommRing B] [IsDomain B]
    {s : Set (PrimeSpectrum B)} (hs : Topology.IsConstructible s)
    (h0 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ s) :
    ∃ q : B, q ≠ 0 ∧ ∀ p : PrimeSpectrum B, q ∉ p.asIdeal → p ∈ s := by
  revert h0
  induction s, hs using Topology.IsConstructible.induction_of_isTopologicalBasis
      _ (PrimeSpectrum.isTopologicalBasis_basic_opens (R := B)) with
  | isCompact_basis i => exact PrimeSpectrum.isCompact_basicOpen _
  | sdiff i t ht =>
    intro h0
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not] at h0

    refine ⟨i, fun hi => h0.1 (by simp [hi]), fun p hp => ?_⟩
    simp only [Set.mem_sdiff, Set.mem_iUnion, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
      not_exists, not_not]
    refine ⟨hp, fun j hj => ?_⟩
    have hj0 : j = 0 := by simpa using h0.2 j hj
    simp [hj0]
  | union s hs t ht Hs Ht =>
    rintro (h0 | h0)
    · obtain ⟨q, hq, hsub⟩ := Hs h0
      exact ⟨q, hq, fun p hp => Or.inl (hsub p hp)⟩
    · obtain ⟨q, hq, hsub⟩ := Ht h0
      exact ⟨q, hq, fun p hp => Or.inr (hsub p hp)⟩

/- English proof (translation)
Take `⟨P, hP⟩` from `h`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Establish `hPp : RingHom.ker φ = P.asIdeal.comap (algebraMap B A)`. Use `congrArg PrimeSpectrum.asIdeal hP` as an intermediate fact. Simplify using `using this.symm`.

Set `σ : (RingHom.ker φ).ResidueField →+* L` to `Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl (fun x hx => by`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]`. Conclude with `isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0))`. Set `g : (RingHom.ker φ).ResidueField →ₐ[B] P.asIdeal.ResidueField` to `Ideal.ResidueField.mapₐ (RingHom.ker φ) P.asIdeal (Algebra.ofId B A) hPp`. Set `F : (RingHom.ker φ).ResidueField ⊗[B] A →ₐ[B] P.asIdeal.ResidueField` to `Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B A _) (fun _ _ => Commute.all _ _)`.

Establish `: Nontrivial ((RingHom.ker φ).ResidueField ⊗[B] A)` using `F.toRingHom.domain_nontrivial`. Take `⟨χ, hχ⟩` from `exists_ringHom_extend_of_finiteType (RingHom.ker φ).ResidueField ((RingHom.ker φ).ResidueField ⊗[B] A) L σ`. Use `⟨χ.comp (Algebra.TensorProduct.includeRight (R := B) (A := (RingHom.ker φ).ResidueField) (B := A)).toRingHom, RingHom.ext fun b => ?_⟩` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Rewrite using `[IsScalarTower.algebraMap_apply B (RingHom.ker φ).ResidueField ((RingHom.ker φ).ResidueField ⊗[B] A), hχ]`.

Conclude with `Ideal.ResidueField.lift_algebraMap _ _ _ _ _`.
-/
theorem exists_ringHom_extend_of_ker_mem_range_comap {B A L : Type*} [CommRing B] [CommRing A]
    [Algebra B A] [Algebra.FiniteType B A] [Field L] [IsAlgClosed L] (φ : B →+* L)
    (h : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    ∃ ψ : A →+* L, ψ.comp (algebraMap B A) = φ := by
  obtain ⟨P, hP⟩ := h
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hPp : RingHom.ker φ = P.asIdeal.comap (algebraMap B A) := by
    have := congrArg PrimeSpectrum.asIdeal hP
    simpa using this.symm

  let σ : (RingHom.ker φ).ResidueField →+* L :=
    Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl (fun x hx => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff]
      exact isUnit_iff_ne_zero.mpr fun h0 => hx (RingHom.mem_ker.mpr h0))

  let g : (RingHom.ker φ).ResidueField →ₐ[B] P.asIdeal.ResidueField :=
    Ideal.ResidueField.mapₐ (RingHom.ker φ) P.asIdeal (Algebra.ofId B A) hPp
  let F : (RingHom.ker φ).ResidueField ⊗[B] A →ₐ[B] P.asIdeal.ResidueField :=
    Algebra.TensorProduct.lift g (IsScalarTower.toAlgHom B A _) (fun _ _ => Commute.all _ _)
  have : Nontrivial ((RingHom.ker φ).ResidueField ⊗[B] A) := F.toRingHom.domain_nontrivial
  obtain ⟨χ, hχ⟩ := exists_ringHom_extend_of_finiteType (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A) L σ
  refine ⟨χ.comp (Algebra.TensorProduct.includeRight (R := B)
    (A := (RingHom.ker φ).ResidueField) (B := A)).toRingHom, RingHom.ext fun b => ?_⟩
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [IsScalarTower.algebraMap_apply B (RingHom.ker φ).ResidueField
    ((RingHom.ker φ).ResidueField ⊗[B] A), hχ]
  exact Ideal.ResidueField.lift_algebraMap _ _ _ _ _

/- English proof (translation)
Introduce `B A _ _ _ _ _ _ _ hinj`. Establish `hfp : (algebraMap B A).FinitePresentation` using `RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)`. Establish `hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ Set.range (PrimeSpectrum.comap (algebraMap B A))`. Use `⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Conclude with `Ideal.comap_bot_of_injective _ hinj`.

Take `⟨q, hq, hsub⟩` from `exists_basicOpen_subset_of_isConstructible_of_bot_mem (PrimeSpectrum.isConstructible_range_comap hfp) hgen`. Conclude with `⟨q, hq, fun φ hφ => exists_ringHom_extend_of_ker_mem_range_comap φ (hsub _ fun hk => hφ (RingHom.mem_ker.mp hk))⟩`.
-/
theorem exists_ne_zero_forall_complexPoint_extend :
    ∀ (B A : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [IsDomain A]
    [Algebra B A] [Algebra.FiniteType B A], Function.Injective (algebraMap B A) →
    ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ ψ : A →+* ℂ, ψ.comp (algebraMap B A) = φ := by
  intro B A _ _ _ _ _ _ _ hinj
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr (Algebra.FinitePresentation.of_finiteType.mp ‹_›)

  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈
      Set.range (PrimeSpectrum.comap (algebraMap B A)) := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
    exact Ideal.comap_bot_of_injective _ hinj
  obtain ⟨q, hq, hsub⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem
    (PrimeSpectrum.isConstructible_range_comap hfp) hgen
  exact ⟨q, hq, fun φ hφ =>
    exists_ringHom_extend_of_ker_mem_range_comap φ (hsub _ fun hk => hφ (RingHom.mem_ker.mp hk))⟩

end GlobalTheory
