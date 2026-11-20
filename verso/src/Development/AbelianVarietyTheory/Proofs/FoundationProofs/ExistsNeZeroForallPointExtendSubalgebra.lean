import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointExtend

open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k A R _ _ _ _ _ _ _ _ _ ξ hinj T`. Take `⟨s, hs⟩` from `(Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)`. Use `set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef`. Establish `hξ : ∀ u, ξ u ∈ S`. Introduce `u`.

Establish `hu : u ∈ Algebra.adjoin k (s : Set A)` using `hs ▸ Algebra.mem_top`. Establish `: ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ` using `⟨u, hu, rfl⟩`. Rewrite `this` using `[AlgHom.map_adjoin]`. Conclude with `Algebra.adjoin_mono Set.subset_union_left this`. Establish `hT : ∀ t ∈ T, t ∈ S` using `fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)`.

Establish `hSfg : S.FG` using `Subalgebra.fg_def.2 ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩`. Use `haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg`. Set `f : A →ₐ[k] S` to `ξ.codRestrict S hξ`. Use `letI : Algebra A S := f.toRingHom.toAlgebra`. Use `haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm`.

Use `haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S`. Use `haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A`. Establish `hfinj : Function.Injective (algebraMap A S)`. Introduce `x y h`. Apply `hinj` to reduce the goal to its premises.

Use `congrArg Subtype.val h` as an intermediate fact. Conclude with `this`. Establish `hfp : Algebra.FinitePresentation A S` using `Algebra.FinitePresentation.of_finiteType.1 ‹_›`. Establish `hc` using `PrimeSpectrum.isConstructible_range_comap (RingHom.finitePresentation_algebraMap.mpr hfp)`. Take `⟨q, hq, H⟩` from `exists_basicOpen_subset_of_isConstructible_of_bot_mem hc ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩`.

Use `⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨ψ, hψ⟩` from `exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))`. Establish `hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u` using `fun u => by`. Use `RingHom.congr_fun hψ u` as an intermediate fact. Conclude with `this`.

Use `⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩` and prove the remaining obligations. Establish `h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩` using `by ext; simp`. Simplify using `only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]`. Rewrite using `[h1, hψu, φ.commutes]`.
-/
theorem exists_ne_zero_forall_point_extend_subalgebra :
    ∀ (k A R : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing R] [IsDomain R] [Algebra k R] (ξ : A →ₐ[k] R),
    Function.Injective ξ → ∀ T : Finset R,
    ∃ (a : A) (S : Subalgebra k R) (hξ : ∀ u, ξ u ∈ S), a ≠ 0 ∧ (∀ t ∈ T, t ∈ S) ∧
      ∀ φ : A →ₐ[k] k, φ a ≠ 0 → ∃ ψ : S →ₐ[k] k, ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := by
  intro k A R _ _ _ _ _ _ _ _ _ ξ hinj T
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra k A).FG)
  set S : Subalgebra k R := Algebra.adjoin k (ξ '' (s : Set A) ∪ (T : Set R)) with hSdef
  have hξ : ∀ u, ξ u ∈ S := by
    intro u
    have hu : u ∈ Algebra.adjoin k (s : Set A) := hs ▸ Algebra.mem_top
    have : ξ u ∈ (Algebra.adjoin k (s : Set A)).map ξ := ⟨u, hu, rfl⟩
    rw [AlgHom.map_adjoin] at this
    exact Algebra.adjoin_mono Set.subset_union_left this
  have hT : ∀ t ∈ T, t ∈ S := fun t ht => Algebra.subset_adjoin (Set.subset_union_right ht)
  have hSfg : S.FG := Subalgebra.fg_def.2
    ⟨_, (s.finite_toSet.image ξ).union T.finite_toSet, rfl⟩
  haveI : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).1 hSfg
  let f : A →ₐ[k] S := ξ.codRestrict S hξ
  letI : Algebra A S := f.toRingHom.toAlgebra
  haveI : IsScalarTower k A S := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  haveI : Algebra.FiniteType A S := Algebra.FiniteType.of_restrictScalars_finiteType k A S
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have hfinj : Function.Injective (algebraMap A S) := by
    intro x y h
    apply hinj
    have := congrArg Subtype.val h
    exact this
  have hfp : Algebra.FinitePresentation A S := Algebra.FinitePresentation.of_finiteType.1 ‹_›
  have hc := PrimeSpectrum.isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr hfp)
  obtain ⟨q, hq, H⟩ := exists_basicOpen_subset_of_isConstructible_of_bot_mem hc
    ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext (Ideal.comap_bot_of_injective _ hfinj)⟩
  refine ⟨q, S, hξ, hq, hT, fun φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := exists_ringHom_extend_of_ker_mem_range_comap (A := S) φ.toRingHom
    (H ⟨RingHom.ker φ.toRingHom, RingHom.ker_isPrime _⟩ (by simpa [RingHom.mem_ker] using hφ))
  have hψu : ∀ u, ψ ⟨ξ u, hξ u⟩ = φ u := fun u => by
    have := RingHom.congr_fun hψ u
    exact this
  refine ⟨{ ψ with commutes' := fun c => ?_ }, hψu⟩
  have h1 : (algebraMap k S c) = ⟨ξ (algebraMap k A c), hξ _⟩ := by
    ext; simp
  simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  rw [h1, hψu, φ.commutes]

end GlobalTheory
