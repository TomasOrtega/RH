import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors.StatementsInj
import GroundTheory.HeightsAndTheta.Heights.ReducedTensors.Imports
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField TensorProduct ComplexAt

noncomputable section

namespace SectionsLattice

/- English proof (translation)
Establish `: IsJacobsonRing C` using `isJacobsonRing_of_finiteType (A := ℂ)`. Establish `hj : (⊥ : Ideal C).jacobson = ⊥`. Rewrite using `[← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced]`. It suffices to establish `g ∈ (⊥ : Ideal C).jacobson by rwa [hj, Ideal.mem_bot] at this`. Use `Ideal.mem_sInf.mpr fun m ⟨_, hm⟩ ↦ ?_` and prove the remaining obligations.

Set `` to `Ideal.Quotient.field m`. Establish `: Algebra.FiniteType ℂ (C ⧸ m)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)`. Establish `: Module.Finite ℂ (C ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing ℂ (C ⧸ m)`. Set `e : C ⧸ m →ₐ[ℂ] ℂ` to `IsAlgClosed.lift`. Establish `h0 : e (Ideal.Quotient.mk m g) = 0` using `hg (e.comp (Ideal.Quotient.mkₐ ℂ m))`.

Rewrite `h0` using `[map_eq_zero_iff e e.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h0`.
-/
theorem eq_zero_of_forall_algHom_complex {C : Type} [CommRing C] [Algebra ℂ C]
    [Algebra.FiniteType ℂ C] [IsReduced C] (g : C) (hg : ∀ ψ : C →ₐ[ℂ] ℂ, ψ g = 0) : g = 0 := by
  have : IsJacobsonRing C := isJacobsonRing_of_finiteType (A := ℂ)
  have hj : (⊥ : Ideal C).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_isReduced]
  suffices g ∈ (⊥ : Ideal C).jacobson by rwa [hj, Ideal.mem_bot] at this
  refine Ideal.mem_sInf.mpr fun m ⟨_, hm⟩ ↦ ?_
  let := Ideal.Quotient.field m
  have : Algebra.FiniteType ℂ (C ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ m) (Ideal.Quotient.mkₐ_surjective ℂ m)
  have : Module.Finite ℂ (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (C ⧸ m)
  let e : C ⧸ m →ₐ[ℂ] ℂ := IsAlgClosed.lift
  have h0 : e (Ideal.Quotient.mk m g) = 0 := hg (e.comp (Ideal.Quotient.mkₐ ℂ m))
  rw [map_eq_zero_iff e e.toRingHom.injective, Ideal.Quotient.eq_zero_iff_mem] at h0
  exact h0

/- English proof (translation)
Introduce `K _ _ σ B _ _ hfin hred ι _ z hz f hf`. Use `set w : ι → ℂ := fun i ↦ (ofComplex σ).symm (z i) with hw`. Set `: Algebra K ℂ` to `σ.toAlgebra`. Establish `hind : ∀ c : ι → K, ∑ i, c i • w i = 0 → ∀ i, c i = 0`. Introduce `c hc`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image c)`. Use `choose a ha using fun i ↦ hb (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Establish `hbK : ((b : 𝓞 K) : K) ≠ 0` using `RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero b.2)`. Establish `hsum : ∑ i, a i • z i = 0`. Establish `: ∑ i, a i • z i = ofComplex σ (σ ((b : 𝓞 K) : K) * ∑ i, c i • w i)`.

Rewrite using `[Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[ComplexAt.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, ← mul_assoc, ← map_mul, show ((a i : 𝓞 K) : K) = (b : 𝓞 K) * c i from (ha i).trans (Algebra.smul_def _ _)]`. Both sides reduce to the same expression. Rewrite using `[this, hc, mul_zero, map_zero]`.

Introduce `i`. Use `Fintype.linearIndependent_iff.mp hz a hsum i` as an intermediate fact. Establish `h2` using `(ha i).symm`. Rewrite `h2` using `[this, map_zero, Algebra.smul_def]`. Conclude with `(mul_eq_zero.mp h2).resolve_left hbK`.

Use `hfin` as an intermediate fact. Set `R` to `K ⊗[𝓞 K] B`. Set `: Algebra B R` to `Algebra.TensorProduct.rightAlgebra`. Establish `hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R` using `IsLocalization.tensorRight _ _`. Establish `hredR : IsReduced R` using `isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R hred`.

Establish `: IsReduced (ℂ ⊗[K] R)` using `h K ℂ R hredR`. Set `r : ι → R` to `fun i ↦ (1 : K) ⊗ₜ f i`. Establish `hg : ∑ i, w i ⊗ₜ[K] r i = 0`. Apply `eq_zero_of_forall_algHom_complex` to reduce the goal to its premises. Introduce `ψ`.

Set `φ : B →+* ℂ` to `ψ.toRingHom.comp ((Algebra.TensorProduct.includeRight : R →ₐ[K] ℂ ⊗[K] R).toRingHom.comp (Algebra.TensorProduct.includeRight : B →ₐ[𝓞 K] R).toRingHom)`. Establish `hφ : φ.comp (algebraMap (𝓞 K) B) = ProjScheme.intEmb σ`. Use extensionality with `a`. Establish `e1 : ((algebraMap (𝓞 K) K a) ⊗ₜ[𝓞 K] (1 : B) : R) = algebraMap (𝓞 K) K a • (1 : R)`. Rewrite using `[Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]`.

Establish `e2` using `ψ.commutes (algebraMap K ℂ (algebraMap (𝓞 K) K a))`. Rewrite `e2` using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`. Simplify using `only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]`. Establish `e0 : (1 : K) ⊗ₜ[𝓞 K] algebraMap (𝓞 K) B a = algebraMap (𝓞 K) K a ⊗ₜ[𝓞 K] (1 : B)`. Rewrite using `[Algebra.algebraMap_eq_smul_one (A := B) a, ← smul_tmul, Algebra.algebraMap_eq_smul_one (A := K) a]`.

Rewrite using `[e0, e1, ← smul_tmul, Algebra.smul_def, mul_one]`. Conclude with `e2`. Use `hf φ hφ` as an intermediate fact. Rewrite using `[map_sum]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) this` and prove the remaining obligations.

Rewrite using `[show w i ⊗ₜ[K] r i = w i • ((1 : ℂ) ⊗ₜ[K] r i) by rw [smul_tmul', smul_eq_mul, mul_one], map_smul, smul_eq_mul]`. Both sides reduce to the same expression. Take `⟨k, c, y, h1, h2⟩` from `vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective K (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) hg`. Introduce `i`. Establish `hri : algebraMap B R (f i) = 0`.

Express the relevant statement in the definitionally equal form `r i = 0`. Rewrite using `[h1 i]`. Conclude with `Finset.sum_eq_zero fun j _ ↦ by rw [hind (fun i ↦ c i j) (h2 j) i, zero_smul]`. Take `⟨⟨_, d, hd, rfl⟩, hm⟩` from `(IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R _).mp hri`. Conclude with `⟨d, nonZeroDivisors.ne_zero hd, by rw [Algebra.smul_def]; exact hm⟩`.
-/
theorem AffineNull.proof (h : BaseChangeReduced.Statement) : AffineNull.Statement := by
  classical
  intro K _ _ σ B _ _ hfin hred ι _ z hz f hf
  set w : ι → ℂ := fun i ↦ (ofComplex σ).symm (z i) with hw
  let : Algebra K ℂ := σ.toAlgebra

  have hind : ∀ c : ι → K, ∑ i, c i • w i = 0 → ∀ i, c i = 0 := by
    intro c hc
    obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
      (Finset.univ.image c)
    choose a ha using fun i ↦ hb (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hbK : ((b : 𝓞 K) : K) ≠ 0 :=
      RingOfIntegers.coe_ne_zero_iff.mpr (nonZeroDivisors.ne_zero b.2)
    have hsum : ∑ i, a i • z i = 0 := by
      have : ∑ i, a i • z i = ofComplex σ (σ ((b : 𝓞 K) : K) * ∑ i, c i • w i) := by
        rw [Finset.mul_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [ComplexAt.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra, ← mul_assoc,
          ← map_mul, show ((a i : 𝓞 K) : K) = (b : 𝓞 K) * c i from (ha i).trans (Algebra.smul_def _ _)]
        rfl
      rw [this, hc, mul_zero, map_zero]
    intro i
    have := Fintype.linearIndependent_iff.mp hz a hsum i
    have h2 := (ha i).symm
    rw [this, map_zero, Algebra.smul_def] at h2
    exact (mul_eq_zero.mp h2).resolve_left hbK

  have := hfin
  let R := K ⊗[𝓞 K] B
  let : Algebra B R := Algebra.TensorProduct.rightAlgebra
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R :=
    IsLocalization.tensorRight _ _
  have hredR : IsReduced R :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R hred
  have : IsReduced (ℂ ⊗[K] R) := h K ℂ R hredR

  let r : ι → R := fun i ↦ (1 : K) ⊗ₜ f i
  have hg : ∑ i, w i ⊗ₜ[K] r i = 0 := by
    apply eq_zero_of_forall_algHom_complex
    intro ψ
    let φ : B →+* ℂ := ψ.toRingHom.comp ((Algebra.TensorProduct.includeRight :
      R →ₐ[K] ℂ ⊗[K] R).toRingHom.comp (Algebra.TensorProduct.includeRight :
        B →ₐ[𝓞 K] R).toRingHom)
    have hφ : φ.comp (algebraMap (𝓞 K) B) = ProjScheme.intEmb σ := by
      ext a
      have e1 : ((algebraMap (𝓞 K) K a) ⊗ₜ[𝓞 K] (1 : B) : R) = algebraMap (𝓞 K) K a • (1 : R) := by
        rw [Algebra.TensorProduct.one_def, smul_tmul', smul_eq_mul, mul_one]
      have e2 := ψ.commutes (algebraMap K ℂ (algebraMap (𝓞 K) K a))
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at e2
      simp only [φ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply]
      have e0 : (1 : K) ⊗ₜ[𝓞 K] algebraMap (𝓞 K) B a = algebraMap (𝓞 K) K a ⊗ₜ[𝓞 K] (1 : B) := by
        rw [Algebra.algebraMap_eq_smul_one (A := B) a, ← smul_tmul,
          Algebra.algebraMap_eq_smul_one (A := K) a]
      rw [e0, e1, ← smul_tmul, Algebra.smul_def, mul_one]
      exact e2
    have := hf φ hφ
    rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) this
    rw [show w i ⊗ₜ[K] r i = w i • ((1 : ℂ) ⊗ₜ[K] r i) by rw [smul_tmul', smul_eq_mul, mul_one],
      map_smul, smul_eq_mul]
    rfl
  obtain ⟨k, c, y, h1, h2⟩ := vanishesTrivially_of_sum_tmul_eq_zero_of_rTensor_injective K
    (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective) hg
  intro i
  have hri : algebraMap B R (f i) = 0 := by
    change r i = 0
    rw [h1 i]
    exact Finset.sum_eq_zero fun j _ ↦ by rw [hind (fun i ↦ c i j) (h2 j) i, zero_smul]
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid B (nonZeroDivisors (𝓞 K))) R _).mp hri
  exact ⟨d, nonZeroDivisors.ne_zero hd, by rw [Algebra.smul_def]; exact hm⟩

end SectionsLattice

end

end GroundTheory.Heights₂.Heights
