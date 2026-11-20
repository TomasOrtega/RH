import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.ExistsNotMem
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalField
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalExt

/- English proof (translation)
Introduce `F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hd c hc`. Establish `hfrob : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁`. Use extensionality with `z`. Rewrite using `[FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hsb]`. Establish `hgen : ∀ t : F₁ ≃ₐ[F₀] F₁, t ∈ Subgroup.zpowers sb`.

Introduce `t`. Take `⟨i, hi⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F₀ F₁).2 t`. Rewrite using `[← hi, ← hfrob]`. Conclude with `Subgroup.npow_mem_zpowers _ _`. Establish `hG : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁)` using `UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb hgen`.

Set `S : Subring A` to `(τ : A →+* A).eqLocus (RingHom.id A)`. Set `f : F₀ →+* S` to `((algebraMap F₁ A).comp (algebraMap F₀ F₁)).codRestrict S (fun z => by`. Express the relevant statement in the definitionally equal form `τ (algebraMap F₁ A (algebraMap F₀ F₁ z)) = algebraMap F₁ A (algebraMap F₀ F₁ z)`. Rewrite using `[hτ, AlgEquiv.commutes])`. Use `letI : Algebra F₀ S := f.toAlgebra`.

Use `haveI : Module.Finite F₀ S := Module.Finite.of_finite`. Set `σ : A ≃ₐ[S] A` to `AlgEquiv.ofRingEquiv (f := τ) (fun r => r.2)`. Establish `hpow : ∀ (j : ℕ) (x : A), (σ ^ j) x = τ^[j] x`. Introduce `j x`. Proceed by induction on `j with`.

Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, ih, Function.iterate_succ_apply']`. Both sides reduce to the same expression. Establish `hpowF : ∀ (j : ℕ) (z : F₁), τ^[j] (algebraMap F₁ A z) = algebraMap F₁ A ((sb ^ j) z)`.

Introduce `j z`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply', ih, hτ, pow_succ', AlgEquiv.mul_apply]`.

Establish `hGal : UpperTheory.ConvolutionTheory.D.IsGal σ (Module.finrank F₀ F₁)`. Use `⟨hG.pos, AlgEquiv.ext fun x => ?_, Subtype.val_injective, fun r hr => ⟨⟨r, hr⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hpow, hd]`. Both sides reduce to the same expression. Take `⟨s, x, y, h⟩` from `hG.sep`.

Use `⟨s, fun i => algebraMap F₁ A (x i), fun i => algebraMap F₁ A (y i), fun j hj => ?_⟩` and prove the remaining obligations. Simplify using `only [hpow, hpowF, ← map_mul, ← map_sum]`. Rewrite using `[h j hj]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hu : IsUnit c`.

Establish `h1 : c ∣ UpperTheory.Gal.InertialTypesAlt.L.itN τ (Module.finrank F₀ F₁) c` using `Finset.dvd_prod_of_mem (fun i => τ^[i] c) (Finset.mem_range.2 hG.pos)`. Rewrite `h1` using `[hc]`. Conclude with `isUnit_of_dvd_one h1`. Take `⟨z, hz⟩` from `UpperTheory.ConvolutionTheory.D.h90 F₀ F₀ S A σ _ hGal hu.unit (by`. Simplify using `only [hpow, IsUnit.unit_spec]`.

Conclude with `hc)`. Conclude with `⟨z, hz⟩`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.L.hilbert_ninety_frobenius_twisted_finite_algebra :
    UpperTheory.Gal.InertialTypesAlt.L.FrobeniusTwistedHilbertNinety := by
  intro F₀ F₁ _ _ _ _ _ sb hsb A _ _ _ τ hτ hd c hc
  classical
  have hfrob : sb = FiniteField.frobeniusAlgEquivOfAlgebraic F₀ F₁ := by
    ext z
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic, hsb]
  have hgen : ∀ t : F₁ ≃ₐ[F₀] F₁, t ∈ Subgroup.zpowers sb := by
    intro t
    obtain ⟨i, hi⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F₀ F₁).2 t
    rw [← hi, ← hfrob]
    exact Subgroup.npow_mem_zpowers _ _
  have hG : UpperTheory.ConvolutionTheory.D.IsGal sb (Module.finrank F₀ F₁) := UpperTheory.ConvolutionTheory.D.galField F₀ F₁ sb hgen
  let S : Subring A := (τ : A →+* A).eqLocus (RingHom.id A)
  let f : F₀ →+* S := ((algebraMap F₁ A).comp (algebraMap F₀ F₁)).codRestrict S (fun z => by
    change τ (algebraMap F₁ A (algebraMap F₀ F₁ z)) = algebraMap F₁ A (algebraMap F₀ F₁ z)
    rw [hτ, AlgEquiv.commutes])
  letI : Algebra F₀ S := f.toAlgebra
  haveI : Module.Finite F₀ S := Module.Finite.of_finite
  let σ : A ≃ₐ[S] A := AlgEquiv.ofRingEquiv (f := τ) (fun r => r.2)
  have hpow : ∀ (j : ℕ) (x : A), (σ ^ j) x = τ^[j] x := by
    intro j x
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', AlgEquiv.mul_apply, ih, Function.iterate_succ_apply']
      rfl
  have hpowF : ∀ (j : ℕ) (z : F₁), τ^[j] (algebraMap F₁ A z) = algebraMap F₁ A ((sb ^ j) z) := by
    intro j z
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, hτ, pow_succ', AlgEquiv.mul_apply]
  have hGal : UpperTheory.ConvolutionTheory.D.IsGal σ (Module.finrank F₀ F₁) := by
    refine ⟨hG.pos, AlgEquiv.ext fun x => ?_, Subtype.val_injective, fun r hr => ⟨⟨r, hr⟩, rfl⟩, ?_⟩
    · rw [hpow, hd]; rfl
    · obtain ⟨s, x, y, h⟩ := hG.sep
      refine ⟨s, fun i => algebraMap F₁ A (x i), fun i => algebraMap F₁ A (y i), fun j hj => ?_⟩
      simp only [hpow, hpowF, ← map_mul, ← map_sum]
      rw [h j hj]
      split_ifs <;> simp
  have hu : IsUnit c := by
    have h1 : c ∣ UpperTheory.Gal.InertialTypesAlt.L.itN τ (Module.finrank F₀ F₁) c :=
      Finset.dvd_prod_of_mem (fun i => τ^[i] c) (Finset.mem_range.2 hG.pos)
    rw [hc] at h1
    exact isUnit_of_dvd_one h1
  obtain ⟨z, hz⟩ := UpperTheory.ConvolutionTheory.D.h90 F₀ F₀ S A σ _ hGal hu.unit (by
    simp only [hpow, IsUnit.unit_spec]
    exact hc)
  exact ⟨z, hz⟩
