import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `S T K _ _ _ _ _ _ Q hQ hfrac hreg`. Use `haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)`. Set `φ : Q.ResidueField →ₐ[S] K` to `Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by`. Introduce `x hx`. Simplify using `only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]`.

Introduce `h0`. Conclude with `hx (hQ ▸ h0))`. Establish `hsurj : Function.Surjective φ`. Introduce `y`. Take `⟨a, b, hb, hy⟩` from `hfrac y`.

Establish `hb0 : algebraMap S K b ≠ 0` using `fun h0 => hb (hQ ▸ h0)`. Use `⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]`. Rewrite using `[← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]`. Set `e : Q.ResidueField ≃ₐ[S] K` to `AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩`.

Set `E : Q.Fiber T ≃ₐ[S] T ⊗[S] K` to `(Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)`. Use `haveI : IsNoetherianRing (Q.Fiber T) := by`. Use `letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra`. Set `Sp` to `Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)`. Use `haveI : IsNoetherianRing Sp := IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance`.

Conclude with `isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm`. Use `haveI : IsRegularRing (Q.Fiber T) := by`. Rewrite using `[isRegularRing_iff]`. Introduce `q hq`. Set `n : Ideal T` to `q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)`.

Use `haveI : n.IsPrime := Ideal.comap_isPrime _ _`. Establish `hn : n.comap (algebraMap S T) = Q`. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap S T) (Ideal.comap ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q`. Rewrite using `[Ideal.comap_comap, AlgHom.comp_algebraMap]`. Conclude with `(Ideal.over_def q Q).symm`.

Use `haveI := hreg n hn`. Conclude with `IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm`. Conclude with `IsRegularRing.of_ringEquiv E.toRingEquiv`.
-/
theorem isRegularRing_tensor_of_fibre_localRings :
    ∀ (S T K : Type) [CommRing S] [CommRing T] [Algebra S T] [IsNoetherianRing T] [Field K]
      [Algebra S K] (Q : Ideal S), RingHom.ker (algebraMap S K) = Q →
      (∀ y : K, ∃ a b : S, b ∉ Q ∧ y * algebraMap S K b = algebraMap S K a) →
      (∀ (n : Ideal T) [n.IsPrime], n.comap (algebraMap S T) = Q →
        IsRegularLocalRing (Localization.AtPrime n ⧸
          (Q.map (algebraMap S T)).map (algebraMap T (Localization.AtPrime n)))) →
      IsRegularRing (T ⊗[S] K) := by
  intro S T K _ _ _ _ _ _ Q hQ hfrac hreg
  haveI : Q.IsPrime := hQ ▸ RingHom.ker_isPrime (algebraMap S K)
  let φ : Q.ResidueField →ₐ[S] K := Ideal.ResidueField.liftₐ Q (Algebra.ofId S K) hQ.ge (by
    intro x hx
    simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
    intro h0
    exact hx (hQ ▸ h0))
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, b, hb, hy⟩ := hfrac y
    have hb0 : algebraMap S K b ≠ 0 := fun h0 => hb (hQ ▸ h0)
    refine ⟨algebraMap S Q.ResidueField a * (algebraMap S Q.ResidueField b)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, AlgHom.commutes, AlgHom.commutes]
    rw [← hy, mul_assoc, mul_inv_cancel₀ hb0, mul_one]
  let e : Q.ResidueField ≃ₐ[S] K := AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, hsurj⟩
  let E : Q.Fiber T ≃ₐ[S] T ⊗[S] K :=
    (Algebra.TensorProduct.congr e AlgEquiv.refl).trans (Algebra.TensorProduct.comm S K T)
  haveI : IsNoetherianRing (Q.Fiber T) := by
    letI : Algebra T (Q.Fiber T) := Algebra.TensorProduct.rightAlgebra
    let Sp := Localization (Algebra.algebraMapSubmonoid T Q.primeCompl)
    haveI : IsNoetherianRing Sp :=
      IsLocalization.isNoetherianRing (Algebra.algebraMapSubmonoid T Q.primeCompl) Sp inferInstance
    exact isNoetherianRing_of_ringEquiv _ (Ideal.Fiber.algEquivAux₁ Q (S := T)).toRingEquiv.symm
  haveI : IsRegularRing (Q.Fiber T) := by
    rw [isRegularRing_iff]
    intro q hq
    let n : Ideal T := q.comap (Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T)
    haveI : n.IsPrime := Ideal.comap_isPrime _ _
    have hn : n.comap (algebraMap S T) = Q := by
      change Ideal.comap (algebraMap S T) (Ideal.comap
        ((Algebra.TensorProduct.includeRight : T →ₐ[S] Q.Fiber T) : T →+* Q.Fiber T) q) = Q
      rw [Ideal.comap_comap, AlgHom.comp_algebraMap]
      exact (Ideal.over_def q Q).symm
    haveI := hreg n hn
    exact IsRegularLocalRing.of_ringEquiv (Ideal.Fiber.algEquivAux₂ Q q).toRingEquiv.symm
  exact IsRegularRing.of_ringEquiv E.toRingEquiv

end GlobalTheory
