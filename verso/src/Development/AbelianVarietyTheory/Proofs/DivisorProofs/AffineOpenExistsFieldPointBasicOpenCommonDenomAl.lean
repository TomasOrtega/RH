import Mathlib
open AlgebraicGeometry

namespace GlobalTheory

/- English proof (translation)
Introduce `X U hU p hp`. Set `P` to `hU.primeIdealOf ⟨p, hp⟩`. Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Set `K` to `FractionRing (Γ(X, U) ⧸ P.asIdeal)`. Set `ψ : Γ(X, U) →+* K` to `(algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)`.

Establish `hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal`. Introduce `g`. Simplify using `only [ψ, RingHom.comp_apply, ne_eq]`. Rewrite using `[map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]`. Use `⟨K, inferInstance, ψ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g hg`. Establish `h1 : P ∈ PrimeSpectrum.basicOpen g` using `(hψ g).1 hg`. Rewrite `h1` using `[← hU.fromSpec_preimage_basicOpen]`. Establish `h2 : hU.fromSpec P = p` using `hU.fromSpec_primeIdealOf ⟨p, hp⟩`. Establish `h3 : hU.fromSpec P ∈ X.basicOpen g` using `h1`.

Rewrite `h3` using `[h2]`. Then use the resulting hypothesis. Introduce `ι _ m`. Establish `hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b`. Introduce `i`. Take `⟨⟨b', ⟨s', hs'⟩⟩, he⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)`.

Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b'`. Take `⟨s, rfl⟩` from `Ideal.Quotient.mk_surjective s'`. Use `⟨b, s, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [ψ, RingHom.comp_apply, ne_eq]`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'`.

Rewrite using `[← he]`. Simplify using `only [ψ, RingHom.comp_apply]`. Conclude with `IsLocalization.mk'_spec _ _ _`. Use `choose b s hs hbs using hrep`. Use `⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun j _ => hs j)`. Introduce `i`. Rewrite using `[map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i), ← mul_assoc, hbs i, map_mul, map_prod]`.
-/
theorem affineOpen_exists_field_point_basicOpen_commonDenom :
    ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U →
      ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧
        ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)),
          ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  intro X U hU p hp
  classical
  let P := hU.primeIdealOf ⟨p, hp⟩
  haveI : P.asIdeal.IsPrime := P.isPrime
  let K := FractionRing (Γ(X, U) ⧸ P.asIdeal)
  let ψ : Γ(X, U) →+* K := (algebraMap (Γ(X, U) ⧸ P.asIdeal) K).comp (Ideal.Quotient.mk P.asIdeal)
  have hψ : ∀ g, ψ g ≠ 0 ↔ g ∉ P.asIdeal := by
    intro g
    simp only [ψ, RingHom.comp_apply, ne_eq]
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  refine ⟨K, inferInstance, ψ, ?_, ?_⟩
  · intro g hg
    have h1 : P ∈ PrimeSpectrum.basicOpen g := (hψ g).1 hg
    rw [← hU.fromSpec_preimage_basicOpen] at h1
    have h2 : hU.fromSpec P = p := hU.fromSpec_primeIdealOf ⟨p, hp⟩
    have h3 : hU.fromSpec P ∈ X.basicOpen g := h1
    rwa [h2] at h3
  · intro ι _ m
    have hrep : ∀ i, ∃ b s : Γ(X, U), ψ s ≠ 0 ∧ m i * ψ s = ψ b := by
      intro i
      obtain ⟨⟨b', ⟨s', hs'⟩⟩, he⟩ := IsLocalization.mk'_surjective
        (nonZeroDivisors (Γ(X, U) ⧸ P.asIdeal)) (m i)
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s'
      refine ⟨b, s, ?_, ?_⟩
      · simp only [ψ, RingHom.comp_apply, ne_eq]
        exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs'
      · rw [← he]
        simp only [ψ, RingHom.comp_apply]
        exact IsLocalization.mk'_spec _ _ _
    choose b s hs hbs using hrep
    refine ⟨fun i => b i * ∏ j ∈ Finset.univ.erase i, s j, ∏ j, s j, ?_, ?_⟩
    · rw [map_prod]
      exact Finset.prod_ne_zero_iff.2 (fun j _ => hs j)
    · intro i
      rw [map_prod, ← Finset.mul_prod_erase Finset.univ (fun j => ψ (s j)) (Finset.mem_univ i),
        ← mul_assoc, hbs i, map_mul, map_prod]

end GlobalTheory
