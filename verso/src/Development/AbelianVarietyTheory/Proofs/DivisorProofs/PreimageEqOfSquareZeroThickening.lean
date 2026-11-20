import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCombIn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.SecGlue

/- English proof (translation)
Introduce `S T _ _ q hq hsq Y u w huw V`. Establish `hsurj : Function.Surjective (spMap q).base`. Introduce `p`. Establish `hker : RingHom.ker q ≤ p.asIdeal`. Introduce `x hx`.

Establish `hx2 : x * x ∈ RingHom.ker q ^ 2`. Rewrite using `[sq]`. Conclude with `Ideal.mul_mem_mul hx hx`. Rewrite `hx2` using `[hsq, Ideal.mem_bot]`. Conclude with `(p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id`.

Use `haveI := p.isPrime`. Use `haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker`. Use `⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Spec.map_base]`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal`. Rewrite using `[Ideal.comap_map_of_surjective _ hq, sup_eq_left]`. Introduce `x hx`. Conclude with `hker (by simpa [RingHom.mem_ker] using hx)`. Use extensionality with `x`.

Take `⟨y, rfl⟩` from `hsurj x`. Rewrite using `[SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]`.
-/
theorem preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by
  intro S T _ _ q hq hsq Y u w huw V
  have hsurj : Function.Surjective (spMap q).base := by
    intro p
    have hker : RingHom.ker q ≤ p.asIdeal := by
      intro x hx
      have hx2 : x * x ∈ RingHom.ker q ^ 2 := by
        rw [sq]; exact Ideal.mul_mem_mul hx hx
      rw [hsq, Ideal.mem_bot] at hx2
      exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
    haveI := p.isPrime
    haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
    refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
    intro x hx
    exact hker (by simpa [RingHom.mem_ker] using hx)
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  rw [SetLike.mem_coe, SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_preimage,
    ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, huw]

end GlobalTheory.SecGlue
