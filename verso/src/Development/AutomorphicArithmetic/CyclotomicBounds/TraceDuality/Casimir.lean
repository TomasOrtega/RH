import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.TraceForm
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.DualFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.TraceDuality.EmbSum
open NumberField
open scoped TensorProduct NNReal
open Classical

/- English proof (translation)
Introduce `E _ _ d m hd hd0 hm`. Take `⟨lam, hlam⟩` from `UpperTheory.WildB.traceForm E d m hd0 hm`. Take `⟨n, a, b, h1, h2, h3⟩` from `UpperTheory.WildB.dualFamily E d hd hd0`. Establish `hs : ∀ (z : Fin n → ℤ) (c : Fin n → 𝓞 E), algebraMap (𝓞 E) E (∑ j, z j • c j) = ∑ j, (z j : ℚ) • (c j : E)`. Introduce `z c`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Use `⟨n, a, b, lam, fun x => ?_, fun x => ?_, fun C _ _ _ φ ψ => UpperTheory.WildB.embSum E d hd0 n a b h1 C φ ψ⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Rewrite using `[hs, map_mul, map_natCast, ← h1 ((m : E) * algebraMap (𝓞 E) E x)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hlam]`. Use `congr 2`. Express the relevant statement in the definitionally equal form `(m : E) * ((b j : E) * (x : E)) / (d : E) = (m : E) * (x : E) * (b j : E) / (d : E)`.

Expand and normalize the polynomial expressions, which then agree. Use `choose M hM using h3 x`. Use `⟨M, fun j => ?_, fun i => ?_⟩` and prove the remaining obligations. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[hs (fun i => M i j), map_mul, ← h1 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (a j))]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hM]`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Rewrite using `[hs (fun j => M i j), map_mul, ← h2 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (b i))]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hM, mul_right_comm]`.
-/
theorem UpperTheory.WildB.casimir :
    ∀ (E : Type) [Field E] [NumberField E] (d : 𝓞 E) (m : ℕ), d ∈ differentIdeal ℤ (𝓞 E) → d ≠ 0 → (∀ a ∈ differentIdeal ℤ (𝓞 E), d ∣ (m : 𝓞 E) * a) → ∃ (n : ℕ) (a b : Fin n → 𝓞 E) (lam : 𝓞 E →+ ℤ), (∀ x : 𝓞 E, ∑ j, lam (b j * x) • a j = (m : 𝓞 E) * x) ∧ (∀ x : 𝓞 E, ∃ M : Fin n → Fin n → ℤ, (∀ j, x * a j = ∑ i, M i j • a i) ∧ ∀ i, x * b i = ∑ j, M i j • b j) ∧ ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (φ ψ : E →+* C), ∑ j, φ (a j : E) * ψ (b j : E) = if ψ = φ then φ (d : E) else 0 := by
  intro E _ _ d m hd hd0 hm
  obtain ⟨lam, hlam⟩ := UpperTheory.WildB.traceForm E d m hd0 hm
  obtain ⟨n, a, b, h1, h2, h3⟩ := UpperTheory.WildB.dualFamily E d hd hd0
  have hs : ∀ (z : Fin n → ℤ) (c : Fin n → 𝓞 E),
      algebraMap (𝓞 E) E (∑ j, z j • c j) = ∑ j, (z j : ℚ) • (c j : E) := by
    intro z c
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
  refine ⟨n, a, b, lam, fun x => ?_, fun x => ?_,
    fun C _ _ _ φ ψ => UpperTheory.WildB.embSum E d hd0 n a b h1 C φ ψ⟩
  · apply RingOfIntegers.coe_injective
    rw [hs, map_mul, map_natCast, ← h1 ((m : E) * algebraMap (𝓞 E) E x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlam]
    congr 2
    change (m : E) * ((b j : E) * (x : E)) / (d : E) = (m : E) * (x : E) * (b j : E) / (d : E)
    ring
  · choose M hM using h3 x
    refine ⟨M, fun j => ?_, fun i => ?_⟩
    · apply RingOfIntegers.coe_injective
      rw [hs (fun i => M i j), map_mul, ← h1 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (a j))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hM]
    · apply RingOfIntegers.coe_injective
      rw [hs (fun j => M i j), map_mul, ← h2 (algebraMap (𝓞 E) E x * algebraMap (𝓞 E) E (b i))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hM, mul_right_comm]
