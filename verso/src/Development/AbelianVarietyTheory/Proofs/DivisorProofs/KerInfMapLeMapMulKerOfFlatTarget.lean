import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use `Submodule.smul_induction_on hz (fun r hr m _ => ⟨1, fun _ => r, fun _ => m, fun _ => hr, by simp⟩) ?_` and prove the remaining obligations. Introduce and unpack `x y ⟨n, b, p, hb, rfl⟩ ⟨n', b', p', hb', rfl⟩`. Use `⟨n + n', Fin.append b b', Fin.append p p', fun i => ?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hb, hb']`. Simplify using `[Fin.sum_univ_add]`.
-/
theorem exists_fin_sum_of_mem_ideal_smul_top {B P : Type} [CommRing B] [AddCommGroup P]
    [Module B P] (I : Ideal B) {z : P} (hz : z ∈ I • (⊤ : Submodule B P)) :
    ∃ (n : ℕ) (b : Fin n → B) (p : Fin n → P), (∀ i, b i ∈ I) ∧ ∑ i, b i • p i = z := by
  refine Submodule.smul_induction_on hz
    (fun r hr m _ => ⟨1, fun _ => r, fun _ => m, fun _ => hr, by simp⟩) ?_
  rintro x y ⟨n, b, p, hb, rfl⟩ ⟨n', b', p', hb', rfl⟩
  refine ⟨n + n', Fin.append b b', Fin.append p p', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hb, hb']
  · simp [Fin.sum_univ_add]

/- English proof (translation)
Introduce `B P A _ _ _ _ _ _ Ψ hΨ I z hz`. Establish `hz1 : Ψ z = 0` using `RingHom.mem_ker.1 hz.1`. Establish `hz2 : z ∈ I • (⊤ : Submodule B P)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hz.2`.

Take `⟨n, b, p, hb, rfl⟩` from `exists_fin_sum_of_mem_ideal_smul_top I hz2`. Establish `h0 : ∑ i, b i • Ψ (p i) = 0`. Simplify `hz1` using `[map_sum, map_smul]`. Take `⟨k, c, a, hx, hc⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := A) (f := b) (x := fun i => Ψ (p i)) h0`. Use `choose q hq using fun j => hΨ (a j)`.

Establish `hzero : ∑ i, ∑ j, (b i * c i j) • q j = 0`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul, hc j, zero_smul]`. Establish `key : ∑ i, b i • p i = ∑ i, b i • (p i - ∑ j, c i j • q j)`.

Simplify using `only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hzero, sub_zero]`. Rewrite using `[key]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hb i)) ?_` and prove the remaining obligations.

Rewrite using `[RingHom.mem_ker]`. Simplify using `only [map_sub, map_sum, map_smul, hq, ← hx i, sub_self]`.
-/
theorem ker_inf_map_le_map_mul_ker_of_flat :
    ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A]
      [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B,
      RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  intro B P A _ _ _ _ _ _ Ψ hΨ I z hz
  have hz1 : Ψ z = 0 := RingHom.mem_ker.1 hz.1
  have hz2 : z ∈ I • (⊤ : Submodule B P) := by
    rw [Ideal.smul_top_eq_map]; exact hz.2
  obtain ⟨n, b, p, hb, rfl⟩ := exists_fin_sum_of_mem_ideal_smul_top I hz2
  have h0 : ∑ i, b i • Ψ (p i) = 0 := by
    simpa [map_sum, map_smul] using hz1
  obtain ⟨k, c, a, hx, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := B) (M := A)
    (f := b) (x := fun i => Ψ (p i)) h0
  choose q hq using fun j => hΨ (a j)
  have hzero : ∑ i, ∑ j, (b i * c i j) • q j = 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_smul, hc j, zero_smul]
  have key : ∑ i, b i • p i = ∑ i, b i • (p i - ∑ j, c i j • q j) := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.smul_sum, smul_smul, hzero, sub_zero]
  rw [key]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hb i)) ?_
  rw [RingHom.mem_ker]
  simp only [map_sub, map_sum, map_smul, hq, ← hx i, sub_self]

end GlobalTheory
