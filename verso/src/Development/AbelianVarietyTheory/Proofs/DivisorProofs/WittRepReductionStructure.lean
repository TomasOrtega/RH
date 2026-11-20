import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformizerSeparableReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReductionUniformizerNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicGeneratorsInvariantTopStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

/- English proof (translation)
Introduce `p _ Λ _ _ _ _ _ _ k _ _ _ h d N b s ρ hρ hch`. Take `⟨e, π, a, u, h0, he, hp, hmon, hmem, -, hψ⟩` from `GlobalTheory.T.exists_uniformizer_separable_reduction p Λ`. Set `c : WittVector p k →+* k` to `WittVector.constantCoeff`. Set `ψ : ℤ_[p] →+* k` to `c.comp s`. Set `Φ : Λ →+* Matrix (Fin h) (Fin h) k` to `c.mapMatrix.comp ρ`.

Establish `hΦ : ∀ l, Φ l = (ρ l).map c` using `fun l => rfl`. Take `⟨hsep, hcp⟩` from `hψ k ψ`. Establish `hsurj : Function.Surjective c` using `fun r => ⟨WittVector.teichmuller p r, by`. Simplify using `only [c, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩`. Establish `hker : ∀ w, c w = 0 → (p : WittVector p k) ∣ w` using `fun w hw => Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero w).2 hw)`.

Establish `hcp0 : c p = 0` using `by rw [map_natCast, CharP.cast_eq_zero]`. Take `⟨ht0, htk⟩` from `GlobalTheory.T.reduction_uniformizer_nilpotent p (WittVector p k) k Λ h e c ρ π u (WittVector.p_nonzero p k) hsurj hker hcp0 he hp`. Establish `hscal : Φ.comp (algebraMap ℤ_[p] Λ) = (algebraMap k (Matrix (Fin h) (Fin h) k)).comp ψ`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z)`.

Rewrite using `[hΦ, hρ, Algebra.algebraMap_eq_smul_one]`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [ψ, hij, Matrix.one_apply]`. Establish `hscal' : ∀ z (l : Λ), Φ (z • l) = ψ z • Φ l`. Introduce `z l`.

Establish `: Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z)` using `RingHom.congr_fun hscal z`. Rewrite using `[Algebra.smul_def, map_mul, this, ← Algebra.smul_def]`. Establish `haev : Polynomial.aeval (Φ a) (h0.map ψ) = Φ (Polynomial.aeval a h0)`. Rewrite using `[Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map, hscal]`. Take `⟨m, hm⟩` from `Ideal.mem_span_singleton.1 hmem`.

Establish `hT : (Φ a).charpoly = (h0.map ψ) ^ (e * N)`. Rewrite using `[hΦ, Matrix.charpoly_map, hch, Polynomial.map_map, Polynomial.map_pow, pow_mul, ← hcp]`. Take `⟨x, hx⟩` from `GlobalTheory.T.cyclic_generators_invariant_top k h e N (Φ π) (Φ a) (h0.map ψ) he (hmon.map ψ) hsep (by rw [← map_mul, ← map_mul, mul_comm]) ht0 htk (fun x => ⟨Φ m *ᵥ x, by rw [haev, hm, map_mul, Matrix.mulVec_mulVec]⟩) hT`. Use `⟨x, ?_⟩` and prove the remaining obligations. Use `set U := Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) with hU`.

Establish `key : ∀ (l : Λ) i, Φ l *ᵥ x i ∈ U`. Introduce `l i`. Rewrite using `[← b.sum_repr l, map_sum, Matrix.sum_mulVec]`. Use `U.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hscal', Matrix.smul_mulVec]`.

Conclude with `U.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)`. Establish `stab : ∀ (l : Λ), ∀ z ∈ U, Φ l *ᵥ z ∈ U`. Introduce `l z hz`. Establish `: U ≤ U.comap (Φ l).mulVecLin`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨⟨i, j⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `Φ l *ᵥ (Φ (b j) *ᵥ x i) ∈ U`. Rewrite using `[Matrix.mulVec_mulVec, ← map_mul]`. Conclude with `key _ _`. Conclude with `this hz`.

Use `hx U (fun i => ?_) (stab π) (stab a)` and prove the remaining obligations. Simplify using `using key 1 i`.
-/
theorem special_fibre_generators : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (h d N : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (s : ℤ_[p] →+* WittVector p k) (ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k)), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k))) → (∀ a : Λ, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s) → ∃ x : Fin N → Fin h → k, Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) = ⊤ := by
  intro p _ Λ _ _ _ _ _ _ k _ _ _ h d N b s ρ hρ hch
  obtain ⟨e, π, a, u, h0, he, hp, hmon, hmem, -, hψ⟩ := GlobalTheory.T.exists_uniformizer_separable_reduction p Λ
  let c : WittVector p k →+* k := WittVector.constantCoeff
  let ψ : ℤ_[p] →+* k := c.comp s
  let Φ : Λ →+* Matrix (Fin h) (Fin h) k := c.mapMatrix.comp ρ
  have hΦ : ∀ l, Φ l = (ρ l).map c := fun l => rfl
  obtain ⟨hsep, hcp⟩ := hψ k ψ
  have hsurj : Function.Surjective c := fun r =>
    ⟨WittVector.teichmuller p r, by
      simp only [c, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  have hker : ∀ w, c w = 0 → (p : WittVector p k) ∣ w := fun w hw =>
    Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero w).2 hw)
  have hcp0 : c p = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨ht0, htk⟩ := GlobalTheory.T.reduction_uniformizer_nilpotent p (WittVector p k) k Λ h e c ρ π u
    (WittVector.p_nonzero p k) hsurj hker hcp0 he hp
  have hscal : Φ.comp (algebraMap ℤ_[p] Λ) = (algebraMap k (Matrix (Fin h) (Fin h) k)).comp ψ := by
    refine RingHom.ext fun z => ?_
    change Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z)
    rw [hΦ, hρ, Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases hij : i = j <;> simp [ψ, hij, Matrix.one_apply]
  have hscal' : ∀ z (l : Λ), Φ (z • l) = ψ z • Φ l := by
    intro z l
    have : Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z) :=
      RingHom.congr_fun hscal z
    rw [Algebra.smul_def, map_mul, this, ← Algebra.smul_def]
  have haev : Polynomial.aeval (Φ a) (h0.map ψ) = Φ (Polynomial.aeval a h0) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
      hscal]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.1 hmem
  have hT : (Φ a).charpoly = (h0.map ψ) ^ (e * N) := by
    rw [hΦ, Matrix.charpoly_map, hch, Polynomial.map_map, Polynomial.map_pow, pow_mul, ← hcp]
  obtain ⟨x, hx⟩ := GlobalTheory.T.cyclic_generators_invariant_top k h e N (Φ π) (Φ a) (h0.map ψ) he (hmon.map ψ) hsep
    (by rw [← map_mul, ← map_mul, mul_comm]) ht0 htk
    (fun x => ⟨Φ m *ᵥ x, by rw [haev, hm, map_mul, Matrix.mulVec_mulVec]⟩) hT
  refine ⟨x, ?_⟩
  set U := Submodule.span k (Set.range fun ij : Fin N × Fin d =>
    (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) with hU
  have key : ∀ (l : Λ) i, Φ l *ᵥ x i ∈ U := by
    intro l i
    rw [← b.sum_repr l, map_sum, Matrix.sum_mulVec]
    refine U.sum_mem fun j _ => ?_
    rw [hscal', Matrix.smul_mulVec]
    exact U.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have stab : ∀ (l : Λ), ∀ z ∈ U, Φ l *ᵥ z ∈ U := by
    intro l z hz
    have : U ≤ U.comap (Φ l).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      change Φ l *ᵥ (Φ (b j) *ᵥ x i) ∈ U
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact key _ _
    exact this hz
  refine hx U (fun i => ?_) (stab π) (stab a)
  simpa using key 1 i

end GlobalTheory.DetInv
