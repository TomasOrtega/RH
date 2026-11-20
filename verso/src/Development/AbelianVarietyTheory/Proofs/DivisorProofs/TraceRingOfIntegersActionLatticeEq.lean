import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleDvdOfDvdCharpolyOfAevalMatrix
open NumberField Polynomial IntermediateField

namespace GlobalTheory.LatticeTrace

/- English proof (translation)
Introduce `F _ _ O _ _ La _ _ _ _ k hk c`. Use `set n := Module.finrank ℤ La with hn`. Set `φ : 𝓞 F →+* Module.End ℤ La` to `((addMonoidEndRingEquivInt La).toRingHom.comp (Module.toAddMonoidEnd O La)).comp (algebraMap (𝓞 F) O)`. Establish `hφ : φ c = (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap` using `rfl`. Set `b` to `Module.finBasis ℤ La`.

Use `set M := LinearMap.toMatrix b b (φ c) with hM`. Use `set M' := M.map (algebraMap ℤ ℚ) with hM'`. Establish `hx : IsIntegral ℚ (c : F)` using `Algebra.IsIntegral.isIntegral _`. Use `set f := minpoly ℚ (c : F) with hf`. Establish `hfmon : f.Monic` using `minpoly.monic hx`.

Establish `hfirr : Irreducible f` using `minpoly.irreducible hx`. Establish `hfZ : f = (minpoly ℤ c).map (algebraMap ℤ ℚ)`. Rewrite using `[hf, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe c), RingOfIntegers.minpoly_coe]`. Establish `hT : aeval (φ c) (minpoly ℤ c) = 0`. Rewrite using `[show φ c = (RingHom.toIntAlgHom φ) c from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]`.

Establish `hMz : aeval M (minpoly ℤ c) = 0`. Establish `hMe : M = LinearMap.toMatrixAlgEquiv b (φ c)` using `rfl`. Rewrite using `[hMe, aeval_algHom_apply, hT, map_zero]`. Establish `hM'f : aeval M' f = 0`. Rewrite using `[hfZ, aeval_map_algebraMap, hM', show M.map (algebraMap ℤ ℚ) = (Algebra.ofId ℤ ℚ).mapMatrix M from rfl, aeval_algHom_apply, hMz, map_zero]`.

Use `set r := Module.finrank ℚ⟮(c : F)⟯ F with hr`. Establish `hdeg : Module.finrank ℚ F = f.natDegree * r`. Rewrite using `[← Module.finrank_mul_finrank ℚ ℚ⟮(c : F)⟯ F, IntermediateField.adjoin.finrank hx]`. Establish `hsize : n = f.natDegree * (k * r)`. Rewrite using `[hk, hdeg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcp : M'.charpoly = f ^ (k * r)` using `GlobalTheory.charpoly_eq_pow_of_aeval_irreducible_eq_zero ℚ n (k * r) M' f hfmon hfirr hM'f hsize`. Establish `htr : (M'.trace : ℚ) = (k * r : ℚ) * -(f.nextCoeff)`. Break down `Nat.eq_zero_or_pos n with h0 | hpos` into its components or cases. Establish `hk0 : k * r = 0`.

Use `hsize` as an intermediate fact. Rewrite `this` using `[h0]`. Break down `Nat.mul_eq_zero.1 this.symm with h | h` into its components or cases. Conclude with `absurd h (Irreducible.natDegree_pos hfirr).ne'`. Conclude with `h`.

Establish `: M'.trace = 0` using `by haveI : IsEmpty (Fin (Module.finrank ℤ La)) := by rw [← hn, h0]; infer_instance`. Simplify using `[Matrix.trace]`. Rewrite using `[this]`. Establish `: (k * r : ℚ) = 0` using `by exact_mod_cast hk0`. Rewrite using `[this, zero_mul]`.

Use `haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩`. Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, hcp, Fintype.card_fin]`. Establish `hnd : (f ^ (k * r)).natDegree = n` using `by rw [hfmon.natDegree_pow, hsize]; ring`. Establish `hne : (f ^ (k * r)).nextCoeff = (f ^ (k * r)).coeff (n - 1)`. Rewrite using `[nextCoeff, hnd, if_neg hpos.ne']`.

Rewrite using `[← hne, hfmon.nextCoeff_pow, nsmul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hTr : (∑ τ : F →+* ℂ, τ (c : F)) = algebraMap ℚ ℂ (Algebra.trace ℚ F c)`. Rewrite using `[trace_eq_sum_embeddings ℂ]`.

Conclude with `Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)`. Establish `hTr2 : Algebra.trace ℚ F c = (r : ℚ) * -(f.nextCoeff)` using `trace_eq_finrank_mul_minpoly_nextCoeff ℚ _`. Establish `hL : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ) = M'.trace`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℤ b, hM', ← hM]`. Conclude with `AddMonoidHom.map_trace (algebraMap ℤ ℚ) M`.

Rewrite using `[← hφ, hTr, hTr2]`. Establish `: ((LinearMap.trace ℤ La (φ c) : ℤ) : ℂ) = algebraMap ℚ ℂ (((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ))` using `by simp`. Rewrite using `[this, hL, htr]`. Simplify using `only [map_mul, map_neg, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem trace_lattice_eq : ∀ (F : Type) [Field F] [NumberField F] (O : Type) [Ring O] [Algebra (𝓞 F) O] (La : Type) [AddCommGroup La] [Module O La] [Module.Free ℤ La] [Module.Finite ℤ La] (k : ℕ), Module.finrank ℤ La = k * Module.finrank ℚ F → ∀ c : 𝓞 F, ((LinearMap.trace ℤ La (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap : ℤ) : ℂ) = (k : ℂ) * ∑ τ : F →+* ℂ, τ (c : F) := by
  intro F _ _ O _ _ La _ _ _ _ k hk c
  classical
  set n := Module.finrank ℤ La with hn

  let φ : 𝓞 F →+* Module.End ℤ La :=
    ((addMonoidEndRingEquivInt La).toRingHom.comp (Module.toAddMonoidEnd O La)).comp (algebraMap (𝓞 F) O)
  have hφ : φ c = (DistribMulAction.toAddMonoidHom La (algebraMap (𝓞 F) O c)).toIntLinearMap := rfl
  let b := Module.finBasis ℤ La
  set M := LinearMap.toMatrix b b (φ c) with hM
  set M' := M.map (algebraMap ℤ ℚ) with hM'
  have hx : IsIntegral ℚ (c : F) := Algebra.IsIntegral.isIntegral _
  set f := minpoly ℚ (c : F) with hf
  have hfmon : f.Monic := minpoly.monic hx
  have hfirr : Irreducible f := minpoly.irreducible hx
  have hfZ : f = (minpoly ℤ c).map (algebraMap ℤ ℚ) := by
    rw [hf, minpoly.isIntegrallyClosed_eq_field_fractions' ℚ (RingOfIntegers.isIntegral_coe c),
      RingOfIntegers.minpoly_coe]
  have hT : aeval (φ c) (minpoly ℤ c) = 0 := by
    rw [show φ c = (RingHom.toIntAlgHom φ) c from rfl, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hMz : aeval M (minpoly ℤ c) = 0 := by
    have hMe : M = LinearMap.toMatrixAlgEquiv b (φ c) := rfl
    rw [hMe, aeval_algHom_apply, hT, map_zero]
  have hM'f : aeval M' f = 0 := by
    rw [hfZ, aeval_map_algebraMap, hM', show M.map (algebraMap ℤ ℚ) = (Algebra.ofId ℤ ℚ).mapMatrix M from rfl,
      aeval_algHom_apply, hMz, map_zero]

  set r := Module.finrank ℚ⟮(c : F)⟯ F with hr
  have hdeg : Module.finrank ℚ F = f.natDegree * r := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮(c : F)⟯ F, IntermediateField.adjoin.finrank hx]
  have hsize : n = f.natDegree * (k * r) := by
    rw [hk, hdeg]; ring
  have hcp : M'.charpoly = f ^ (k * r) :=
    GlobalTheory.charpoly_eq_pow_of_aeval_irreducible_eq_zero ℚ n (k * r) M' f hfmon hfirr hM'f hsize

  have htr : (M'.trace : ℚ) = (k * r : ℚ) * -(f.nextCoeff) := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · have hk0 : k * r = 0 := by
        have := hsize; rw [h0] at this
        rcases Nat.mul_eq_zero.1 this.symm with h | h
        · exact absurd h (Irreducible.natDegree_pos hfirr).ne'
        · exact h
      have : M'.trace = 0 := by
        haveI : IsEmpty (Fin (Module.finrank ℤ La)) := by rw [← hn, h0]; infer_instance
        simp [Matrix.trace]
      rw [this]
      have : (k * r : ℚ) = 0 := by exact_mod_cast hk0
      rw [this, zero_mul]
    · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, hcp, Fintype.card_fin]
      have hnd : (f ^ (k * r)).natDegree = n := by rw [hfmon.natDegree_pow, hsize]; ring
      have hne : (f ^ (k * r)).nextCoeff = (f ^ (k * r)).coeff (n - 1) := by
        rw [nextCoeff, hnd, if_neg hpos.ne']
      rw [← hne, hfmon.nextCoeff_pow, nsmul_eq_mul]
      push_cast; ring

  have hTr : (∑ τ : F →+* ℂ, τ (c : F)) = algebraMap ℚ ℂ (Algebra.trace ℚ F c) := by
    rw [trace_eq_sum_embeddings ℂ]
    exact Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun _ => rfl)
  have hTr2 : Algebra.trace ℚ F c = (r : ℚ) * -(f.nextCoeff) := trace_eq_finrank_mul_minpoly_nextCoeff ℚ _
  have hL : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ) = M'.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℤ b, hM', ← hM]
    exact AddMonoidHom.map_trace (algebraMap ℤ ℚ) M
  rw [← hφ, hTr, hTr2]
  have : ((LinearMap.trace ℤ La (φ c) : ℤ) : ℂ) = algebraMap ℚ ℂ (((LinearMap.trace ℤ La (φ c) : ℤ) : ℚ)) := by simp
  rw [this, hL, htr]
  simp only [map_mul, map_neg, map_natCast]
  ring

end GlobalTheory.LatticeTrace
