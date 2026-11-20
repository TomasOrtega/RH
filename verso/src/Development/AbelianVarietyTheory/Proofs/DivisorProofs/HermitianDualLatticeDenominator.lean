import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualLatticeBoundedDenominator

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.TraceDenom

/- English proof (translation)
Establish `h : ∀ i, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * f i)`. Introduce `i`. Establish `hal : IsAlgebraic ℤ (f i)` using `(IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (f i))`. Take `⟨y, hy0, hy⟩` from `hal.exists_integral_multiple`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩` and prove the remaining obligations.

Break down `Int.natAbs_eq y with h | h` into its components or cases. Establish `e : ((y.natAbs : ℕ) : E) = (y : E)`. Rewrite using `[← Int.cast_natCast]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e, ← zsmul_eq_mul]`. Conclude with `hy`. Establish `e : ((y.natAbs : ℕ) : E) = -(y : E)`. Rewrite using `[← Int.cast_natCast, ← Int.cast_neg]`. Use `congr 1`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[e, neg_mul, ← zsmul_eq_mul]`. Conclude with `hy.neg`. Use `choose m hm0 hm using h`. Use `⟨∏ i, m i, Finset.prod_pos (fun i _ => hm0 i), fun i => ?_⟩` and prove the remaining obligations.

Take `⟨k, hk⟩` from `Finset.dvd_prod_of_mem m (Finset.mem_univ i)`. Rewrite using `[hk, Nat.cast_mul, mul_comm ((m i : ℕ) : E), mul_assoc]`. Establish `hk' : IsIntegral ℤ ((k : ℕ) : E)`. Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ)))`. Conclude with `hk'.mul (hm i)`.
-/
theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]
    (f : ι → E) : ∃ m : ℕ, 0 < m ∧ ∀ i, IsIntegral ℤ ((m : E) * f i) := by
  have h : ∀ i, ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * f i) := by
    intro i
    have hal : IsAlgebraic ℤ (f i) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (f i))
    obtain ⟨y, hy0, hy⟩ := hal.exists_integral_multiple
    refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
        rw [← Int.cast_natCast]; congr 1; omega
      rw [e, ← zsmul_eq_mul]; exact hy
    · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
        rw [← Int.cast_natCast, ← Int.cast_neg]; congr 1; omega
      rw [e, neg_mul, ← zsmul_eq_mul]; exact hy.neg
  choose m hm0 hm using h
  refine ⟨∏ i, m i, Finset.prod_pos (fun i _ => hm0 i), fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  rw [hk, Nat.cast_mul, mul_comm ((m i : ℕ) : E), mul_assoc]
  have hk' : IsIntegral ℤ ((k : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (k : ℤ)))
  exact hk'.mul (hm i)

/- English proof (translation)
Take `⟨x, hx⟩` from `σ.bijective.2 (b : E)`. Establish `h1 : IsIntegral ℤ (σ.toRingHom.toIntAlgHom x)`. Express the relevant statement in the definitionally equal form `IsIntegral ℤ (σ x)`. Rewrite using `[hx]`. Conclude with `b.isIntegral_coe`.

Establish `hint : IsIntegral ℤ x` using `(isIntegral_algHom_iff (σ.toRingHom.toIntAlgHom) σ.injective).1 h1`. Conclude with `⟨⟨x, hint⟩, hx⟩`.
-/
theorem exists_preimage_ringOfIntegers {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (b : 𝓞 E) : ∃ a : 𝓞 E, σ (a : E) = b := by
  obtain ⟨x, hx⟩ := σ.bijective.2 (b : E)
  have h1 : IsIntegral ℤ (σ.toRingHom.toIntAlgHom x) := by
    change IsIntegral ℤ (σ x); rw [hx]; exact b.isIntegral_coe
  have hint : IsIntegral ℤ x :=
    (isIntegral_algHom_iff (σ.toRingHom.toIntAlgHom) σ.injective).1 h1
  exact ⟨⟨x, hint⟩, hx⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J hJ c hc`. Take `⟨D, hD, hDual⟩` from `GlobalTheory.exists_den_traceDual_ringOfIntegers (F := E)`. Take `⟨M, hM, hMint⟩` from `exists_nat_mul_isIntegral (fun p : Fin n × Fin n => c⁻¹ * J⁻¹ p.1 p.2)`. Use `⟨D * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD.ne' hM.ne'), fun ξ hξ i => ?_⟩` and prove the remaining obligations. Establish `hv : ∀ k, ∃ o : 𝓞 E, (D : E) * (c * (ξ ᵥ* J) k) = o`.

Introduce `k`. Apply `hDual` to reduce the goal to its premises. Introduce `b`. Take `⟨a, ha⟩` from `exists_preimage_ringOfIntegers σ b`. Take `⟨z, hz⟩` from `hξ (Pi.single k a)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz]`. Use `congr 1`. Establish `hs : (fun j => σ (((Pi.single k a : Fin n → 𝓞 E) j : E))) = Pi.single k (σ (a : E))`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = k`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hj]`. Simplify using `only [form, Matrix.dotProduct_mulVec, hs]`.

Simplify using `[dotProduct, Pi.single_apply, ha, mul_assoc]`. Use `choose o ho using hv`. Establish `hunit : IsUnit J.det` using `hJ.isUnit`. Establish `hξeq : ξ = (ξ ᵥ* J) ᵥ* J⁻¹`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hunit, Matrix.vecMul_one]`.

Generalize the expression as in `ξ ᵥ* J = v at ho hξeq`. Establish `hexp : ((D * M : ℕ) : E) * ξ i = ∑ k, (D : E) * (c * v k) * ((M : E) * (c⁻¹ * J⁻¹ k i))`. Rewrite using `[hξeq]`. Simplify using `only [Matrix.vecMul, dotProduct, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hint : IsIntegral ℤ (((D * M : ℕ) : E) * ξ i)`. Rewrite using `[hexp]`. Use `IsIntegral.sum _ fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[ho k]`. Conclude with `(o k).isIntegral_coe.mul (hMint (k, i))`. Conclude with `⟨⟨_, hint⟩, rfl⟩`.
-/
theorem nat_mul_integral_of_trace_form_int : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : J.det ≠ 0) (c : E) (hc : c ≠ 0),
    ∃ N : ℕ, 1 ≤ N ∧ ∀ ξ : Fin n → E, (∀ β : Fin n → 𝓞 E, ∃ z : ℤ, Algebra.trace ℚ E (c * form σ J ξ (fun i => (β i : E))) = z) →
      ∀ i, ∃ o : 𝓞 E, (N : E) * ξ i = o := by
  intro F E _ _ _ _ _ σ n J hJ c hc
  obtain ⟨D, hD, hDual⟩ := GlobalTheory.exists_den_traceDual_ringOfIntegers (F := E)
  obtain ⟨M, hM, hMint⟩ := exists_nat_mul_isIntegral (fun p : Fin n × Fin n => c⁻¹ * J⁻¹ p.1 p.2)
  refine ⟨D * M, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hD.ne' hM.ne'), fun ξ hξ i => ?_⟩
  have hv : ∀ k, ∃ o : 𝓞 E, (D : E) * (c * (ξ ᵥ* J) k) = o := by
    intro k
    apply hDual
    intro b
    obtain ⟨a, ha⟩ := exists_preimage_ringOfIntegers σ b
    obtain ⟨z, hz⟩ := hξ (Pi.single k a)
    refine ⟨z, ?_⟩
    rw [← hz]
    congr 1
    have hs : (fun j => σ (((Pi.single k a : Fin n → 𝓞 E) j : E))) = Pi.single k (σ (a : E)) := by
      funext j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    simp only [form, Matrix.dotProduct_mulVec, hs]
    simp [dotProduct, Pi.single_apply, ha, mul_assoc]
  choose o ho using hv
  have hunit : IsUnit J.det := hJ.isUnit
  have hξeq : ξ = (ξ ᵥ* J) ᵥ* J⁻¹ := by
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hunit, Matrix.vecMul_one]
  generalize ξ ᵥ* J = v at ho hξeq
  have hexp : ((D * M : ℕ) : E) * ξ i =
      ∑ k, (D : E) * (c * v k) * ((M : E) * (c⁻¹ * J⁻¹ k i)) := by
    rw [hξeq]
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    field_simp
  have hint : IsIntegral ℤ (((D * M : ℕ) : E) * ξ i) := by
    rw [hexp]
    refine IsIntegral.sum _ fun k _ => ?_
    rw [ho k]
    exact (o k).isIntegral_coe.mul (hMint (k, i))
  exact ⟨⟨_, hint⟩, rfl⟩

end GlobalTheory.TraceDenom
