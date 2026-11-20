import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootDivisorSupportEmpty

/- English proof (translation)
Assemble the required witnesses or components as `⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hz]⟩`.
-/
theorem isIntegral_of_pow_eq_one {z : ℂ} {k : ℕ} (hk : 0 < k) (hz : z ^ k = 1) : IsIntegral ℤ z :=
  ⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hz]⟩

/- English proof (translation)
Establish `: M.det ∈ integralClosure ℤ ℂ`. Rewrite using `[Matrix.det_apply]`. Use `Subalgebra.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Conclude with `zsmul_mem (Subalgebra.prod_mem _ fun i _ => h _ _) _`.

Conclude with `this`.
-/
theorem isIntegral_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ a b, IsIntegral ℤ (M a b)) :
    IsIntegral ℤ M.det := by
  have : M.det ∈ integralClosure ℤ ℂ := by
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun σ _ => ?_
    rw [Units.smul_def]
    exact zsmul_mem (Subalgebra.prod_mem _ fun i _ => h _ _) _
  exact this

/- English proof (translation)
Use `isIntegral_det _ fun a b => ?_` and prove the remaining obligations. Simplify using `only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]`. Use `Fin.addCases (fun c => ?_) (fun c => ?_) ((p.2.1.orderEmbOfFin p.2.2) b)` and prove the remaining obligations. Rewrite using `[Fin.append_left, Matrix.one_apply] split_ifs`. Conclude with `isIntegral_one`.

Conclude with `isIntegral_zero`. Rewrite using `[Fin.append_right]`. Take `⟨k, hk, hz⟩` from `hζ p.1 a c`. Conclude with `isIntegral_of_pow_eq_one hk hz`.
-/
theorem isIntegral_rootCoord {f j m : ℕ} {ζ : Fin f → Matrix (Fin j) (Fin m) ℂ} (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine isIntegral_det _ fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  refine Fin.addCases (fun c => ?_) (fun c => ?_) ((p.2.1.orderEmbOfFin p.2.2) b)
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hz⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hz

end RootDivisorSupportEmpty

open RootDivisorSupportEmpty in

/- English proof (translation)
Introduce `f j m ζ hζ`. Use extensionality with `Q`. Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨hQmin, hrel⟩`. Establish `hQp : Q.IsPrime` using `hQmin.1.1`.

Establish `hle` using `hQmin.1.2`. Establish `hs : rootAnchorSection f j m ∈ Q` using `hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`. Take `⟨τ, -, hτ⟩` from `(hQp.prod_mem_iff).1 hs`. Take `⟨I, hI⟩` from `hrel τ`. Apply `hI` to reduce the goal to its premises.

Take `⟨p, hpm, hp⟩` from `isIntegral_rootCoord hζ ⟨τ, I⟩`. Use `set n := p.natDegree`. Use `set G : MRing (plBlocks f j m) := ∑ k ∈ Finset.range (n + 1), C (p.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (n - k) with hGdef`. Establish `hy0 : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1` using `anchor_minor _ _ _`. Establish `hG : G ∈ rootPointIdeal ζ`.

Rewrite using `[rootPointIdeal, mCoordIdeal, RingHom.mem_ker]`. Simplify using `only [hGdef, mConeMap, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hy0, MvPolynomial.C_1, one_mul]`. Establish `hterm : ∀ k ∈ Finset.range (n + 1), algebraMap ℤ (MvPolynomial (Fin f) ℂ) (p.coeff k) * (C (rootCoord ζ ⟨τ, I⟩) * X τ) ^ k * (X τ : MvPolynomial (Fin f) ℂ) ^ (n - k) = C ((p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k) * X τ ^ n`. Introduce `k hk`. Establish `hkn : k ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)`.

Rewrite using `[eq_intCast, ← map_intCast (C : ℂ →+* MvPolynomial (Fin f) ℂ), mul_pow, C_mul, C_pow, ← Nat.add_sub_cancel' hkn, pow_add, Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]`. Establish `hsum : ∑ k ∈ Finset.range (n + 1), (p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k = 0`. Rewrite using `[← hp, Polynomial.eval₂_eq_sum_range]`.

Simplify using `[n]`. Rewrite using `[hsum, MvPolynomial.C_0, zero_mul]`. Establish `hGQ : G ∈ Q` using `hle (Ideal.mem_sup_left hG)`. Establish `h0 : Ideal.Quotient.mk Q (X ⟨τ, plAnchor j m⟩) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 hτ`. Establish `hpow : Ideal.Quotient.mk Q (X ⟨τ, I⟩) ^ n = 0`.

Establish `h1` using `Ideal.Quotient.eq_zero_iff_mem.2 hGQ`. Simplify using `only [hGdef, map_sum, map_mul, map_pow, h0] at h1`. Rewrite `h1` using `[Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, pow_zero, mul_one, hpm.coeff_natDegree, map_one, map_one, one_mul]`. Conclude with `h1`. Introduce `k hk`.

Rewrite using `[zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)), mul_zero]`. Use `hQp` as an intermediate fact. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_pow_eq_zero hpow)`.
-/
theorem RootDivSuppEmpty.proof : RootDivSuppEmpty.Statement := by
  intro f j m ζ hζ
  ext Q
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hQmin, hrel⟩
  have hQp : Q.IsPrime := hQmin.1.1
  have hle := hQmin.1.2
  have hs : rootAnchorSection f j m ∈ Q := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  obtain ⟨τ, -, hτ⟩ := (hQp.prod_mem_iff).1 hs
  obtain ⟨I, hI⟩ := hrel τ
  apply hI
  obtain ⟨p, hpm, hp⟩ := isIntegral_rootCoord hζ ⟨τ, I⟩
  set n := p.natDegree
  set G : MRing (plBlocks f j m) := ∑ k ∈ Finset.range (n + 1),
    C (p.coeff k) * X ⟨τ, I⟩ ^ k * X ⟨τ, plAnchor j m⟩ ^ (n - k) with hGdef
  have hy0 : rootCoord ζ ⟨τ, plAnchor j m⟩ = 1 := anchor_minor _ _ _
  have hG : G ∈ rootPointIdeal ζ := by
    rw [rootPointIdeal, mCoordIdeal, RingHom.mem_ker]
    simp only [hGdef, mConeMap, map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      hy0, MvPolynomial.C_1, one_mul]
    have hterm : ∀ k ∈ Finset.range (n + 1),
        algebraMap ℤ (MvPolynomial (Fin f) ℂ) (p.coeff k) * (C (rootCoord ζ ⟨τ, I⟩) * X τ) ^ k *
          (X τ : MvPolynomial (Fin f) ℂ) ^ (n - k) =
        C ((p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k) * X τ ^ n := by
      intro k hk
      have hkn : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      rw [eq_intCast, ← map_intCast (C : ℂ →+* MvPolynomial (Fin f) ℂ), mul_pow, C_mul, C_pow,
        ← Nat.add_sub_cancel' hkn, pow_add, Nat.add_sub_cancel_left]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
    have hsum : ∑ k ∈ Finset.range (n + 1), (p.coeff k : ℂ) * rootCoord ζ ⟨τ, I⟩ ^ k = 0 := by
      rw [← hp, Polynomial.eval₂_eq_sum_range]
      simp [n]
    rw [hsum, MvPolynomial.C_0, zero_mul]
  have hGQ : G ∈ Q := hle (Ideal.mem_sup_left hG)
  have h0 : Ideal.Quotient.mk Q (X ⟨τ, plAnchor j m⟩) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hτ
  have hpow : Ideal.Quotient.mk Q (X ⟨τ, I⟩) ^ n = 0 := by
    have h1 := Ideal.Quotient.eq_zero_iff_mem.2 hGQ
    simp only [hGdef, map_sum, map_mul, map_pow, h0] at h1
    rw [Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self, pow_zero, mul_one,
      hpm.coeff_natDegree, map_one, map_one, one_mul] at h1
    · exact h1
    · intro k hk
      rw [zero_pow (Nat.sub_ne_zero_of_lt (Finset.mem_range.1 hk)), mul_zero]
  have := hQp
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_pow_eq_zero hpow)

end

end GroundTheory.Heights₂.Heights
