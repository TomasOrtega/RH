import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCovolumeCommonAdelicFixatorOfColumnsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsConstAlongSingleton
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)

namespace GlobalTheory.FrameExt

/- English proof (translation)
Set `W` to `LinearMap.range Q.mulVecLin`. Set `b` to `Module.finBasis K W`. Establish `key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w`. Introduce and unpack `⟨w, v, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `[Matrix.mulVec_mulVec, hQ]`. Use `⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap), LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) = Q.mulVecLin` using `LinearMap.ext fun v => by simp`. Rewrite using `[this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`.

Rewrite using `[← LinearMap.toMatrix'_comp]`. Establish `: (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) = LinearMap.id` using `LinearMap.ext fun c => by`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key, LinearEquiv.apply_symm_apply, LinearMap.id_apply]`. Rewrite using `[this, LinearMap.toMatrix'_id]`.
-/
theorem idem_factor {K : Type} [Field K] {n : ℕ} (Q : Matrix (Fin n) (Fin n) K) (hQ : Q * Q = Q) :
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) K) (C : Matrix (Fin m) (Fin n) K), Z * C = Q ∧ C * Z = 1 := by
  let W := LinearMap.range Q.mulVecLin
  let b := Module.finBasis K W
  have key : ∀ w : W, Q.mulVecLin.rangeRestrict (w : Fin n → K) = w := by
    rintro ⟨w, v, rfl⟩
    apply Subtype.ext
    simp [Matrix.mulVec_mulVec, hQ]
  refine ⟨Module.finrank K W, LinearMap.toMatrix' (W.subtype ∘ₗ b.equivFun.symm.toLinearMap),
    LinearMap.toMatrix' (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    have : (W.subtype ∘ₗ b.equivFun.symm.toLinearMap) ∘ₗ (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict)
        = Q.mulVecLin := LinearMap.ext fun v => by simp
    rw [this, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix'_comp]
    have : (b.equivFun.toLinearMap ∘ₗ Q.mulVecLin.rangeRestrict) ∘ₗ (W.subtype ∘ₗ b.equivFun.symm.toLinearMap)
        = LinearMap.id := LinearMap.ext fun c => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype, key,
        LinearEquiv.apply_symm_apply, LinearMap.id_apply]
    rw [this, LinearMap.toMatrix'_id]

end GlobalTheory.FrameExt

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y hcm hJ hW`. Establish `hσ : ∀ e, σ (σ e) = e` using `fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e`. Establish `ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M` using `fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]`. Establish `cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0` using `Matrix.ext fun i j => by simp [Formalism.UG.cT]`. Establish `hJJ : cT (σ : E →+* E) J = J` using `Matrix.ext fun i j => hJ.1 i j`.

Establish `hBX : cT (σ : E →+* E) Y * J * X = 1` using `GlobalTheory.StdPar.yx hcm hJ hW`. Take `⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J` from `⟨_, rfl⟩`. Establish `hAX : A * X = 0` using `by rw [hA]; exact hW.xx`. Establish `hAY : A * Y = 1` using `by rw [hA]; exact hW.xy`.

Establish `hBY : B * Y = 0` using `by rw [hB]; exact hW.yy`. Establish `hBX' : B * X = 1` using `by rw [hB]; exact hBX`. Take `⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A` from `⟨_, rfl⟩`. Establish `hAQ : A * Q = 0`. Rewrite using `[hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]`.

Simplify using the standard rewrite rules. Establish `hBQ : B * Q = 0`. Rewrite using `[hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]`. Simplify using the standard rewrite rules. Establish `hQQ : Q * Q = Q`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]`. Use `_ = Q := by rw [hBQ, hAQ]; simp`. Take `⟨m, Z, C, hZC, hCZ⟩` from `GlobalTheory.FrameExt.idem_factor Q hQQ`. Establish `hQZ : Q * Z = Z` using `by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]`.

Establish `hAZ : A * Z = 0` using `by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]`. Establish `hBZ : B * Z = 0` using `by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]`. Establish `hzc : cT (σ : E →+* E) Z * J * X = 0`. Use `congrArg (cT (σ : E →+* E)) hAZ` as an intermediate fact. Rewrite `this` using `[hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.

Establish `hzd : cT (σ : E →+* E) Z * J * Y = 0`. Use `congrArg (cT (σ : E →+* E)) hBZ` as an intermediate fact. Rewrite `this` using `[hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Take `⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z` from `⟨_, rfl⟩`. Establish `hJ₀h : cT (σ : E →+* E) J₀ = J₀`.

Rewrite using `[hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]`. Establish `key : cT (σ : E →+* E) Z * J = J₀ * C`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hZC, hQ]`. Simplify using the standard rewrite rules.

Use `_ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by`. Rewrite using `[Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]`. Use `_ = J₀ * C := by rw [hzc, hzd]; simp`. Establish `hJZ : J * Z = cT (σ : E →+* E) C * J₀`. Use `congrArg (cT (σ : E →+* E)) key` as an intermediate fact.

Rewrite `this` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h]`. Then use the resulting hypothesis. Establish `hJu : IsUnit J.det` using `isUnit_iff_ne_zero.mpr hJ.2`. Establish `hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀)`. Rewrite using `[← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]`. Establish `hdet₀ : J₀.det ≠ 0`.

Use `Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_` and prove the remaining obligations. Rewrite using `[← hCZ, hZ]`. Simplify using `only [Matrix.mul_assoc]`. Establish `hJ₀u : IsUnit J₀.det` using `isUnit_iff_ne_zero.mpr hdet₀`. Use `⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩` and prove the remaining obligations.

Use `congrFun (congrFun hJ₀h i) j` as an intermediate fact. Simplify `this` using `[Formalism.UG.cT]`. Rewrite using `[← hA]`. Conclude with `hAZ`. Rewrite using `[← hB]`.

Conclude with `hBZ`. Rewrite using `[← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]`. Normalize the expressions using the abelian group laws. Establish `htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace`. Rewrite using `[← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]`.

Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite `htr` using `[Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ]`. Simplify using `only [Matrix.trace_one, Fintype.card_fin] at htr`. Establish `h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E)` using `by push_cast at htr ⊢; rw [htr]; ring`.

Conclude with `Nat.cast_injective h3`.
-/
theorem GlobalTheory.FrameExt.exists_fr : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E),
    IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∃ (m : ℕ) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J X Y Z J₀ := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ hW
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have ccT : ∀ {p q : ℕ} (M : Matrix (Fin p) (Fin q) E), cT (σ : E →+* E) (cT (σ : E →+* E) M) = M :=
    fun M => Matrix.ext fun i j => by simp [Formalism.UG.cT, hσ]
  have cT0 : ∀ {p q : ℕ}, cT (σ : E →+* E) (0 : Matrix (Fin p) (Fin q) E) = 0 :=
    Matrix.ext fun i j => by simp [Formalism.UG.cT]
  have hJJ : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hBX : cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx hcm hJ hW
  obtain ⟨A, hA⟩ : ∃ A, A = cT (σ : E →+* E) X * J := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = cT (σ : E →+* E) Y * J := ⟨_, rfl⟩
  have hAX : A * X = 0 := by rw [hA]; exact hW.xx
  have hAY : A * Y = 1 := by rw [hA]; exact hW.xy
  have hBY : B * Y = 0 := by rw [hB]; exact hW.yy
  have hBX' : B * X = 1 := by rw [hB]; exact hBX
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 - X * B - Y * A := ⟨_, rfl⟩
  have hAQ : A * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hAX, hAY]
    simp
  have hBQ : B * Q = 0 := by
    rw [hQ, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hBX', hBY]
    simp
  have hQQ : Q * Q = Q := by
    calc Q * Q = (1 - X * B - Y * A) * Q := by rw [← hQ]
      _ = Q - X * (B * Q) - Y * (A * Q) := by
        rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Q := by rw [hBQ, hAQ]; simp
  obtain ⟨m, Z, C, hZC, hCZ⟩ := GlobalTheory.FrameExt.idem_factor Q hQQ
  have hQZ : Q * Z = Z := by rw [← hZC, Matrix.mul_assoc, hCZ, Matrix.mul_one]
  have hAZ : A * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hAQ, Matrix.zero_mul]
  have hBZ : B * Z = 0 := by rw [← hQZ, ← Matrix.mul_assoc, hBQ, Matrix.zero_mul]

  have hzc : cT (σ : E →+* E) Z * J * X = 0 := by
    have := congrArg (cT (σ : E →+* E)) hAZ
    rwa [hA, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  have hzd : cT (σ : E →+* E) Z * J * Y = 0 := by
    have := congrArg (cT (σ : E →+* E)) hBZ
    rwa [hB, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, cT0, ← Matrix.mul_assoc] at this
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀, J₀ = cT (σ : E →+* E) Z * J * Z := ⟨_, rfl⟩
  have hJ₀h : cT (σ : E →+* E) J₀ = J₀ := by
    rw [hJ₀, Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, Matrix.mul_assoc]
  have key : cT (σ : E →+* E) Z * J = J₀ * C := by
    calc cT (σ : E →+* E) Z * J = cT (σ : E →+* E) Z * J * (X * B + Y * A + Z * C) := by
          rw [hZC, hQ]; simp
      _ = cT (σ : E →+* E) Z * J * X * B + cT (σ : E →+* E) Z * J * Y * A + J₀ * C := by
          rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ₀]
      _ = J₀ * C := by rw [hzc, hzd]; simp
  have hJZ : J * Z = cT (σ : E →+* E) C * J₀ := by
    have := congrArg (cT (σ : E →+* E)) key
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ccT, hJJ, hJ₀h] at this
  have hJu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
  have hZ : Z = J⁻¹ * (cT (σ : E →+* E) C * J₀) := by
    rw [← hJZ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJu, Matrix.one_mul]
  have hdet₀ : J₀.det ≠ 0 := by
    refine Matrix.det_ne_zero_of_left_inverse (B := C * J⁻¹ * cT (σ : E →+* E) C) ?_
    rw [← hCZ, hZ]; simp only [Matrix.mul_assoc]
  have hJ₀u : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hdet₀
  refine ⟨m, Z, J₀, ⟨hcm, hJ, ⟨fun i j => ?_, hdet₀⟩, hW.xx, hW.yy, hW.xy, hBX, ?_, ?_, hzc, hzd, hJ₀.symm, ?_, ?_⟩⟩
  · have := congrFun (congrFun hJ₀h i) j
    simpa [Formalism.UG.cT] using this
  · rw [← hA]; exact hAZ
  · rw [← hB]; exact hBZ
  · rw [← hA, ← hB, key, ← Matrix.mul_assoc J₀⁻¹, Matrix.nonsing_inv_mul _ hJ₀u, Matrix.one_mul, hZC, hQ]
    abel
  · have htr : (1 : Matrix (Fin n) (Fin n) E).trace = (X * B).trace + (Y * A).trace + (Z * C).trace := by
      rw [← Matrix.trace_add, ← Matrix.trace_add, hZC, hQ]; congr 1; abel
    rw [Matrix.trace_mul_comm X B, hBX', Matrix.trace_mul_comm Y A, hAY, Matrix.trace_mul_comm Z C, hCZ] at htr
    simp only [Matrix.trace_one, Fintype.card_fin] at htr
    have h3 : ((m + 2 * (r + 1) : ℕ) : E) = ((n : ℕ) : E) := by push_cast at htr ⊢; rw [htr]; ring
    exact Nat.cast_injective h3
