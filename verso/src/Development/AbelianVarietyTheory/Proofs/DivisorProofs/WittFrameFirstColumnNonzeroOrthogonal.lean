import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.AdaptedSplit

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Formalism.UG.cT, GlobalTheory.EisMidHt.firstColumn, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem cT_mulVec_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n r : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (Y : Matrix (Fin n) (Fin (r + 1)) E) (z : Fin n → E) :
    ((Formalism.UG.cT (σ : E →+* E) Y * J) *ᵥ z) 0 = hE σ J (GlobalTheory.EisMidHt.firstColumn Y) z := by
  simp only [hE, Formalism.UG.hform, Formalism.UG.cT, GlobalTheory.EisMidHt.firstColumn, Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hE_add_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (u y x : Fin n → E) (c : E) :
    hE σ J u (y + c • x) = hE σ J u y + c * hE σ J u x := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
theorem hE_smul {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (u x : Fin n → E) (l : E) :
    hE σ J u (l • x) = l * hE σ J u x := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring`.
-/
theorem hE_symm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hJ]; ring

end GlobalTheory.AdaptedSplit

open GlobalTheory.AdaptedSplit in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a hcm hJ hW hA`. Establish `hσ : ∀ e, σ (σ e) = e` using `fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e`. Establish `hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1`. Establish `h` using `congrFun (congrFun hW.xy 0) 0`. Rewrite `h` using `[Matrix.one_apply_eq, Matrix.mul_apply]`.

Rewrite using `[← cT_mulVec_zero, ← h]`. Both sides reduce to the same expression. Establish `hyx : hE σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn X) = 1`. Rewrite using `[hE_symm σ J hσ hJ.1, hxy, map_one]`. Establish `h0 : ∀ u : Fin n → E, hE σ J u 0 = 0` using `fun u => by simp [hE, Formalism.UG.hform]`.

Use `⟨fun hx => ?_, fun y h1 h2 => ⟨fun c hy hc => ?_, fun c l => ⟨fun hz => ?_, fun ⟨h3, h4⟩ => ?_⟩⟩⟩` and prove the remaining obligations. Rewrite `hxy` using `[hx]`. Simplify using `[hE, Formalism.UG.hform] at hxy`. Establish `h` using `congrArg (hE σ J (GlobalTheory.EisMidHt.firstColumn Y)) hc`. Rewrite `h` using `[hE_add_smul, h2, hyx, h0, zero_add, mul_one]`.

Rewrite `hc` using `[h, zero_smul, add_zero]`. Conclude with `hy hc`. Establish `h` using `(hA.split _ hz 0).1`. Establish `hX : Xᵀ 0 = GlobalTheory.EisMidHt.firstColumn X` using `rfl`. Rewrite `h` using `[cT_mulVec_zero, hE_smul, hE_add_smul, h2, hyx, zero_add, mul_one, hX]`.

Use `⟨?_, h⟩` and prove the remaining obligations. Establish `e : l • y = l • (y + c • GlobalTheory.EisMidHt.firstColumn X) - (l * c) • GlobalTheory.EisMidHt.firstColumn X`. Rewrite using `[smul_add, smul_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`.

Conclude with `L.sub_mem hz h`. Rewrite using `[smul_add, smul_smul]`. Conclude with `L.add_mem h3 h4`.
-/
theorem GlobalTheory.AdaptedSplit.smul_add_mem_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
      GlobalTheory.EisLine.IsAdapted σ J X Y L a →
      GlobalTheory.EisMidHt.firstColumn X ≠ 0 ∧
      ∀ y : Fin n → E, hE σ J (GlobalTheory.EisMidHt.firstColumn X) y = 0 → hE σ J (GlobalTheory.EisMidHt.firstColumn Y) y = 0 →
        (∀ c : E, y ≠ 0 → y + c • GlobalTheory.EisMidHt.firstColumn X ≠ 0) ∧
        ∀ c l : E, (l • (y + c • GlobalTheory.EisMidHt.firstColumn X) ∈ L ↔ l • y ∈ L ∧ (l * c) • GlobalTheory.EisMidHt.firstColumn X ∈ L) := by
  intro F E _ _ _ _ _ σ n J r X Y L a hcm hJ hW hA
  have hσ : ∀ e, σ (σ e) = e := fun e => GlobalTheory.SiegelSet.sigma_sigma (σ := σ) hcm e
  have hxy : hE σ J (GlobalTheory.EisMidHt.firstColumn X) (GlobalTheory.EisMidHt.firstColumn Y) = 1 := by
    have h := congrFun (congrFun hW.xy 0) 0
    rw [Matrix.one_apply_eq, Matrix.mul_apply] at h
    rw [← cT_mulVec_zero, ← h]
    rfl
  have hyx : hE σ J (GlobalTheory.EisMidHt.firstColumn Y) (GlobalTheory.EisMidHt.firstColumn X) = 1 := by
    rw [hE_symm σ J hσ hJ.1, hxy, map_one]
  have h0 : ∀ u : Fin n → E, hE σ J u 0 = 0 := fun u => by simp [hE, Formalism.UG.hform]
  refine ⟨fun hx => ?_, fun y h1 h2 => ⟨fun c hy hc => ?_, fun c l => ⟨fun hz => ?_, fun ⟨h3, h4⟩ => ?_⟩⟩⟩
  · rw [hx] at hxy
    simp [hE, Formalism.UG.hform] at hxy
  · have h := congrArg (hE σ J (GlobalTheory.EisMidHt.firstColumn Y)) hc
    rw [hE_add_smul, h2, hyx, h0, zero_add, mul_one] at h
    rw [h, zero_smul, add_zero] at hc
    exact hy hc
  · have h := (hA.split _ hz 0).1
    have hX : Xᵀ 0 = GlobalTheory.EisMidHt.firstColumn X := rfl
    rw [cT_mulVec_zero, hE_smul, hE_add_smul, h2, hyx, zero_add, mul_one, hX] at h
    refine ⟨?_, h⟩
    have e : l • y = l • (y + c • GlobalTheory.EisMidHt.firstColumn X) - (l * c) • GlobalTheory.EisMidHt.firstColumn X := by
      rw [smul_add, smul_smul]; abel
    rw [e]
    exact L.sub_mem hz h
  · rw [smul_add, smul_smul]
    exact L.add_mem h3 h4
