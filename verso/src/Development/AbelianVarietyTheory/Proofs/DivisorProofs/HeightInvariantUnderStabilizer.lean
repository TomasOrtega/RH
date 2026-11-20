import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisCT

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1` using `congrArg (fun M => M 0 0) hW.xy`. Simplify using `only [Matrix.one_apply_eq] at h1`. Rewrite `h1` using `[Matrix.mul_apply]`.

Simplify using `[Matrix.mul_apply, Formalism.UG.cT, hc] at h1`.
-/
theorem exists_col0_ne_zero_of_witt {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ J X Y) :
    ∃ i, X i 0 ≠ 0 := by
  by_contra hc
  push_neg at hc
  have h1 := congrArg (fun M => M 0 0) hW.xy
  simp only [Matrix.one_apply_eq] at h1
  rw [Matrix.mul_apply] at h1
  simp [Matrix.mul_apply, Formalism.UG.cT, hc] at h1

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h hS p hp hst v`. Take `⟨-, -, -, -, hW, -, hI1, hI2⟩` from `hS`. Take `⟨lp, hlp⟩` from `hst`. Establish `key : absE F E lp = 1`. Rewrite `hp` using `[← range_ratEmb]`.

Take `⟨γ, rfl⟩` from `hp`. Take `⟨i, hi⟩` from `exists_col0_ne_zero_of_witt hW`. Establish `hmat : (matHom _ σ J (ratEmb σ J γ)).1 = (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F` using `F) (AF F)) := by`. Use extensionality with `s t`. Both sides reduce to the same expression.

Rewrite `hlp` using `[hmat]`. Establish `hent` using `congrArg (fun M => M i 0) hlp`. Simplify using `only [adMat] at hent`. Rewrite `hent` using `[← RingHom.map_matrix_mul]`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent`.

Establish `hx : col0 X i 0 = X i 0` using `rfl`. Rewrite `hent` using `[hx]`. Use `set e : E := ((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0 / X i 0 with he_def`. Establish `he : inclR (F` using `F) (AF F) e * inclR (F := F) (AF F) (X i 0) = inclR (F := F) (AF F) (((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0) := by`. Rewrite using `[← map_mul, he_def, div_mul_cancel₀ _ hi]`.

Establish `hu : IsUnit (inclR (F` using `F) (AF F) (X i 0)) := (isUnit_iff_ne_zero.2 hi).map _`. Establish `hl : lp.1 = inclR (F` using `F) (AF F) e := by`. Rewrite `hent` using `[← he]`. Conclude with `(hu.mul_left_inj.1 hent).symm`. Distinguish the cases in `he0 : e = 0`.

Rewrite `hl` using `[he0, map_zero]`. Establish `: Subsingleton (AF F ⊗[F] E)`. Establish `h01` using `lp.mul_inv`. Rewrite `h01` using `[hl, zero_mul]`. Conclude with `subsingleton_of_zero_eq_one h01`.

Rewrite using `[Subsingleton.elim lp 1, map_one]`. Use `GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 e he0)` as an intermediate fact. Rewrite `this` using `[show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 e he0)) = lp from Units.ext (by simp [hl])]`. Then use the resulting hypothesis. Take `⟨q, lq, hq, k, hk, rfl⟩` from `hI1 v`. Establish `e1 : h (q * k) = absE F E lq` using `hI2 q lq hq k hk`.

Establish `hpq : (matHom _ σ J (p * q)).1 * adMat F (col0 X) = (lp * lq).1 • adMat F (col0 X)`. Rewrite using `[map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hlp, smul_smul, Units.val_mul, mul_comm]`. Establish `e2 : h (p * q * k) = absE F E (lp * lq)` using `hI2 (p * q) (lp * lq) hpq k hk`. Rewrite using `[← mul_assoc, e2, e1, map_mul, key, one_mul]`.
-/
theorem iwaHt_mul_rat_stabL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), HidaSetting σ J X Y L a h →
    ∀ p ∈ ratPts σ J, GlobalTheory.EisCT.StabL σ J (col0 X) p → ∀ v, h (p * v) = h v := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hS p hp hst v
  obtain ⟨-, -, -, -, hW, -, hI1, hI2⟩ := hS
  obtain ⟨lp, hlp⟩ := hst
  have key : absE F E lp = 1 := by
    rw [← range_ratEmb] at hp
    obtain ⟨γ, rfl⟩ := hp
    obtain ⟨i, hi⟩ := exists_col0_ne_zero_of_witt hW
    have hmat : (matHom _ σ J (ratEmb σ J γ)).1 = (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) (AF F)) := by
      ext s t; rfl
    rw [hmat] at hlp
    have hent := congrArg (fun M => M i 0) hlp
    simp only [adMat] at hent
    rw [← RingHom.map_matrix_mul] at hent
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at hent
    have hx : col0 X i 0 = X i 0 := rfl
    rw [hx] at hent
    set e : E := ((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0 / X i 0 with he_def
    have he : inclR (F := F) (AF F) e * inclR (F := F) (AF F) (X i 0) =
        inclR (F := F) (AF F) (((γ.1.1 : Matrix (Fin n) (Fin n) E) * col0 X) i 0) := by
      rw [← map_mul, he_def, div_mul_cancel₀ _ hi]
    have hu : IsUnit (inclR (F := F) (AF F) (X i 0)) := (isUnit_iff_ne_zero.2 hi).map _
    have hl : lp.1 = inclR (F := F) (AF F) e := by
      rw [← he] at hent
      exact (hu.mul_left_inj.1 hent).symm
    by_cases he0 : e = 0
    · rw [he0, map_zero] at hl
      have : Subsingleton (AF F ⊗[F] E) := by
        have h01 := lp.mul_inv
        rw [hl, zero_mul] at h01
        exact subsingleton_of_zero_eq_one h01
      rw [Subsingleton.elim lp 1, map_one]
    · have := GlobalTheory.Doubling.absE_inclR (F := F) (E := E) (Units.mk0 e he0)
      rwa [show (Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 e he0)) = lp from
        Units.ext (by simp [hl])] at this
  obtain ⟨q, lq, hq, k, hk, rfl⟩ := hI1 v
  have e1 : h (q * k) = absE F E lq := hI2 q lq hq k hk
  have hpq : (matHom _ σ J (p * q)).1 * adMat F (col0 X) = (lp * lq).1 • adMat F (col0 X) := by
    rw [map_mul, Units.val_mul, Matrix.mul_assoc, hq, Matrix.mul_smul, hlp, smul_smul, Units.val_mul, mul_comm]
  have e2 : h (p * q * k) = absE F E (lp * lq) := hI2 (p * q) (lp * lq) hpq k hk
  rw [← mul_assoc, e2, e1, map_mul, key, one_mul]

end GlobalTheory.EisCT
