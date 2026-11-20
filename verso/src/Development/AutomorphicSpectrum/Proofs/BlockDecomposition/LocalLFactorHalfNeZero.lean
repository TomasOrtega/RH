import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LamUnr

section
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/- English proof (translation)
Unfold `IsUnramifiedChar`. Rewrite using `[MonoidHom.ker_one]`. Conclude with `le_top`.
-/
theorem isUnramifiedChar_one : IsUnramifiedChar (1 : Kˣ →* ℂˣ) := by
  unfold IsUnramifiedChar
  rw [MonoidHom.ker_one]
  exact le_top

/- English proof (translation)
Rewrite using `[localLFactor_of_isUnramified hu]`. Use `inv_ne_zero fun h0 => ?_` and prove the remaining obligations. Establish `hq : (1 : ℝ) < (residueCard K : ℝ)` using `by exact_mod_cast one_lt_residueCard (K := K)`. Establish `hqn : 0 < residueCard K` using `zero_lt_one.trans one_lt_residueCard`. Establish `hsq : (((μ (unifUnit K) : ℂˣ) : ℂ)) * ((μ (unifUnit K) : ℂˣ) : ℂ) = 1`.

Establish `h1` using `congrArg (fun f : Kˣ →* ℂˣ => ((f (unifUnit K) : ℂˣ) : ℂ)) hμ`. Simplify using `using h1`. Establish `hn1 : ‖((μ (unifUnit K) : ℂˣ) : ℂ)‖ = 1`. Establish `h2` using `congrArg norm hsq`. Rewrite `h2` using `[norm_mul, norm_one]`.

Use polynomial arithmetic with `[norm_nonneg (((μ (unifUnit K) : ℂˣ) : ℂ))]`. Establish `hn2 : ‖(residueCard K : ℂ) ^ (-(1 / 2 : ℂ))‖ < 1`. Rewrite using `[Complex.norm_natCast_cpow_of_pos hqn]`. Establish `hre : (-(1 / 2 : ℂ)).re = -(1 / 2)` using `by norm_num`. Rewrite using `[hre]`.

Conclude with `Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)`. Establish `h3 : ((μ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 / 2 : ℂ)) = 1` using `(sub_eq_zero.mp h0).symm`. Establish `h4` using `congrArg norm h3`. Rewrite `h4` using `[norm_mul, hn1, one_mul, norm_one]`. Conclude with `hn2.ne h4`.
-/
theorem localLFactor_half_ne_zero {μ : Kˣ →* ℂˣ} (hu : IsUnramifiedChar μ) (hμ : μ * μ = 1) :
    localLFactor μ (1 / 2) ≠ 0 := by
  rw [localLFactor_of_isUnramified hu]
  refine inv_ne_zero fun h0 => ?_
  have hq : (1 : ℝ) < (residueCard K : ℝ) := by exact_mod_cast one_lt_residueCard (K := K)
  have hqn : 0 < residueCard K := zero_lt_one.trans one_lt_residueCard
  have hsq : (((μ (unifUnit K) : ℂˣ) : ℂ)) * ((μ (unifUnit K) : ℂˣ) : ℂ) = 1 := by
    have h1 := congrArg (fun f : Kˣ →* ℂˣ => ((f (unifUnit K) : ℂˣ) : ℂ)) hμ
    simpa using h1
  have hn1 : ‖((μ (unifUnit K) : ℂˣ) : ℂ)‖ = 1 := by
    have h2 := congrArg norm hsq
    rw [norm_mul, norm_one] at h2
    nlinarith [norm_nonneg (((μ (unifUnit K) : ℂˣ) : ℂ))]
  have hn2 : ‖(residueCard K : ℂ) ^ (-(1 / 2 : ℂ))‖ < 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hqn]
    have hre : (-(1 / 2 : ℂ)).re = -(1 / 2) := by norm_num
    rw [hre]
    exact Real.rpow_lt_one_of_one_lt_of_neg hq (by norm_num)
  have h3 : ((μ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-(1 / 2 : ℂ)) = 1 :=
    (sub_eq_zero.mp h0).symm
  have h4 := congrArg norm h3
  rw [norm_mul, hn1, one_mul, norm_one] at h4
  exact hn2.ne h4

variable [MeasurableSpace K] [BorelSpace K]

/- English proof (translation)
Establish `hinv : μ⁻¹ = μ` using `(eq_inv_of_mul_eq_one_left hμ).symm`. Establish `hs : (1 : ℂ) - 1 / 2 = 1 / 2` using `by norm_num`. Establish `hL` using `localLFactor_half_ne_zero hu hμ`. Unfold `gam`. Rewrite using `[hinv, hs, localEpsilon_of_isUnramified hu, hψ]`.

Simplify using `only [neg_zero, zpow_zero, Int.cast_zero, zero_mul, Complex.cpow_zero, one_mul]`. Conclude with `div_self hL`.
-/
theorem gam_half_eq_one {ψ : AddChar K Circle} (hψ : addCharConductor ψ = 0) {μ : Kˣ →* ℂˣ}
    (hu : IsUnramifiedChar μ) (hμ : μ * μ = 1) : gam ψ μ (1 / 2) = 1 := by
  have hinv : μ⁻¹ = μ := (eq_inv_of_mul_eq_one_left hμ).symm
  have hs : (1 : ℂ) - 1 / 2 = 1 / 2 := by norm_num
  have hL := localLFactor_half_ne_zero hu hμ
  unfold gam
  rw [hinv, hs, localEpsilon_of_isUnramified hu, hψ]
  simp only [neg_zero, zpow_zero, Int.cast_zero, zero_mul, Complex.cpow_zero, one_mul]
  exact div_self hL

end

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ χ η hχ hχE hu hη`. Unfold `Ad3.K.GL2LocalData.lamE`. Rewrite using `[gam_half_eq_one hχ.2.2 isUnramifiedChar_one (mul_one 1), gam_half_eq_one hχ.2.2 hu hη, gam_half_eq_one hχE.2.2 isUnramifiedChar_one (mul_one 1)]`. Evaluate the numerical expressions.
-/
theorem lamE_eq_one : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] (χ : AddChar F Circle) (η : Fˣ →* ℂˣ), Ad3.IsStd χ → Ad3.IsStd (Ad3.K.GL2LocalData.chE E χ) → IsUnramifiedChar η → η * η = 1 → Ad3.K.GL2LocalData.lamE E χ η = 1 := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ χ η hχ hχE hu hη
  unfold Ad3.K.GL2LocalData.lamE
  rw [gam_half_eq_one hχ.2.2 isUnramifiedChar_one (mul_one 1), gam_half_eq_one hχ.2.2 hu hη,
    gam_half_eq_one hχE.2.2 isUnramifiedChar_one (mul_one 1)]
  norm_num

end GlobalTheory.CompanionTheory.LamUnr
