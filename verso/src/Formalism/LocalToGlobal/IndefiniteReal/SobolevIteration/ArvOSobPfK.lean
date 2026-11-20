import Formalism.LocalToGlobal.IndefiniteReal.SobolevIteration.ArvOSobPfSt

noncomputable section

open Formalism.IndefR.Datum Matrix
open scoped ComplexOrder

namespace Formalism.IndefR.Tow.SobPf

variable {n : ℕ}

/- English proof (translation)
Establish `h1 : star ((r : ℂ) • x) = (r : ℂ) • star x`. Rewrite using `[star_smul]`. Simplify using the standard rewrite rules. Rewrite using `[h1, Matrix.mulVec_smul]`. Simplify using `only [smul_dotProduct, dotProduct_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_smul (A : Matrix (Fin n) (Fin n) ℂ) (r : ℝ) (x : Fin n → ℂ) :
    (star ((r : ℂ) • x) ⬝ᵥ A *ᵥ ((r : ℂ) • x)) = (r : ℂ) ^ 2 * (star x ⬝ᵥ A *ᵥ x) := by

  have h1 : star ((r : ℂ) • x) = (r : ℂ) • star x := by
    rw [star_smul]; simp
  rw [h1, Matrix.mulVec_smul]
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `h : Continuous fun x : Fin n → ℂ => star x ⬝ᵥ A *ᵥ x`. Simplify using `only [dotProduct, Matrix.mulVec, Pi.star_apply]`. Use `fun_prop`. Conclude with `Complex.continuous_re.comp h`.
-/
theorem continuous_quad (A : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun x : Fin n → ℂ => (star x ⬝ᵥ A *ᵥ x).re := by
  have h : Continuous fun x : Fin n → ℂ => star x ⬝ᵥ A *ᵥ x := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    fun_prop
  exact Complex.continuous_re.comp h

/- English proof (translation)
Establish `sph : ∀ x : Fin n → ℂ, x ≠ 0 → ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 ∧ x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x)`. Introduce `x hx`. Establish `hnx : 0 < ‖x‖` using `norm_pos_iff.2 hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul]`.

Simplify using `[hnx.ne']`. Rewrite using `[smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnx.ne', Complex.ofReal_one, one_smul]`. Distinguish the cases in `hS : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty`. Take `⟨x0, hx0, hmin⟩` from `(isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS (continuous_quad A).continuousOn`. Establish `hx0ne : x0 ≠ 0`.

Introduce `h`. Rewrite `hx0` using `[h, mem_sphere_zero_iff_norm, norm_zero]`. Conclude with `zero_ne_one hx0`. Use `⟨(star x0 ⬝ᵥ A *ᵥ x0).re, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hA.dotProduct_mulVec_pos hx0ne`.

Establish `h2` using `(Complex.lt_def.1 h).1`. Simplify using `using h2`. Introduce `x`. Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality.

Simplify using the standard rewrite rules. Take `⟨hu, hxu⟩` from `sph x hx set u : Fin n → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def`. Establish `key : (star x ⬝ᵥ A *ᵥ x) = ((‖x‖ : ℝ) : ℂ) ^ 2 * (star u ⬝ᵥ A *ᵥ u)` using `by conv_lhs => rw [hxu]`. Conclude with `quad_smul A ‖x‖ u`. Establish `hre : (star x ⬝ᵥ A *ᵥ x).re = ‖x‖ ^ 2 * (star u ⬝ᵥ A *ᵥ u).re`.

Rewrite using `[key, ← Complex.ofReal_pow, Complex.re_ofReal_mul]`. Establish `hle : (star x0 ⬝ᵥ A *ᵥ x0).re ≤ (star u ⬝ᵥ A *ᵥ u).re` using `isMinOn_iff.1 hmin u hu`. Rewrite using `[hre, mul_comm]`. Conclude with `mul_le_mul_of_nonneg_left hle (sq_nonneg _)`. Use `⟨1, one_pos, fun x => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd ⟨_, (sph x hx).1⟩ hS`.
-/
theorem posDef_lower (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef) :
    ∃ c > (0 : ℝ), ∀ x : Fin n → ℂ, c * ‖x‖ ^ 2 ≤ (star x ⬝ᵥ A *ᵥ x).re := by

  have sph : ∀ x : Fin n → ℂ, x ≠ 0 →
      ((‖x‖⁻¹ : ℝ) : ℂ) • x ∈ Metric.sphere (0 : Fin n → ℂ) 1 ∧
        x = ((‖x‖ : ℝ) : ℂ) • (((‖x‖⁻¹ : ℝ) : ℂ) • x) := by
    intro x hx
    have hnx : 0 < ‖x‖ := norm_pos_iff.2 hx
    refine ⟨?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hnx.ne']
    · rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hnx.ne', Complex.ofReal_one, one_smul]
  by_cases hS : (Metric.sphere (0 : Fin n → ℂ) 1).Nonempty
  · obtain ⟨x0, hx0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℂ) 1).exists_isMinOn hS
      (continuous_quad A).continuousOn
    have hx0ne : x0 ≠ 0 := by
      intro h
      rw [h, mem_sphere_zero_iff_norm, norm_zero] at hx0
      exact zero_ne_one hx0
    refine ⟨(star x0 ⬝ᵥ A *ᵥ x0).re, ?_, ?_⟩
    · have h := hA.dotProduct_mulVec_pos hx0ne
      have h2 := (Complex.lt_def.1 h).1
      simpa using h2
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · obtain ⟨hu, hxu⟩ := sph x hx
        set u : Fin n → ℂ := ((‖x‖⁻¹ : ℝ) : ℂ) • x with hu_def
        have key : (star x ⬝ᵥ A *ᵥ x) = ((‖x‖ : ℝ) : ℂ) ^ 2 * (star u ⬝ᵥ A *ᵥ u) := by
          conv_lhs => rw [hxu]
          exact quad_smul A ‖x‖ u
        have hre : (star x ⬝ᵥ A *ᵥ x).re = ‖x‖ ^ 2 * (star u ⬝ᵥ A *ᵥ u).re := by
          rw [key, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
        have hle : (star x0 ⬝ᵥ A *ᵥ x0).re ≤ (star u ⬝ᵥ A *ᵥ u).re := isMinOn_iff.1 hmin u hu
        rw [hre, mul_comm]
        exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
  · refine ⟨1, one_pos, fun x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exact absurd ⟨_, (sph x hx).1⟩ hS

/- English proof (translation)
Establish `hk' : k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k` using `hk`. Establish `h1 : kᴴ * G * k = G` using `hk'.1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem KAt_pres {G s k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ KAt G s) : kᴴ * (G * s) * k = G * s := by

  have hk' : k ∈ Formalism.QuantumDeterminants.UH G ∧ k * s = s * k := hk
  have h1 : kᴴ * G * k = G := hk'.1
  calc kᴴ * (G * s) * k = kᴴ * G * (s * k) := by simp only [Matrix.mul_assoc]
    _ = kᴴ * G * (k * s) := by rw [hk'.2]
    _ = (kᴴ * G * k) * s := by simp only [Matrix.mul_assoc]
    _ = G * s := by rw [h1]

/- English proof (translation)
Establish `e : KAt G s = {g | gᴴ * G * g = G} ∩ {g | g * s = s * g}` using `Set.ext fun _ => Iff.rfl`. Rewrite using `[e]`. Use `IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ ?_)` and prove the remaining obligations. Conclude with `(continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id`. Conclude with `continuous_id.matrix_mul continuous_const`.

Conclude with `continuous_const.matrix_mul continuous_id`.
-/
theorem isClosed_KAt (G s : Matrix (Fin n) (Fin n) ℂ) : IsClosed (KAt G s) := by

  have e : KAt G s = {g | gᴴ * G * g = G} ∩ {g | g * s = s * g} := Set.ext fun _ => Iff.rfl
  rw [e]
  refine IsClosed.inter (isClosed_eq ?_ continuous_const) (isClosed_eq ?_ ?_)
  · exact (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  · exact continuous_id.matrix_mul continuous_const
  · exact continuous_const.matrix_mul continuous_id

/- English proof (translation)
Take `⟨-, -, hP⟩` from `hs`. Take `⟨c, hc, hcP⟩` from `posDef_lower (G * s) hP`. Establish `hvec : ∀ k ∈ KAt G s, ∀ x : Fin n → ℂ, ‖k *ᵥ x‖ ^ 2 ≤ (star x ⬝ᵥ (G * s) *ᵥ x).re / c`. Introduce `k hk x`. Establish `hpres : kᴴ * ((G * s) * k) = G * s`.

Rewrite using `[← Matrix.mul_assoc]`. Conclude with `KAt_pres hk`. Establish `h2 : star (k *ᵥ x) ⬝ᵥ (G * s) *ᵥ (k *ᵥ x) = star x ⬝ᵥ (G * s) *ᵥ x`. Rewrite using `[Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hpres, ← Matrix.dotProduct_mulVec]`. Establish `h1` using `hcP (k *ᵥ x)`.

Rewrite `h1` using `[h2]`. Rewrite using `[le_div_iff₀ hc, mul_comm]`. Conclude with `h1`. Use `IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (0 : ℂ) (Real.sqrt ((star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c))) (isClosed_KAt G s) ?_` and prove the remaining obligations. Introduce `k hk`.

Use `Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_` and prove the remaining obligations. Rewrite using `[mem_closedBall_zero_iff]`. Establish `hcomp : (k *ᵥ (Pi.single j 1 : Fin n → ℂ)) i = k i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hle : ‖k i j‖ ≤ ‖k *ᵥ (Pi.single j 1 : Fin n → ℂ)‖`.

Rewrite using `[← hcomp]`. Conclude with `norm_le_pi_norm _ i`. Establish `hsq : ‖k i j‖ ^ 2 ≤ (star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c` using `le_trans (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hvec k hk _)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isCompact_KAt {G s : Matrix (Fin n) (Fin n) ℂ} (hs : IsCartanInv G s) : IsCompact (KAt G s) := by
  obtain ⟨-, -, hP⟩ := hs
  obtain ⟨c, hc, hcP⟩ := posDef_lower (G * s) hP
  have hvec : ∀ k ∈ KAt G s, ∀ x : Fin n → ℂ,
      ‖k *ᵥ x‖ ^ 2 ≤ (star x ⬝ᵥ (G * s) *ᵥ x).re / c := by
    intro k hk x
    have hpres : kᴴ * ((G * s) * k) = G * s := by
      rw [← Matrix.mul_assoc]; exact KAt_pres hk
    have h2 : star (k *ᵥ x) ⬝ᵥ (G * s) *ᵥ (k *ᵥ x) = star x ⬝ᵥ (G * s) *ᵥ x := by
      rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
        hpres, ← Matrix.dotProduct_mulVec]
    have h1 := hcP (k *ᵥ x)
    rw [h2] at h1
    rw [le_div_iff₀ hc, mul_comm]
    exact h1
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_closedBall (0 : ℂ)
      (Real.sqrt ((star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c)))
    (isClosed_KAt G s) ?_
  intro k hk
  refine Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_
  rw [mem_closedBall_zero_iff]
  have hcomp : (k *ᵥ (Pi.single j 1 : Fin n → ℂ)) i = k i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hle : ‖k i j‖ ≤ ‖k *ᵥ (Pi.single j 1 : Fin n → ℂ)‖ := by
    rw [← hcomp]; exact norm_le_pi_norm _ i
  have hsq : ‖k i j‖ ^ 2 ≤ (star (Pi.single j 1 : Fin n → ℂ) ⬝ᵥ (G * s) *ᵥ (Pi.single j 1 : Fin n → ℂ)).re / c :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hle 2) (hvec k hk _)
  calc ‖k i j‖ = |‖k i j‖| := (abs_norm _).symm
    _ ≤ _ := Real.abs_le_sqrt hsq

end Formalism.IndefR.Tow.SobPf

end
