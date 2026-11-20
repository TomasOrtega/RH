import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedMaxCompactVector
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2 lc)
open scoped NumberField.AdeleRing ValuativeRel
open Ad3.K.GL2LocalData

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitPi.Iwasawa

open GlobalTheory.CompanionTheory.SplitRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def rd (g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  !![g.val 0 0 / (g.val).det, g.val 0 1 / (g.val).det; g.val 1 0, g.val 1 1]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `hd` using `det_ne g`. Establish `e` using `Matrix.det_fin_two g.val`. Rewrite using `[rd, Matrix.det_fin_two_of]`. Clear the denominators using the available nonvanishing facts. Conclude with `e.symm`.
-/
theorem rd_det (g : GL (Fin 2) F) : (rd g).det = 1 := by
  have hd := det_ne g
  have e := Matrix.det_fin_two g.val
  rw [rd, Matrix.det_fin_two_of]
  field_simp
  exact e.symm

/- English proof (translation)
Establish `hd` using `det_ne g`. Establish `h` using `dil χ (rd_det g) hd Φ 0`. Rewrite `h` using `[zero_mul]`. Rewrite using `[h]`. Establish `e : cjA (g.val).det (rd g) = !![g.val 0 0 / (g.val).det, g.val 0 1; g.val 1 0 / (g.val).det, g.val 1 1]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cjA, rd] <;> field_simp`. Rewrite using `[e]`. Simplify using `[GL2LocalData.piS, rWm]`.
-/
theorem piS_zero (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (g : GL (Fin 2) F) (Φ : F × F → ℂ) :
    piS χ c₁ g Φ 0 = ((c₁ (GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (GeneralLinearGroup.det g) (1 / 2) *
      rWS χ (rd g) Φ 0 := by
  have hd := det_ne g
  have h := dil χ (rd_det g) hd Φ 0
  rw [zero_mul] at h
  rw [h]
  have e : cjA (g.val).det (rd g) =
      !![g.val 0 0 / (g.val).det, g.val 0 1; g.val 1 0 / (g.val).det, g.val 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [cjA, rd] <;> field_simp
  rw [e]
  simp [GL2LocalData.piS, rWm]

/- English proof (translation)
Establish `hM : ((modulus z : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast modulus_ne_zero hz`. Distinguish the cases in `hc : m' 1 0 = 0`. Establish `hc0 : m 1 0 = 0` using `by rw [h0, hc, mul_zero]`. Rewrite using `[rWS_zero χ hm hc0, rWS_zero χ hm' hc]`. Rewrite `hm`, `hm'` using `[Matrix.det_fin_two]`.

Rewrite `hm` using `[hc0, mul_zero, sub_zero, h1]`. Rewrite `hm'` using `[hc, mul_zero, sub_zero]`. Establish `e : m' 0 0 = m 0 0 * z`. Establish `hne : m' 1 1 ≠ 0`. Introduce `h`.

Rewrite `hm'` using `[h, mul_zero]`. Conclude with `zero_ne_one hm'`. Apply `mul_right_cancel₀ hne` to reduce the goal to its premises. Rewrite using `[hm', ← hm]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hmod : modulus (m' 0 0) = modulus (m 0 0) * modulus z` using `by rw [e, modulus_mul]`. Simplify using `only [Prod.fst_zero, Prod.snd_zero, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]`. Rewrite using `[hmod]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `hc0 : m 1 0 ≠ 0` using `by rw [h0]; exact mul_ne_zero hz hc`. Rewrite using `[rWS_ne χ hc0, rWS_ne χ hc, h0, h1, modulus_mul]`. Establish `e : ∀ u : F × F, (m 0 0 * (((0 : F × F)).1 * ((0 : F × F)).2) + z * m' 1 1 * (u.1 * u.2) - (u.1 * ((0 : F × F)).2 + u.2 * ((0 : F × F)).1)) / (z * m' 1 0) = (m' 0 0 * (((0 : F × F)).1 * ((0 : F × F)).2) + m' 1 1 * (u.1 * u.2) - (u.1 * ((0 : F × F)).2 + u.2 * ((0 : F × F)).1)) / m …`. Introduce `u`. Simplify using `only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_add, add_zero, sub_zero]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [e]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem rWS_scale (χ : AddChar F Circle) {m m' : Matrix (Fin 2) (Fin 2) F} (hm : m.det = 1)
    (hm' : m'.det = 1) {z : F} (hz : z ≠ 0) (h0 : m 1 0 = z * m' 1 0) (h1 : m 1 1 = z * m' 1 1)
    (Φ : F × F → ℂ) :
    rWS χ m Φ 0 = (((modulus z : ℝ)⁻¹ : ℝ) : ℂ) * rWS χ m' Φ 0 := by
  have hM : ((modulus z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast modulus_ne_zero hz
  by_cases hc : m' 1 0 = 0
  · have hc0 : m 1 0 = 0 := by rw [h0, hc, mul_zero]
    rw [rWS_zero χ hm hc0, rWS_zero χ hm' hc]
    rw [Matrix.det_fin_two] at hm hm'
    rw [hc0, mul_zero, sub_zero, h1] at hm
    rw [hc, mul_zero, sub_zero] at hm'
    have e : m' 0 0 = m 0 0 * z := by
      have hne : m' 1 1 ≠ 0 := by
        intro h
        rw [h, mul_zero] at hm'
        exact zero_ne_one hm'
      apply mul_right_cancel₀ hne
      rw [hm', ← hm]
      ring
    have hmod : modulus (m' 0 0) = modulus (m 0 0) * modulus z := by rw [e, modulus_mul]
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, AddChar.map_zero_eq_one, Circle.coe_one, one_mul]
    rw [hmod]
    push_cast
    field_simp
  · have hc0 : m 1 0 ≠ 0 := by rw [h0]; exact mul_ne_zero hz hc
    rw [rWS_ne χ hc0, rWS_ne χ hc, h0, h1, modulus_mul]
    have e : ∀ u : F × F, (m 0 0 * (((0 : F × F)).1 * ((0 : F × F)).2) + z * m' 1 1 * (u.1 * u.2) -
        (u.1 * ((0 : F × F)).2 + u.2 * ((0 : F × F)).1)) / (z * m' 1 0) =
        (m' 0 0 * (((0 : F × F)).1 * ((0 : F × F)).2) + m' 1 1 * (u.1 * u.2) -
        (u.1 * ((0 : F × F)).2 + u.2 * ((0 : F × F)).1)) / m' 1 0 := by
      intro u
      simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_add, add_zero, sub_zero]
      field_simp
    simp only [e]
    push_cast
    field_simp

omit [MeasurableSpace F] [BorelSpace F] in
/- English proof (translation)
Establish `hp : (0 : ℝ) < (modulus (u : F) : ℝ)`. Use `modulus_ne_zero u.ne_zero` as an intermediate fact. Check the signs of the components of the expression. Rewrite using `[mp, Complex.norm_cpow_eq_rpow_re_of_pos hp]`. Evaluate the numerical expressions.
-/
theorem norm_mp (u : Fˣ) : ‖mp u (1 / 2)‖ = (modulus (u : F) : ℝ) ^ (1 / 2 : ℝ) := by
  have hp : (0 : ℝ) < (modulus (u : F) : ℝ) := by
    have := modulus_ne_zero u.ne_zero
    positivity
  rw [mp, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  norm_num

/- English proof (translation)
Use `set g : GL (Fin 2) F := uni2 x * dg2 a 1 * dg2 z z * k with hg`. Take `⟨d1, d2⟩` from `GlobalTheory.CompanionTheory.SphTheta.SplitPiK.det_integral hk`. Establish `d0` using `det_ne k`. Establish `hmk : modulus (k.val).det = 1` using `GlobalTheory.CompanionTheory.SphTheta.SplitPiK.modulus_of_unit d0 d1 d2`. Establish `hz0 : (z : F) ≠ 0` using `z.ne_zero`.

Establish `hr : ∀ j, g.val 1 j = (z : F) * k.val 1 j`. Introduce `j`. Simplify using `[hg, uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hD : (g.val).det = (a : F) * ((z : F) * (z : F)) * (k.val).det`. Establish `e1 : ((uni2 x : GL (Fin 2) F).val).det = 1` using `by simp [uni2, Matrix.det_fin_two]`.

Establish `e2 : ((dg2 a 1 : GL (Fin 2) F).val).det = (a : F)` using `by simp [dg2, Matrix.det_fin_two]`. Establish `e3 : ((dg2 z z : GL (Fin 2) F).val).det = (z : F) * (z : F)` using `by simp [dg2, Matrix.det_fin_two]`. Rewrite using `[hg, det_mul', det_mul', det_mul', e1, e2, e3, one_mul]`. Establish `hred : (!![k.val 0 0 / (k.val).det, k.val 0 1 / (k.val).det; k.val 1 0, k.val 1 1] : Matrix (Fin 2) (Fin 2) F) = rd k` using `rfl`. Rewrite using `[hred, piS_zero, rWS_scale χ (rd_det g) (rd_det k) hz0 (by simpa [rd] using hr 0) (by simpa [rd] using hr 1) Φ]`.

Establish `hval : ((GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det` using `Matrix.GeneralLinearGroup.val_det_apply g`. Establish `hmD : modulus ((GeneralLinearGroup.det g : Fˣ) : F) = modulus (a : F) * (modulus (z : F) * modulus (z : F))`. Rewrite using `[hval, hD, modulus_mul, modulus_mul, modulus_mul, hmk, mul_one]`. Establish `hzp : (0 : ℝ) < (modulus (z : F) : ℝ)`. Use `modulus_ne_zero hz0` as an intermediate fact.

Check the signs of the components of the expression. Rewrite using `[norm_mul, norm_mul, norm_mul, hc₁, one_mul, norm_mp, hmD]`. Use `push_cast`. Rewrite using `[Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), ← sq, ← Real.rpow_natCast, ← Real.rpow_mul hzp.le]`. Evaluate the numerical expressions.

Clear the denominators using the available nonvanishing facts.
-/
theorem norm_piS_iwasawa (χ : AddChar F Circle) (c₁ : Fˣ →* ℂˣ) (hc₁ : ∀ x, ‖((c₁ x : ℂˣ) : ℂ)‖ = 1)
    (Φ : F × F → ℂ) (x : F) (a z : Fˣ) {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    ‖piS χ c₁ (uni2 x * dg2 a 1 * dg2 z z * k) Φ 0‖ = (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) *
      ‖rWS χ !![k.val 0 0 / (k.val).det, k.val 0 1 / (k.val).det; k.val 1 0, k.val 1 1] Φ 0‖ := by
  set g : GL (Fin 2) F := uni2 x * dg2 a 1 * dg2 z z * k with hg
  obtain ⟨d1, d2⟩ := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.det_integral hk
  have d0 := det_ne k
  have hmk : modulus (k.val).det = 1 := GlobalTheory.CompanionTheory.SphTheta.SplitPiK.modulus_of_unit d0 d1 d2
  have hz0 : (z : F) ≠ 0 := z.ne_zero
  have hr : ∀ j, g.val 1 j = (z : F) * k.val 1 j := by
    intro j
    simp [hg, uni2, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hD : (g.val).det = (a : F) * ((z : F) * (z : F)) * (k.val).det := by
    have e1 : ((uni2 x : GL (Fin 2) F).val).det = 1 := by simp [uni2, Matrix.det_fin_two]
    have e2 : ((dg2 a 1 : GL (Fin 2) F).val).det = (a : F) := by simp [dg2, Matrix.det_fin_two]
    have e3 : ((dg2 z z : GL (Fin 2) F).val).det = (z : F) * (z : F) := by simp [dg2, Matrix.det_fin_two]
    rw [hg, det_mul', det_mul', det_mul', e1, e2, e3, one_mul]
  have hred : (!![k.val 0 0 / (k.val).det, k.val 0 1 / (k.val).det; k.val 1 0, k.val 1 1] :
      Matrix (Fin 2) (Fin 2) F) = rd k := rfl
  rw [hred, piS_zero, rWS_scale χ (rd_det g) (rd_det k) hz0 (by simpa [rd] using hr 0)
    (by simpa [rd] using hr 1) Φ]
  have hval : ((GeneralLinearGroup.det g : Fˣ) : F) = (g.val).det :=
    Matrix.GeneralLinearGroup.val_det_apply g
  have hmD : modulus ((GeneralLinearGroup.det g : Fˣ) : F) =
      modulus (a : F) * (modulus (z : F) * modulus (z : F)) := by
    rw [hval, hD, modulus_mul, modulus_mul, modulus_mul, hmk, mul_one]
  have hzp : (0 : ℝ) < (modulus (z : F) : ℝ) := by
    have := modulus_ne_zero hz0
    positivity
  rw [norm_mul, norm_mul, norm_mul, hc₁, one_mul, norm_mp, hmD]
  push_cast
  rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), ← sq,
    ← Real.rpow_natCast, ← Real.rpow_mul hzp.le]
  norm_num
  field_simp

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ _ _ c₁ hc Φ _ x a z k hk`. Conclude with `(norm_piS_iwasawa χ c₁ hc Φ x a z hk).le`.
-/
theorem main : ForES fun F _ _ _ _ _ _ _ χ => ∀ c₁ : Fˣ →* ℂˣ, (∀ x, ‖((c₁ x : ℂˣ) : ℂ)‖ = 1) → ∀ Φ ∈ SBE (F × F), ∀ (x : F) (a z : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2,
  ‖piS χ c₁ (uni2 x * dg2 a 1 * dg2 z z * k) Φ 0‖ ≤ (modulus (a : F) : ℝ) ^ (1 / 2 : ℝ) *
    ‖rWS χ !![k.val 0 0 / (k.val).det, k.val 0 1 / (k.val).det; k.val 1 0, k.val 1 1] Φ 0‖ := by
  intro F _ _ _ _ _ _ _ χ _ _ c₁ hc Φ _ x a z k hk
  exact (norm_piS_iwasawa χ c₁ hc Φ x a z hk).le

end GlobalTheory.CompanionTheory.SplitPi.Iwasawa
