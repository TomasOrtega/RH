import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashIntMatrixPosDetProperties
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

/- English proof (translation)
Take `⟨r, hr⟩` from `hγ`. Move the coercions through the operations in `at hr`. Use `set p := γ 0 0`. Use `set q := γ 0 1`. Use `set s := γ 1 1`.

Establish `hdet' : p * s - (N * l * r) * q = 1`. Rewrite `hdet` using `[Matrix.det_fin_two]`. Rewrite `hdet` using `[hr]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s, -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s; N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s), -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ? …` and prove the remaining obligations.

Establish `hγe : γ = !![p, q; N * l * r, s]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]`. Rewrite using `[hγe]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.

Take the linear combination `-(N * a * p + b * N * l * r) * h`. Take the linear combination `-(N * a * q + b * s) * h`. Take the linear combination `-(N * l * c * p + N * d * N * l * r) * h`. Take the linear combination `-(N * l * c * q + N * d * s) * h`. Rewrite using `[Matrix.det_fin_two_of]`.

Take the linear combination `((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]`. Use `push_cast`. Conclude with `Dvd.intro _ rfl`. Simplify using `only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]`.

Conclude with `⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩`.
-/
theorem atkinLehner_conj_int (N l : ℕ) (a b c d : ℤ) (h : (N : ℤ) * a * d - l * b * c = 1) (γ : M2)
    (hγ : ((N * l : ℕ) : ℤ) ∣ γ 1 0) (hdet : γ.det = 1) :
    ∃ γ' : M2, !![(N : ℤ) * a, b; N * l * c, N * d] * γ = γ' * !![(N : ℤ) * a, b; N * l * c, N * d] ∧
    γ'.det = 1 ∧ ((N * l : ℕ) : ℤ) ∣ γ' 1 0 ∧ (N : ℤ) ∣ γ' 1 1 - γ 0 0 := by
  obtain ⟨r, hr⟩ := hγ
  push_cast at hr
  set p := γ 0 0
  set q := γ 0 1
  set s := γ 1 1
  have hdet' : p * s - (N * l * r) * q = 1 := by
    rw [Matrix.det_fin_two] at hdet; rw [hr] at hdet; linarith
  refine ⟨!![(N : ℤ) * a * d * p + N * l * b * d * r - N * l * a * c * q - l * b * c * s,
     -(a * b * p) - l * b * b * r + N * a * a * q + a * b * s;
     N * l * (c * d * p + N * d * d * r - l * c * c * q - c * d * s),
     -(l * b * c * p) - N * l * b * d * r + N * l * a * c * q + N * a * d * s], ?_, ?_, ?_, ?_⟩
  · have hγe : γ = !![p, q; N * l * r, s] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [p, q, s, hr]
    rw [hγe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination -(N * a * p + b * N * l * r) * h
    · linear_combination -(N * a * q + b * s) * h
    · linear_combination -(N * l * c * p + N * d * N * l * r) * h
    · linear_combination -(N * l * c * q + N * d * s) * h
  · rw [Matrix.det_fin_two_of]
    linear_combination ((N : ℤ) * a * d - l * b * c) ^ 2 * hdet' + ((N : ℤ) * a * d - l * b * c + 1) * h
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    push_cast
    exact Dvd.intro _ rfl
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
      Matrix.cons_val_fin_one]
    exact ⟨-(b * d * l * r) + l * a * c * q + a * d * s - a * d * p, by linear_combination p * h⟩

/- English proof (translation)
Introduce `k N l χ f a b c d h hk hN hf`. Use `set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ`. Establish `hQdet : 0 < Q.det`. Establish `: Q.det = N * (N * a * d - l * b * c)` using `by rw [hQ, Matrix.det_fin_two_of]; ring`. Rewrite using `[this, h, mul_one]`.

Conclude with `hN` after adjusting the coercions. Establish `hiff` using `(slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)`. Establish `hiff0` using `(slz_props k f hk).2.2.1 (N * l) (ch χ)`. Use `hiff.2 fun γ hγ => ?_` and prove the remaining obligations. Establish `hγdet : (γ : M2).det = 1` using `Matrix.SpecialLinearGroup.det_coe γ`.

Establish `hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0` using `by exact_mod_cast hγ`. Take `⟨g, hg, hgdet, hgdvd, hgcong⟩` from `atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet`. Set `γ₁ : SL(2, ℤ)` to `⟨g, hgdet⟩`. Establish `hf1` using `hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)`. Establish `hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f)`.

Rewrite using `[← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg, slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]`. Rewrite using `[hcalc, hf1]`. Establish `hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1)`. Simplify using `only [ch]`. Establish `e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N)` using `(ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by`.

Establish `: (N : ℤ) ∣ g 1 1 - γ 0 0` using `hgcong`. Rewrite using `[← dvd_neg, neg_sub]`. Conclude with `this)`. Establish `e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1`. Establish `hd` using `hγdet`.

Rewrite `hd` using `[Matrix.det_fin_two]`. Take `⟨r, hr⟩` from `hγ'`. Establish `: ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1`. Rewrite using `[hd]`. Simplify using the standard rewrite rules.

Rewrite `this` using `[hr]`. Move the coercions through the operations in `at this`. Simplify using `using this`. Rewrite using `[e1, MulChar.inv_apply_eq_inv']`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations.

Rewrite using `[← map_mul, e2, map_one]`. Use function extensionality and compare the values at `τ`. Simplify using `only [slz]`. Rewrite using `[hchar]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inv_slz_atkinLehner : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ),
    N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f →
    Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  intro k N l χ f a b c d h hk hN hf
  set Q : M2 := !![(N : ℤ) * a, b; N * l * c, N * d] with hQ
  have hQdet : 0 < Q.det := by
    have : Q.det = N * (N * a * d - l * b * c) := by rw [hQ, Matrix.det_fin_two_of]; ring
    rw [this, h, mul_one]; exact_mod_cast hN
  have hiff := (slz_props k (slz k Q f) hk).2.2.1 (N * l) (ch χ⁻¹)
  have hiff0 := (slz_props k f hk).2.2.1 (N * l) (ch χ)
  refine hiff.2 fun γ hγ => ?_
  have hγdet : (γ : M2).det = 1 := Matrix.SpecialLinearGroup.det_coe γ
  have hγ' : ((N * l : ℕ) : ℤ) ∣ (γ : M2) 1 0 := by exact_mod_cast hγ
  obtain ⟨g, hg, hgdet, hgdvd, hgcong⟩ := atkinLehner_conj_int N l a b c d h (γ : M2) hγ' hγdet
  let γ₁ : SL(2, ℤ) := ⟨g, hgdet⟩
  have hf1 := hiff0.1 hf γ₁ (by exact_mod_cast hgdvd)
  have hcalc : slz k (γ : M2) (slz k Q f) = slz k Q (slz k (γ₁ : M2) f) := by
    rw [← slz_mul k f Q (γ : M2) hQdet (by rw [hγdet]; exact one_pos), hg,
      slz_mul k f g Q (by rw [hgdet]; exact one_pos) hQdet]
  rw [hcalc, hf1]
  have hchar : ch χ (γ₁ 1 1) = ch χ⁻¹ (γ 1 1) := by
    simp only [ch]
    have e1 : ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ 0 0 : ℤ) : ZMod N) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 (by
        have : (N : ℤ) ∣ g 1 1 - γ 0 0 := hgcong
        rw [← dvd_neg, neg_sub]; exact this)
    have e2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have hd := hγdet
      rw [Matrix.det_fin_two] at hd
      obtain ⟨r, hr⟩ := hγ'
      have : ((((γ : M2) 0 0 * (γ : M2) 1 1 - (γ : M2) 0 1 * (γ : M2) 1 0 : ℤ)) : ZMod N) = 1 := by
        rw [hd]; simp
      rw [hr] at this
      push_cast at this
      simpa using this
    rw [e1, MulChar.inv_apply_eq_inv']
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, e2, map_one]
  funext τ
  simp only [slz]
  rw [hchar]
  ring

end GlobalTheory.EisM
