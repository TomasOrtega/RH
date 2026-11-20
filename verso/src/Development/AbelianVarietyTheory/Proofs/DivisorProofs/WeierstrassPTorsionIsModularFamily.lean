import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneityOfIsTauOfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTauOfUpperHalfPlaneLatticeSmulSL2Z

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice]`. Simplify using `[_root_.GlobalTheory.QFam.tauPair]`.
-/
private lemma mem_tauPair_lattice_iff (τ : ℍ) (z : ℂ) :
    z ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice ↔ ∃ m n : ℤ, (m : ℂ) * τ + n = z := by
  rw [PeriodPair.mem_lattice]
  simp [_root_.GlobalTheory.QFam.tauPair]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Simplify using `[UpperHalfPlane.denom]`.
-/
private lemma modularGroup_denom_eq (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ =
      ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Rewrite using `[← modularGroup_denom_eq]`. Conclude with `UpperHalfPlane.denom_ne_zero _ τ`.
-/
private lemma modularGroup_denom_ne_zero (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
  rw [← modularGroup_denom_eq]
  exact UpperHalfPlane.denom_ne_zero _ τ

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply]`. Simplify using the standard rewrite rules.
-/
private lemma coe_modularGroup_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    ((γ • τ : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Establish `hv0 : _root_.GlobalTheory.WpFam.vact N x γ 0 = x 0 * ((γ 0 0 : ℤ) : ZMod N) + x 1 * ((γ 1 0 : ℤ) : ZMod N)`. Simplify using `[_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Establish `hv1 : _root_.GlobalTheory.WpFam.vact N x γ 1 = x 0 * ((γ 0 1 : ℤ) : ZMod N) + x 1 * ((γ 1 1 : ℤ) : ZMod N)`. Simplify using `[_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul, dotProduct, Fin.sum_univ_two]`. Use `set y := _root_.GlobalTheory.WpFam.vact N x γ`.

Establish `h0 : (N : ℤ) ∣ ((y 0).val : ℤ) - ((x 0).val * γ 0 0 + (x 1).val * γ 1 0)`. Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Simplify using `[hv0]`. Establish `h1 : (N : ℤ) ∣ ((y 1).val : ℤ) - ((x 0).val * γ 0 1 + (x 1).val * γ 1 1)`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Use `push_cast`. Simplify using `[hv1]`. Take `⟨k, hk⟩` from `h0`. Take `⟨k', hk'⟩` from `h1`.

Use `⟨(k : ℂ) * τ + k', (mem_tauPair_lattice_iff τ _).2 ⟨k, k', rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hN : (N : ℂ) ≠ 0` using `by exact_mod_cast NeZero.ne N`. Establish `hD` using `modularGroup_denom_ne_zero γ τ`. Establish `e0` using `congrArg (fun t : ℤ => (t : ℂ)) hk`. Establish `e1` using `congrArg (fun t : ℤ => (t : ℂ)) hk'`.

Move the coercions through the operations in `at e0 e1`. Establish `hw : (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ)`. Rewrite using `[coe_modularGroup_smul, mul_div_assoc', mul_div_cancel_left₀ _ hD]`. Unfold `_root_.GlobalTheory.WpFam.tors`. Rewrite using `[mul_div_assoc', div_add' _ _ _ hN, div_left_inj' hN]`.

Take the linear combination `(τ : ℂ) * e0 + e1 - ((x 0).val : ℂ) * hw`.
-/
private lemma exists_tors_vact_eq_denom_mul_tors_smul_add (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N)
    (γ : SL(2, ℤ)) (τ : ℍ) :
    ∃ l ∈ (_root_.GlobalTheory.QFam.tauPair τ).lattice,
      _root_.GlobalTheory.WpFam.tors N τ (_root_.GlobalTheory.WpFam.vact N x γ) =
        (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l := by
  have hv0 : _root_.GlobalTheory.WpFam.vact N x γ 0 =
      x 0 * ((γ 0 0 : ℤ) : ZMod N) + x 1 * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  have hv1 : _root_.GlobalTheory.WpFam.vact N x γ 1 =
      x 0 * ((γ 0 1 : ℤ) : ZMod N) + x 1 * ((γ 1 1 : ℤ) : ZMod N) := by
    simp [_root_.GlobalTheory.WpFam.vact, _root_.GlobalTheory.WpFam.vmul, _root_.GlobalTheory.WpFam.redGL, Matrix.vecMul,
      dotProduct, Fin.sum_univ_two]
  set y := _root_.GlobalTheory.WpFam.vact N x γ
  have h0 : (N : ℤ) ∣ ((y 0).val : ℤ) - ((x 0).val * γ 0 0 + (x 1).val * γ 1 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv0]
  have h1 : (N : ℤ) ∣ ((y 1).val : ℤ) - ((x 0).val * γ 0 1 + (x 1).val * γ 1 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    simp [hv1]
  obtain ⟨k, hk⟩ := h0
  obtain ⟨k', hk'⟩ := h1
  refine ⟨(k : ℂ) * τ + k', (mem_tauPair_lattice_iff τ _).2 ⟨k, k', rfl⟩, ?_⟩
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hD := modularGroup_denom_ne_zero γ τ
  have e0 := congrArg (fun t : ℤ => (t : ℂ)) hk
  have e1 := congrArg (fun t : ℤ => (t : ℂ)) hk'
  push_cast at e0 e1
  have hw : (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((γ • τ : ℍ) : ℂ) =
      ((γ 0 0 : ℤ) : ℂ) * τ + ((γ 0 1 : ℤ) : ℂ) := by
    rw [coe_modularGroup_smul, mul_div_assoc', mul_div_cancel_left₀ _ hD]
  unfold _root_.GlobalTheory.WpFam.tors
  rw [mul_div_assoc', div_add' _ _ _ hN, div_left_inj' hN]
  linear_combination (τ : ℂ) * e0 + e1 - ((x 0).val : ℂ) * hw

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
/- English proof (translation)
Establish `hD` using `modularGroup_denom_ne_zero γ τ`. Establish `hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1`. Establish `h` using `γ.det_coe`. Rewrite `h` using `[Matrix.det_fin_two]`. Then use the resulting hypothesis. Establish `key : ∀ u v : ℤ, (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * ((u : ℂ) * ((γ • τ : ℍ) : ℂ) + v) = ((u * γ 0 0 + v * γ 1 0 : ℤ) : ℂ) * τ + ((u * γ 0 1 + v * γ 1 1 : ℤ) : ℂ)`.

Introduce `u v`. Rewrite using `[coe_modularGroup_smul]`. Clear the denominators using the available nonvanishing facts. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `_root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf`. Use `⟨hD, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_tauPair_lattice_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, rfl⟩`.

Use `⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩` and prove the remaining obligations. Establish `h1 : (m * γ 1 1 - n * γ 1 0) * γ 0 0 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 0 = m`. Take the linear combination `m * hdet`. Establish `h2 : (m * γ 1 1 - n * γ 1 0) * γ 0 1 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 1 = n`. Take the linear combination `n * hdet`.

Rewrite using `[key, h1, h2]`. Introduce and unpack `⟨u, v, rfl⟩`. Conclude with `⟨_, _, (key u v).symm⟩`.
-/
private lemma isTauOf_tauPair_denom_smul (γ : SL(2, ℤ)) (τ : ℍ) :
    _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf (_root_.GlobalTheory.QFam.tauPair τ) (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ))
      (γ • τ) := by
  have hD := modularGroup_denom_ne_zero γ τ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have key : ∀ u v : ℤ, (((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) *
      ((u : ℂ) * ((γ • τ : ℍ) : ℂ) + v) =
      ((u * γ 0 0 + v * γ 1 0 : ℤ) : ℂ) * τ + ((u * γ 0 1 + v * γ 1 1 : ℤ) : ℂ) := by
    intro u v
    rw [coe_modularGroup_smul]
    field_simp
    push_cast
    ring
  unfold _root_.ReciprocityTheory.ChartRestriction.L1.IsTauOf
  refine ⟨hD, fun z => ?_⟩
  rw [mem_tauPair_lattice_iff]
  constructor
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * γ 1 1 - n * γ 1 0, -(m * γ 0 1) + n * γ 0 0, ?_⟩
    have h1 : (m * γ 1 1 - n * γ 1 0) * γ 0 0 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 0 = m := by
      linear_combination m * hdet
    have h2 : (m * γ 1 1 - n * γ 1 0) * γ 0 1 + (-(m * γ 0 1) + n * γ 0 0) * γ 1 1 = n := by
      linear_combination n * hdet
    rw [key, h1, h2]
  · rintro ⟨u, v, rfl⟩
    exact ⟨_, _, (key u v).symm⟩

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in

/- English proof (translation)
Introduce `N _`. Prove the components needed by the constructor for the conclusion. Introduce `x γ`. Use function extensionality and compare the values at `τ`. Take `⟨l, hl, hP⟩` from `exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ`.

Establish `hom` using `_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)`. Establish `hper : (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) = (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tor …` using `(_root_.GlobalTheory.QFam.tauPair τ).weierstrassP_add_coe _ ⟨l, hl⟩`. Rewrite using `[ModularForm.SL_slash_apply, modularGroup_denom_eq]`. Unfold `_root_.GlobalTheory.WpFam.wp`. Rewrite using `[hP, hper, hom.2.1, zpow_neg, zpow_ofNat]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x γ`. Use function extensionality and compare the values at `τ`. Take `⟨l, hl, hP⟩` from `exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ`. Establish `hom` using `_root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)`.

Establish `hper : (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) = (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory …` using `(_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP_add_coe _ ⟨l, hl⟩`. Rewrite using `[ModularForm.SL_slash_apply, modularGroup_denom_eq]`. Unfold `_root_.GlobalTheory.WpFam.wpd`. Rewrite using `[hP, hper, hom.2.2.1, zpow_neg, zpow_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.WpFam.isFam_wp_wpd : ∀ (N : ℕ) [NeZero N],
    _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 2
        (_root_.GlobalTheory.WpFam.wp N) ∧
      _root_.GlobalTheory.QFam.IsFam (_root_.GlobalTheory.WpFam.vact N) 3
        (_root_.GlobalTheory.WpFam.wpd N) := by
  intro N _
  constructor
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wp
    rw [hP, hper, hom.2.1, zpow_neg, zpow_ofNat]
    ring
  · intro x γ
    funext τ
    obtain ⟨l, hl, hP⟩ := exists_tors_vact_eq_denom_mul_tors_smul_add N x γ τ
    have hom := _root_.GlobalTheory.WpFam.homogeneity_of_isTauOf _ _ _ (isTauOf_tauPair_denom_smul γ τ)
    have hper : (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x + l) =
        (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP
        ((((γ 1 0 : ℤ) : ℂ) * τ + ((γ 1 1 : ℤ) : ℂ)) * _root_.GlobalTheory.WpFam.tors N (γ • τ) x) :=
      (_root_.GlobalTheory.QFam.tauPair τ).derivWeierstrassP_add_coe _ ⟨l, hl⟩
    rw [ModularForm.SL_slash_apply, modularGroup_denom_eq]
    unfold _root_.GlobalTheory.WpFam.wpd
    rw [hP, hper, hom.2.2.1, zpow_neg, zpow_ofNat]
    ring

end GlobalTheory.WpFam
