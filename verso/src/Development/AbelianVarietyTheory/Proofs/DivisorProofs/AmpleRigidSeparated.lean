import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrderSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassPullbackVeryAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleRigid

open GlobalTheory.CechPic GlobalTheory.EffBound

/- English proof (translation)
Establish `h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0` using `GlobalTheory.ThetaExtend.pic_local (R := K) _`. Rewrite using `[Hom.one_def, Over.comp_left, pull_comp, h, map_zero]`.
-/
theorem pull_one_left_eq_zero {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (c : Pic A.left) :
    pull (1 : A ⟶ A).left c = 0 := by
  have h : pull (η[A] : 𝟙_ (Over (Sp K)) ⟶ A).left c = 0 := GlobalTheory.ThetaExtend.pic_local (R := K) _
  rw [Hom.one_def, Over.comp_left, pull_comp, h, map_zero]

/- English proof (translation)
Rewrite using `[Nat.choose_succ_succ', Nat.choose_one_right]`.
-/
theorem choose_two_succ (n : ℕ) : (n + 1).choose 2 = n + n.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

/- English proof (translation)
Establish `hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c = 2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c`. Introduce `n`. Establish `h` using `hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹`. Establish `e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1)` using `mul_inv_cancel_right _ _`. Establish `e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2)` using `(pow_succ _ _).symm`.

Establish `e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n` using `by rw [pow_succ, mul_inv_cancel_right]`. Establish `e4 : ψ * ψ⁻¹ = 1` using `mul_inv_cancel _`. Rewrite `h` using `[e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero]`. Rewrite using `[two_nsmul]`. Conclude with `h.symm`.

Establish `key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c = (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_zero, pull_one_left_eq_zero]`. Simplify using the standard rewrite rules. Rewrite using `[pow_one]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Establish `h` using `eq_sub_of_add_eq (hrec n)`. Rewrite using `[show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]`. Rewrite using `[show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1), choose_two_succ n]`. Use `push_cast`.

Use `module`. Conclude with `(key n).1`.
-/
theorem pull_pow_left (hcube : CubeSt) {K : Type} [Field K] [IsAlgClosed K] {A : Over (Sp K)} [GrpObj A]
    [IsCommMonObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : Out.RelAmple A L)
    (c : Pic A.left) (ψ : A ⟶ A) (n : ℕ) :
    pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c := by
  have hrec : ∀ n : ℕ, pull (ψ ^ (n + 2)).left c + pull (ψ ^ n).left c =
      2 • pull (ψ ^ (n + 1)).left c + pull ψ.left c + pull ψ⁻¹.left c := by
    intro n
    have h := hcube K A hA L hL hamp c (ψ ^ (n + 1)) ψ ψ⁻¹
    have e1 : ψ ^ (n + 1) * ψ * ψ⁻¹ = ψ ^ (n + 1) := mul_inv_cancel_right _ _
    have e2 : ψ ^ (n + 1) * ψ = ψ ^ (n + 2) := (pow_succ _ _).symm
    have e3 : ψ ^ (n + 1) * ψ⁻¹ = ψ ^ n := by rw [pow_succ, mul_inv_cancel_right]
    have e4 : ψ * ψ⁻¹ = 1 := mul_inv_cancel _
    rw [e1, e2, e3, e4, pull_one_left_eq_zero, add_zero, add_zero] at h
    rw [two_nsmul]
    exact h.symm
  have key : ∀ n : ℕ, (pull (ψ ^ n).left c = (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c +
      ((n.choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) ∧ (pull (ψ ^ (n + 1)).left c =
      (((n + 1 + 1).choose 2 : ℕ) : ℤ) • pull ψ.left c + (((n + 1).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left c) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [pow_zero, pull_one_left_eq_zero]; simp
      · rw [pow_one]; simp
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := eq_sub_of_add_eq (hrec n)
      rw [show n + 1 + 1 = n + 2 from rfl, h, ih.1, ih.2]
      rw [show n + 2 + 1 = n + 1 + 1 + 1 from rfl, choose_two_succ (n + 1 + 1), choose_two_succ (n + 1),
        choose_two_succ n]
      push_cast
      module
  exact (key n).1

/- English proof (translation)
Introduce `hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu`. Use `haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA`. Take `⟨d, hd, n0, s, hs⟩` from `(GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp`. Establish `heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL))`. Introduce `φ`.

Rewrite using `[← cls_pw hL (d : ℤ)]`. Conclude with `eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance`. Establish `heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL))`. Introduce `φ j hj`. Proceed by induction on `j, hj using Nat.le_induction with`.

Consider the case `base => simpa using heff φ`. Consider the case `succ j hj ih`. Use `push_cast`. Rewrite using `[add_zsmul, one_zsmul]`. Conclude with `eff_add _ _ ih (heff φ)`.

Take `⟨t₀, ht₀⟩` from `hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))`. Establish `hN : t₀ + 2 < Q ^ (t₀ + 2)` using `Nat.lt_pow_self (by omega)`. Take `⟨ψ, hψ, rfl⟩` from `hu (t₀ + 2)`. Establish `hpow` using `pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))`. Establish `hψ1 : ψ = 1`.

Use `ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_` and prove the remaining obligations. Establish `h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2`. Rewrite using `[choose_two_succ]`. Use linear arithmetic over natural numbers and integers. Establish `h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2` using `Nat.le_mul_of_pos_left _ hd`.

Use linear arithmetic over natural numbers and integers. Establish `hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2` using `Nat.choose_pos (by omega)`. Establish `e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) - (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) = (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL)`. Rewrite using `[hpow, map_zsmul, ← natCast_zsmul]`. Use `push_cast`.

Use `module`. Rewrite using `[e]`. Conclude with `heffn _ _ hb`. Rewrite using `[hψ1, one_pow]`.
-/
theorem separatedSt_of_const_cube : ConstSt → CubeSt → SeparatedSt := by
  intro hconst hcube K _ _ A _ _ hA L hL hamp Q hQ u hu
  haveI := GlobalTheory.isIntegral_of_isAbelianScheme_field K A hA
  obtain ⟨d, hd, n0, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy K A L hL).1 hamp
  have heff : ∀ φ : A.left ⟶ A.left, Eff (pull φ ((d : ℤ) • cls L hL)) := by
    intro φ
    rw [← cls_pw hL (d : ℤ)]
    exact eff_pull_of_veryAmpleBy K A.hom _ n0 s _ hs φ inferInstance
  have heffn : ∀ (φ : A.left ⟶ A.left) (j : ℕ), 1 ≤ j → Eff ((j : ℤ) • pull φ ((d : ℤ) • cls L hL)) := by
    intro φ j hj
    induction j, hj using Nat.le_induction with
    | base => simpa using heff φ
    | succ j hj ih =>
      push_cast
      rw [add_zsmul, one_zsmul]
      exact eff_add _ _ ih (heff φ)
  obtain ⟨t₀, ht₀⟩ := hconst K A hA L hL hamp ((d : ℤ) • pull u.left (cls L hL))
  have hN : t₀ + 2 < Q ^ (t₀ + 2) := Nat.lt_pow_self (by omega)
  obtain ⟨ψ, hψ, rfl⟩ := hu (t₀ + 2)
  have hpow := pull_pow_left hcube hA L hL hamp (cls L hL) ψ (Q ^ (t₀ + 2))
  have hψ1 : ψ = 1 := by
    refine ht₀ (d * (Q ^ (t₀ + 2) + 1).choose 2) ?_ ψ hψ ?_
    · have h1 : Q ^ (t₀ + 2) ≤ (Q ^ (t₀ + 2) + 1).choose 2 := by
        rw [choose_two_succ]; omega
      have h2 : (Q ^ (t₀ + 2) + 1).choose 2 ≤ d * (Q ^ (t₀ + 2) + 1).choose 2 :=
        Nat.le_mul_of_pos_left _ hd
      omega
    · have hb : 1 ≤ (Q ^ (t₀ + 2)).choose 2 := Nat.choose_pos (by omega)
      have e : (d : ℤ) • pull (ψ ^ (Q ^ (t₀ + 2))).left (cls L hL) -
          (d * (Q ^ (t₀ + 2) + 1).choose 2) • pull ψ.left (cls L hL) =
          (((Q ^ (t₀ + 2)).choose 2 : ℕ) : ℤ) • pull ψ⁻¹.left ((d : ℤ) • cls L hL) := by
        rw [hpow, map_zsmul, ← natCast_zsmul]
        push_cast
        module
      rw [e]
      exact heffn _ _ hb
  rw [hψ1, one_pow]

end GlobalTheory.AmpleRigid
