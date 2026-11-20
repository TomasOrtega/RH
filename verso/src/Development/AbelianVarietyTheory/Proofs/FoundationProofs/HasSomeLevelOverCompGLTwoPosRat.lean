import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllQConjOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatHermiteNormalFormMobiusStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatConjPrincipalCongruenceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionAllCoeffsDeltaPowAffineSubstStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

/- English proof (translation)
Introduce `γ hγ`. Rewrite `hγ`, the goal using `[CongruenceSubgroup.Gamma_mem]`. Take `⟨h1, h2, h3, h4⟩` from `hγ`. Establish `c` using `fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) => congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using c _ _ h1`. Simplify using `using c _ _ h2`. Simplify using `using c _ _ h3`. Simplify using `using c _ _ h4`.
-/
theorem gamma_mul_le (m k : ℕ) : CongruenceSubgroup.Gamma (m * k) ≤ CongruenceSubgroup.Gamma m := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have c := fun (x : ℤ) (y : ZMod (m * k)) (e : (x : ZMod (m * k)) = y) =>
    congrArg (ZMod.castHom (dvd_mul_right m k) (ZMod m)) e
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ _ h1
  · simpa using c _ _ h2
  · simpa using c _ _ h3
  · simpa using c _ _ h4

/- English proof (translation)
Introduce `E g f hE ⟨N, w, hN, hinv, hexp⟩`. Take `⟨n₁, hn₁, hH⟩` from `GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g`. Take `⟨n₂, hn₂, hC⟩` from `GlobalTheory.T.glTwoPosRat_conj_principal_congruence g`. Take `⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩` from `GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties`. Take `⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩` from `GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob`.

Use `⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩` and prove the remaining obligations. Introduce `δ hδ τ`. Establish `hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂)`. Establish `: N * n₁ * n₂ = N * n₂ * n₁` using `by ring`. Rewrite `hδ` using `[this]`.

Conclude with `gamma_mul_le _ _ hδ`. Take `⟨δ', hδ'm, hgδ⟩` from `hC N δ hδ'`. Establish `e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ)`. Rewrite using `[cmp_mul, cmp_sl]`. Establish `e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f`.

Rewrite using `[cmp_mul, cmp_sl]`. Use `congr 1`. Use function extensionality and compare the values at `σ`. Conclude with `hinv δ' hδ'm σ`. Use `congrFun (e1.symm.trans (hgδ ▸ e2)) τ` as an intermediate fact.

Conclude with `this`. Introduce `γ₀`. Take `⟨γ, a, d, b, had, hmob⟩` from `hH γ₀`. Establish `ha : 0 < a` using `Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)`. Establish `hd : 0 < d` using `Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)`.

Establish `key` using `GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)`. Rewrite `key` using `[had]`. Establish `hlift` using `QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _) (p := (· ∈ E)) (Subring.zero_mem E) key`. Use `hlift using 2 with τ` and compare the differences between its conclusion and the goal. Use `congr 1`.

Establish `hz : (((a : ℂ) * τ + b) / d).im > 0`. Establish `: (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ)` using `by push_cast; field_simp`. Rewrite using `[this]`. Simplify using `only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]`. Establish `: (0 : ℝ) < (a : ℝ) / d` using `by positivity`.

Use `τ.im_pos` as an intermediate fact. Simplify using `only [UpperHalfPlane.coe_im]`. Check the signs of the components of the expression. Use `show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)`. Establish `hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d`.

Rewrite using `[UpperHalfPlane.ofComplex_apply_of_im_pos hz]`. Establish `hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) = ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ)`. Rewrite using `[← mob_sl, hzc]`. Simplify using `only [up]`. Rewrite using `[hmob τ, hm, UpperHalfPlane.ofComplex_apply]`.
-/
theorem inR_cmp : ∀ (E : Subring ℂ) (g : GQ) (f : ℍ → ℂ), (∀ x : ℚ, Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ∈ E) →
    InR E f → InR E (GlobalTheory.FN.cmp g f) := by
  intro E g f hE ⟨N, w, hN, hinv, hexp⟩
  obtain ⟨n₁, hn₁, hH⟩ := GlobalTheory.T.glTwoPosRat_hermite_normal_form_mobius g
  obtain ⟨n₂, hn₂, hC⟩ := GlobalTheory.T.glTwoPosRat_conj_principal_congruence g
  obtain ⟨mob_hs, mob_mul, mob_one, mob_sl, mob_diff, mob_up⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  obtain ⟨cmp_one, cmp_mul, cmp_sl, cmp_up⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨N * n₁ * n₂, w * n₁, by positivity, ?_, ?_⟩
  · intro δ hδ τ
    have hδ' : δ ∈ CongruenceSubgroup.Gamma (N * n₂) := by
      have : N * n₁ * n₂ = N * n₂ * n₁ := by ring
      rw [this] at hδ
      exact gamma_mul_le _ _ hδ
    obtain ⟨δ', hδ'm, hgδ⟩ := hC N δ hδ'
    have e1 : GlobalTheory.FN.cmp (g * ofSL δ) f = fun τ => GlobalTheory.FN.cmp g f (δ • τ) := by
      rw [cmp_mul, cmp_sl]
    have e2 : GlobalTheory.FN.cmp (ofSL δ' * g) f = GlobalTheory.FN.cmp g f := by
      rw [cmp_mul, cmp_sl]
      congr 1
      funext σ
      exact hinv δ' hδ'm σ
    have := congrFun (e1.symm.trans (hgδ ▸ e2)) τ
    exact this
  · intro γ₀
    obtain ⟨γ, a, d, b, had, hmob⟩ := hH γ₀
    have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have hd : 0 < d := Nat.pos_of_ne_zero (by rintro rfl; simp at had; omega)
    have key := GlobalTheory.T.qExpansionAllCoeffs_deltaPow_affineSubst E N w a d b (fun τ => f (γ • τ)) hE hN ha hd (hexp γ)
    rw [had] at key
    have hlift := QAll.of_dvd (N := N * n₁) (N' := N * n₁ * n₂) (by positivity) (dvd_mul_right _ _)
      (p := (· ∈ E)) (Subring.zero_mem E) key
    convert hlift using 2 with τ
    congr 1
    have hz : (((a : ℂ) * τ + b) / d).im > 0 := by
      have : (((a : ℂ) * τ + b) / d) = ((a : ℝ) / d : ℝ) * (τ : ℂ) + ((b : ℝ) / d : ℝ) := by
        push_cast; field_simp
      rw [this]
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      have : (0 : ℝ) < (a : ℝ) / d := by positivity
      have := τ.im_pos
      simp only [UpperHalfPlane.coe_im]
      positivity
    show up f (mob g ((γ₀ • τ : ℍ) : ℂ)) = up (fun τ => f (γ • τ)) (((a : ℂ) * τ + b) / d)
    have hzc : ((UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) = ((a : ℂ) * τ + b) / d := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    have hm : mob (ofSL γ) (((a : ℂ) * τ + b) / d) =
        ((γ • UpperHalfPlane.ofComplex (((a : ℂ) * τ + b) / d) : ℍ) : ℂ) := by
      rw [← mob_sl, hzc]
    simp only [up]
    rw [hmob τ, hm, UpperHalfPlane.ofComplex_apply]

end GlobalTheory.FN
