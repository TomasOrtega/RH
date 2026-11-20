import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleFramesIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnimodularOverlatticeRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSemicharactersNestedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfAppellHumbertThetaFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFourthPowerUnderIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineHomOfLiftTranslationFiniteIndexLatticesStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LefschetzAmple

/- English proof (translation)
Introduce `g A _ hA M u Hm χ hM hAH`. Establish `hint : ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (hermForm Hm l l').im = n`. Introduce `l hl l' hl'`. Establish `h1` using `GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l, hl⟩ ⟨l', hl'⟩`. Establish `h2` using `GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l', hl'⟩ ⟨l, hl⟩`.

Rewrite `h2` using `[add_comm]`. Establish `hsw` using `GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hAH.1 l l'`. Establish `him : (hermForm Hm l' l).im = -(hermForm Hm l l').im`. Rewrite using `[hsw, Complex.conj_im]`. Establish `hne : χ ⟨l, hl⟩ * χ ⟨l', hl'⟩ ≠ 0`.

Apply the tactic sequence `refine mul_ne_zero ?_ ?_ <;> refine norm_ne_zero_iff.1 ?_ <;> rw [hAH.2.2.1] <;> norm_num`. Establish `h3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l l').im) = Complex.exp (Real.pi * Complex.I * (hermForm Hm l' l).im)`. Use `mul_left_cancel₀ hne ?_` and prove the remaining obligations. Rewrite using `[← h1, h2]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h3` using `[him]`. Establish `h4 : Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm l l').im) = 1`. Establish `e : (2 * Real.pi * Complex.I * (hermForm Hm l l').im : ℂ) = Real.pi * Complex.I * (hermForm Hm l l').im - Real.pi * Complex.I * ((-(hermForm Hm l l').im : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[e, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h4`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Use `mul_right_cancel₀ hπ (by rw [← hn]; ring : ((hermForm Hm l l').im : ℂ) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I))` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Take `⟨Λ₁, Ef, N, hle, hd1, hf1, hEf, hbij, hN, hNΛ⟩` from `GlobalTheory.T.exists_unimodular_overlattice_riemannForm g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint`. Take `⟨P, uB, χB, hg, hΛB, hAHB, -, -⟩` from `GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij`. Establish `hle' : u.Λ ≤ uB.Λ` using `hΛB ▸ hle`. Establish `hNΛ' : ∀ x ∈ uB.Λ, N • x ∈ u.Λ` using `hΛB ▸ hNΛ`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_shift_semicharacters_nested_lattices g u.Λ uB.Λ Hm χ χB hle' u.discrete u.full hAH.1 hAH.2.1 hAH.2.2.1 hAHB.2.2.1 (GlobalTheory.LatticeHom.semicharacter_add u hM hAH) (GlobalTheory.LatticeHom.semicharacter_add uB P.isLB hAHB)`.

Take `⟨ψ, hψ, hψex, hcov⟩` from `GlobalTheory.T.theta_fourth_power_under_isogeny g A hA M u Hm χ hM hAH (fun θ => GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction g A hA M u Hm χ hM hAH 4 θ) P uB χB hle' a hg hAHB ha`. Establish `hψa : IsAffineHom ψ` using `GlobalTheory.T.isAffineHom_of_lift_translation_finiteIndex_lattices g A hA P.A P.isAb M P.L u uB a N hN hle' hNΛ' ψ hψ hψex`. Establish `: IsProper A.hom` using `hA.proper`. Conclude with `(GlobalTheory.FrameCompare.relAmple_iff A.hom hM).2 inferInstance fun x => by`. Take `⟨s, V, hx, hV, hs⟩` from `hcov x`.

Conclude with `⟨4, s, by norm_num, hx, hs ▸ hV.preimage ψ⟩`.
-/
theorem relAmple_of_isAH : ∀ (g : ℕ) (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A →
    ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ),
    M.IsLB → u.IsAH Hm χ → Out.RelAmple A M := by
  intro g A _ hA M u Hm χ hM hAH
  have hint : ∀ l ∈ u.Λ, ∀ l' ∈ u.Λ, ∃ n : ℤ, (hermForm Hm l l').im = n := by
    intro l hl l' hl'
    have h1 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l, hl⟩ ⟨l', hl'⟩
    have h2 := GlobalTheory.LatticeHom.semicharacter_add u hM hAH ⟨l', hl'⟩ ⟨l, hl⟩
    rw [add_comm] at h2
    have hsw := GlobalTheory.LatticeHom.hermForm_swap_of_isHermitian hAH.1 l l'
    have him : (hermForm Hm l' l).im = -(hermForm Hm l l').im := by
      rw [hsw, Complex.conj_im]
    have hne : χ ⟨l, hl⟩ * χ ⟨l', hl'⟩ ≠ 0 := by
      refine mul_ne_zero ?_ ?_ <;> refine norm_ne_zero_iff.1 ?_ <;> rw [hAH.2.2.1] <;> norm_num
    have h3 : Complex.exp (Real.pi * Complex.I * (hermForm Hm l l').im) =
        Complex.exp (Real.pi * Complex.I * (hermForm Hm l' l).im) := by
      refine mul_left_cancel₀ hne ?_
      rw [← h1, h2]
      ring
    rw [him] at h3
    have h4 : Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm l l').im) = 1 := by
      have e : (2 * Real.pi * Complex.I * (hermForm Hm l l').im : ℂ) =
          Real.pi * Complex.I * (hermForm Hm l l').im - Real.pi * Complex.I * ((-(hermForm Hm l l').im : ℝ) : ℂ) := by
        push_cast; ring
      rw [e, Complex.exp_sub, h3, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h4
    refine ⟨n, ?_⟩
    have hπ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := mul_right_cancel₀ hπ (by rw [← hn]; ring : ((hermForm Hm l l').im : ℂ) * (2 * Real.pi * Complex.I) = n * (2 * Real.pi * Complex.I))
    exact_mod_cast this
  obtain ⟨Λ₁, Ef, N, hle, hd1, hf1, hEf, hbij, hN, hNΛ⟩ := GlobalTheory.T.exists_unimodular_overlattice_riemannForm g u.Λ Hm u.discrete u.full hAH.1 hAH.2.1 hint
  obtain ⟨P, uB, χB, hg, hΛB, hAHB, -, -⟩ :=
    GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd1 hf1 hAH.1 hAH.2.1 hEf hbij
  have hle' : u.Λ ≤ uB.Λ := hΛB ▸ hle
  have hNΛ' : ∀ x ∈ uB.Λ, N • x ∈ u.Λ := hΛB ▸ hNΛ
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_shift_semicharacters_nested_lattices g u.Λ uB.Λ Hm χ χB hle' u.discrete u.full hAH.1 hAH.2.1 hAH.2.2.1 hAHB.2.2.1
    (GlobalTheory.LatticeHom.semicharacter_add u hM hAH) (GlobalTheory.LatticeHom.semicharacter_add uB P.isLB hAHB)
  obtain ⟨ψ, hψ, hψex, hcov⟩ := GlobalTheory.T.theta_fourth_power_under_isogeny g A hA M u Hm χ hM hAH (fun θ => GlobalTheory.T.exists_section_of_appellHumbert_thetaFunction g A hA M u Hm χ hM hAH 4 θ)
    P uB χB hle' a hg hAHB ha
  have hψa : IsAffineHom ψ := GlobalTheory.T.isAffineHom_of_lift_translation_finiteIndex_lattices g A hA P.A P.isAb M P.L u uB a N hN hle' hNΛ' ψ hψ hψex
  have : IsProper A.hom := hA.proper
  exact (GlobalTheory.FrameCompare.relAmple_iff A.hom hM).2 inferInstance fun x => by
    obtain ⟨s, V, hx, hV, hs⟩ := hcov x
    exact ⟨4, s, by norm_num, hx, hs ▸ hV.preimage ψ⟩

end GlobalTheory.LefschetzAmple
