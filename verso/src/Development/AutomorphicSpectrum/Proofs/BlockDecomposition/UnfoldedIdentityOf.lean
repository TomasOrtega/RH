import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

noncomputable section

open UpperHalfPlane hiding I
open MeasureTheory Complex CongruenceSubgroup Filter Topology
open scoped MatrixGroups ModularForm Modular ComplexConjugate Real
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

/- English proof (translation)
Establish `h1` using `hf.exp ((1 : ℝ) +ᵥ z)`. Establish `h2` using `hf.exp z`. Use `h1.unique ?_` and prove the remaining obligations. Use `h2 using 2 with n` and compare the differences between its conclusion and the goal. Use `congr 1`.

Establish `: (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = 1 + (z : ℂ)` using `by simp`. Rewrite using `[this, mul_add, mul_one, Complex.exp_add]`. Establish `: Complex.exp (2 * Real.pi * Complex.I * n) = 1`. Use `Complex.exp_nat_mul_two_pi_mul_I n` as an intermediate fact. Rewrite using `[← this]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, one_mul]`.
-/
theorem form_vadd {k N : ℕ} {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} {a : ℕ → ℂ}
    (hf : IsForm k N χ f a) (z : ℍ) : f ((1 : ℝ) +ᵥ z) = f z := by
  have h1 := hf.exp ((1 : ℝ) +ᵥ z)
  have h2 := hf.exp z
  refine h1.unique ?_
  convert h2 using 2 with n
  congr 1
  have : (((1 : ℝ) +ᵥ z : ℍ) : ℂ) = 1 + (z : ℂ) := by simp
  rw [this, mul_add, mul_one, Complex.exp_add]
  have : Complex.exp (2 * Real.pi * Complex.I * n) = 1 := by
    have := Complex.exp_nat_mul_two_pi_mul_I n
    rw [← this]; congr 1; ring
  rw [this, one_mul]

/- English proof (translation)
Take `⟨g, hg⟩` from `p.2.2.exists_SL2_row 1`. Use `⟨g, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hg.1`. Simplify using `using hg.2`.
-/
theorem exists_row (L : ℕ) (p : Idx L) : ∃ g : SL(2, ℤ), g 1 0 = L * p.1.2 ∧ g 1 1 = p.1.1 := by
  obtain ⟨g, hg⟩ := p.2.2.exists_SL2_row 1
  refine ⟨g, ?_, ?_⟩
  · simpa using hg.1
  · simpa using hg.2

/- English proof (translation)
Introduce `h5 h1 h2 hB k N M ν _ _ hM h4 hk χ f a hf c hν hpar β hβ s hs`. Use `set ψ : DirichletCharacter ℂ M := c * DirichletCharacter.changeLevel hM χ⁻¹ with hψ`. Establish `hM0 : 0 < M` using `Nat.pos_of_ne_zero (NeZero.ne M)`. Establish `hM4 : 4 ≤ M` using `Nat.le_of_dvd hM0 h4`. Use `haveI : Fact (1 < M) := ⟨by omega⟩`.

Establish `hL : 2 ≤ 4 * M ^ 2` using `by nlinarith`. Use `choose γ hγ using exists_row (4 * M ^ 2)`. Establish `hth` using `hB (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν hν (by simpa using MulChar.map_nonunit ψ⁻¹ not_isUnit_zero) (fun n => DirichletCharacter.norm_le_one _ _)`. Take `⟨hcont, hper, -, -⟩` from `hth`. Establish `hfc : Continuous (f : ℍ → ℂ)` using `f.holo'.continuous`.

Establish `hmeas : Measurable (FF f ψ k ν s)`. Unfold `FF`. Use `((hfc.measurable).mul ?_).mul ?_` and prove the remaining obligations. Conclude with `(Complex.continuous_conj.comp hcont).measurable`. Conclude with `(Complex.measurable_ofReal.comp (UpperHalfPlane.continuous_im.measurable)).pow_const _`.

Establish `hinv : ∀ z, FF f ψ k ν s ((1 : ℝ) +ᵥ z) = FF f ψ k ν s z`. Introduce `z`. Unfold `FF`. Rewrite using `[form_vadd hf z, hper z]`. Simplify using the standard rewrite rules.

Take `⟨hint, hval⟩` from `h2 k N M ν (by omega) hk χ f a hf ψ hν hpar s hs`. Establish `hU` using `h1 (4 * M ^ 2) hL β hβ γ (fun p => hγ p) (FF f ψ k ν s) hmeas hinv hint`. Rewrite using `[← hval, hU]`. Use `integral_congr_ae (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `show (β z : ℂ) * _ = (β z : ℂ) * _`.

Use `congr 1`. Unfold `Ep`. Rewrite using `[← tsum_mul_left]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Use `h5 k N M ν p.1.1 hM χ f a hf c p.1.2 (γ p) z s p.2.1 hν (by rw [(hγ p).1]; push_cast; ring) (hγ p).2` as an intermediate fact.

Conclude with `this.symm`.
-/
theorem unfolded_identity_of : T5 → U1 → U2 → B2 → S1 := by
  intro h5 h1 h2 hB k N M ν _ _ hM h4 hk χ f a hf c hν hpar β hβ s hs
  set ψ : DirichletCharacter ℂ M := c * DirichletCharacter.changeLevel hM χ⁻¹ with hψ
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM4 : 4 ≤ M := Nat.le_of_dvd hM0 h4
  haveI : Fact (1 < M) := ⟨by omega⟩
  have hL : 2 ≤ 4 * M ^ 2 := by nlinarith
  choose γ hγ using exists_row (4 * M ^ 2)
  have hth := hB (fun n : ℤ => ψ⁻¹ (n : ZMod M)) ν hν
    (by simpa using MulChar.map_nonunit ψ⁻¹ not_isUnit_zero) (fun n => DirichletCharacter.norm_le_one _ _)
  obtain ⟨hcont, hper, -, -⟩ := hth
  have hfc : Continuous (f : ℍ → ℂ) := f.holo'.continuous
  have hmeas : Measurable (FF f ψ k ν s) := by
    unfold FF
    refine ((hfc.measurable).mul ?_).mul ?_
    · exact (Complex.continuous_conj.comp hcont).measurable
    · exact (Complex.measurable_ofReal.comp (UpperHalfPlane.continuous_im.measurable)).pow_const _
  have hinv : ∀ z, FF f ψ k ν s ((1 : ℝ) +ᵥ z) = FF f ψ k ν s z := by
    intro z
    unfold FF
    rw [form_vadd hf z, hper z]
    simp
  obtain ⟨hint, hval⟩ := h2 k N M ν (by omega) hk χ f a hf ψ hν hpar s hs
  have hU := h1 (4 * M ^ 2) hL β hβ γ (fun p => hγ p) (FF f ψ k ν s) hmeas hinv hint
  rw [← hval, hU]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show (β z : ℂ) * _ = (β z : ℂ) * _
  congr 1
  unfold Ep
  rw [← tsum_mul_left]
  refine tsum_congr fun p => ?_
  have := h5 k N M ν p.1.1 hM χ f a hf c p.1.2 (γ p) z s p.2.1 hν
    (by rw [(hγ p).1]; push_cast; ring) (hγ p).2
  exact this.symm

end GlobalTheory.CompanionTheory.HalfWeight
