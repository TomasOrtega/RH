import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusFundamentalDomainCoversStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicHolomorphicDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicPeriodicConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcEqualDifferencePluriharmonicStatement

open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory.MetricUniq

/- English proof (translation)
Introduce `g E _ _ _ B τ hτ j h₁ h₂ hm₁ hm₂ hdd h0 P hP`. Take `⟨b, z⟩` from `P`. Establish `hb : b ∈ B` using `hP.1`. Establish `hpos₁` using `hm₁.2.1`. Establish `hpos₂` using `hm₂.2.1`.

Establish `hmemc : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov B g` using `fun z => ⟨hb, Set.mem_univ _⟩`. Establish `hcd₁ : ContDiffOn ℝ ∞ (fun Q => Real.log (h₁ Q)) (cov B g)` using `hm₁.1.log fun Q hQ => (hpos₁ Q hQ).ne'`. Establish `hcd₂ : ContDiffOn ℝ ∞ (fun Q => Real.log (h₂ Q)) (cov B g)` using `hm₂.1.log fun Q hQ => (hpos₂ Q hQ).ne'`. Take `⟨hcf, hH⟩` from `GlobalTheory.T.ddc_equal_difference_pluriharmonic B hτ.1 b hb _ _ hcd₁ hcd₂ hdd`. Use `set f : (Fin g → ℂ) → ℝ := fun z => Real.log (h₁ (b, z)) - Real.log (h₂ (b, z)) with hf`.

Establish `hper : ∀ l ∈ stdLat g, ∀ z, f (z + per (τ b) l) = f z`. Introduce `l hl z`. Establish `e₁` using `hm₁.2.2 l hl (b, z) (hmemc z)`. Establish `e₂` using `hm₂.2.2 l hl (b, z) (hmemc z)`. Simplify using `only [transl] at e₁ e₂`.

Establish `hj : ‖j l (b, z)‖ ^ 2 ≠ 0`. Introduce `h0'`. Rewrite `e₁` using `[h0', mul_zero]`. Conclude with `(hpos₁ _ (hmemc z)).ne' e₁.symm`. Establish `p₁` using `hpos₁ _ (hmemc (z + per (τ b) l))`.

Establish `p₂` using `hpos₂ _ (hmemc (z + per (τ b) l))`. Simplify using `only [hf]`. Rewrite using `[← e₁, ← e₂, Real.log_mul p₁.ne' hj, Real.log_mul p₂.ne' hj]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : ((τ b).map Complex.im).det ≠ 0` using `(hτ.2.2 b hb).2.det_pos.ne'`.

Establish `hcont : Continuous (per (τ b))`. Unfold `per`. Use `fun_prop`. Establish `key` using `GlobalTheory.T.pluriharmonic_periodic_constant f (per (τ b) '' Set.Icc 0 1) (per (τ b) '' (stdLat g : Set (Fl g))) (hcf.of_le (by simp)) (GlobalTheory.T.pluriharmonic_holomorphic_derivative f hcf hH) (isCompact_Icc.image hcont) (by rintro _ ⟨l, hl, rfl⟩ z; exact hper l hl z) (by`. Introduce `z`.

Take `⟨x, hx, l, hl, rfl⟩` from `GlobalTheory.T.torus_fundamental_domain_covers (τ b) hdet z`. Conclude with `⟨_, ⟨x, hx, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩)`. Establish `h00 : f 0 = 0`. Use `h0 b hb` as an intermediate fact. Simplify using `only [zeroSec] at this`.

Simplify using `only [hf, this, sub_self]`. Establish `hz` using `key z`. Rewrite `hz` using `[h00]`. Establish `hl : Real.log (h₁ (b, z)) = Real.log (h₂ (b, z))`. Simplify using `only [hf] at hz`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Real.log_injOn_pos (Set.mem_Ioi.2 (hpos₁ _ (hmemc z))) (Set.mem_Ioi.2 (hpos₂ _ (hmemc z))) hl`.
-/
theorem metric_eq_of_ddc_eq : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (j : Fl g → Pt E g → ℂ) (h₁ h₂ : Pt E g → ℝ), IsMetric B τ (stdLat g) j h₁ → IsMetric B τ (stdLat g) j h₂ → (∀ P ∈ cov B g, ∀ v w : Pt E g, ddc (fun Q => Real.log (h₁ Q)) P v w = ddc (fun Q => Real.log (h₂ Q)) P v w) → (∀ b ∈ B, h₁ (zeroSec g b) = h₂ (zeroSec g b)) → Set.EqOn h₁ h₂ (cov B g) := by
  intro g E _ _ _ B τ hτ j h₁ h₂ hm₁ hm₂ hdd h0 P hP
  obtain ⟨b, z⟩ := P
  have hb : b ∈ B := hP.1
  have hpos₁ := hm₁.2.1
  have hpos₂ := hm₂.2.1
  have hmemc : ∀ z : Fin g → ℂ, ((b, z) : Pt E g) ∈ cov B g := fun z => ⟨hb, Set.mem_univ _⟩
  have hcd₁ : ContDiffOn ℝ ∞ (fun Q => Real.log (h₁ Q)) (cov B g) :=
    hm₁.1.log fun Q hQ => (hpos₁ Q hQ).ne'
  have hcd₂ : ContDiffOn ℝ ∞ (fun Q => Real.log (h₂ Q)) (cov B g) :=
    hm₂.1.log fun Q hQ => (hpos₂ Q hQ).ne'
  obtain ⟨hcf, hH⟩ := GlobalTheory.T.ddc_equal_difference_pluriharmonic B hτ.1 b hb _ _ hcd₁ hcd₂ hdd
  set f : (Fin g → ℂ) → ℝ := fun z => Real.log (h₁ (b, z)) - Real.log (h₂ (b, z)) with hf
  have hper : ∀ l ∈ stdLat g, ∀ z, f (z + per (τ b) l) = f z := by
    intro l hl z
    have e₁ := hm₁.2.2 l hl (b, z) (hmemc z)
    have e₂ := hm₂.2.2 l hl (b, z) (hmemc z)
    simp only [transl] at e₁ e₂
    have hj : ‖j l (b, z)‖ ^ 2 ≠ 0 := by
      intro h0'
      rw [h0', mul_zero] at e₁
      exact (hpos₁ _ (hmemc z)).ne' e₁.symm
    have p₁ := hpos₁ _ (hmemc (z + per (τ b) l))
    have p₂ := hpos₂ _ (hmemc (z + per (τ b) l))
    simp only [hf]
    rw [← e₁, ← e₂, Real.log_mul p₁.ne' hj, Real.log_mul p₂.ne' hj]
    ring
  have hdet : ((τ b).map Complex.im).det ≠ 0 := (hτ.2.2 b hb).2.det_pos.ne'
  have hcont : Continuous (per (τ b)) := by
    unfold per
    fun_prop
  have key := GlobalTheory.T.pluriharmonic_periodic_constant f (per (τ b) '' Set.Icc 0 1) (per (τ b) '' (stdLat g : Set (Fl g)))
    (hcf.of_le (by simp)) (GlobalTheory.T.pluriharmonic_holomorphic_derivative f hcf hH) (isCompact_Icc.image hcont)
    (by rintro _ ⟨l, hl, rfl⟩ z; exact hper l hl z)
    (by
      intro z
      obtain ⟨x, hx, l, hl, rfl⟩ := GlobalTheory.T.torus_fundamental_domain_covers (τ b) hdet z
      exact ⟨_, ⟨x, hx, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩)
  have h00 : f 0 = 0 := by
    have := h0 b hb
    simp only [zeroSec] at this
    simp only [hf, this, sub_self]
  have hz := key z
  rw [h00] at hz
  have hl : Real.log (h₁ (b, z)) = Real.log (h₂ (b, z)) := by
    simp only [hf] at hz
    linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.2 (hpos₁ _ (hmemc z))) (Set.mem_Ioi.2 (hpos₂ _ (hmemc z))) hl

end GlobalTheory.MetricUniq
