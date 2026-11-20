import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.IdealLattice

open scoped MatrixGroups UpperHalfPlane

/- English proof (translation)
Introduce `z hz`. Take `⟨o, ho⟩` from `(GlobalTheory.MomDict.inOK_iff D ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2)).1 ⟨0, 1, by simp [GlobalTheory.MomOne.wK]⟩`. Take `⟨a, ha, rfl⟩` from `(GlobalTheory.CurveLattice.mem_lamOf D c x z).1 hz`. Use `(GlobalTheory.CurveLattice.mem_lamOf D c x _).2 ⟨o * a, c.mul_mem_left o ha, ?_⟩` and prove the remaining obligations. Rewrite using `[ho]`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wK_mul_mem (D : D7) (c : Ideal (𝓞 D.host.K)) (x : ℂ) :
    ∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x := by
  intro z hz
  obtain ⟨o, ho⟩ := (GlobalTheory.MomDict.inOK_iff D ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2)).1
    ⟨0, 1, by simp [GlobalTheory.MomOne.wK]⟩
  obtain ⟨a, ha, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D c x z).1 hz
  refine (GlobalTheory.CurveLattice.mem_lamOf D c x _).2 ⟨o * a, c.mul_mem_left o ha, ?_⟩
  rw [ho]; simp; ring

/- English proof (translation)
Take `⟨g, hg⟩` from `ModularGroup.exists_smul_mem_fd τ₀`. Use `set A : ℤ := g 0 0 with hA`. Use `set B : ℤ := g 0 1 with hB`. Use `set C : ℤ := g 1 0 with hC`. Use `set E : ℤ := g 1 1 with hE`.

Establish `hdet : A * E - B * C = 1`. Use `g.2` as an intermediate fact. Rewrite `this` using `[Matrix.det_fin_two]`. Conclude with `this`. Establish `hdetC : (A : ℂ) * E - B * C = 1` using `by exact_mod_cast hdet`.

Establish `hco : ((g • τ₀ : ℍ) : ℂ) = (A * τ₀ + B) / (C * τ₀ + E)`. Rewrite using `[UpperHalfPlane.coe_specialLinearGroup_apply]`. Simplify using `[A, B, C, E]`. Establish `hden : (C * (τ₀ : ℂ) + E) ≠ 0`. Introduce `h0`.

Use `(g • τ₀).im_pos` as an intermediate fact. Rewrite `this` using `[← UpperHalfPlane.coe_im, hco, h0, div_zero]`. Simplify using `at this`. Use `⟨b * (C * τ₀ + E), g • τ₀, mul_ne_zero hb hden, hg, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[h, hco]`.

Establish `key : ∀ m n : ℂ, (C * (τ₀ : ℂ) + E) * (m + n * ((A * τ₀ + B) / (C * τ₀ + E))) = m * (C * τ₀ + E) + n * (A * τ₀ + B)` using `fun m n => by`. Clear the denominators using the available nonvanishing facts. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨M, N, rfl⟩`. Use `⟨N * A - M * B, M * E - N * C, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, key]`. Use `push_cast`. Take the linear combination `(-b * (M * (τ₀ : ℂ) + N)) * hdetC`. Introduce and unpack `⟨m, n, rfl⟩`. Use `⟨m * C + n * A, m * E + n * B, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_assoc, key]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_reduced {Λ : AddSubgroup ℂ} {b : ℂ} {τ₀ : ℍ} (hb : b ≠ 0)
    (h : ∀ z, z ∈ Λ ↔ ∃ m n : ℤ, b * (m * (τ₀ : ℂ) + n) = z) :
    ∃ ω₁ : ℂ, ∃ τ : ℍ, ω₁ ≠ 0 ∧ τ ∈ ModularGroup.fd ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice Λ ω₁ τ := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ₀
  set A : ℤ := g 0 0 with hA
  set B : ℤ := g 0 1 with hB
  set C : ℤ := g 1 0 with hC
  set E : ℤ := g 1 1 with hE
  have hdet : A * E - B * C = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hdetC : (A : ℂ) * E - B * C = 1 := by exact_mod_cast hdet
  have hco : ((g • τ₀ : ℍ) : ℂ) = (A * τ₀ + B) / (C * τ₀ + E) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp [A, B, C, E]
  have hden : (C * (τ₀ : ℂ) + E) ≠ 0 := by
    intro h0
    have := (g • τ₀).im_pos
    rw [← UpperHalfPlane.coe_im, hco, h0, div_zero] at this
    simp at this
  refine ⟨b * (C * τ₀ + E), g • τ₀, mul_ne_zero hb hden, hg, fun z => ?_⟩
  rw [h, hco]
  have key : ∀ m n : ℂ, (C * (τ₀ : ℂ) + E) * (m + n * ((A * τ₀ + B) / (C * τ₀ + E))) =
      m * (C * τ₀ + E) + n * (A * τ₀ + B) := fun m n => by
    field_simp
  constructor
  · rintro ⟨M, N, rfl⟩
    refine ⟨N * A - M * B, M * E - N * C, ?_⟩
    rw [mul_assoc, key]
    push_cast
    linear_combination (-b * (M * (τ₀ : ℂ) + N)) * hdetC
  · rintro ⟨m, n, rfl⟩
    refine ⟨m * C + n * A, m * E + n * B, ?_⟩
    rw [mul_assoc, key]
    push_cast
    ring

/- English proof (translation)
Introduce `D c hc x hx`. Establish `hst` using `wK_mul_mem D c x`. Use `⟨hst, ?_⟩` and prove the remaining obligations. Take `⟨a, τ₀, ha, -, hlat⟩` from `GlobalTheory.CurveLattice.exists_tau D c hc`. Take `⟨ω₁, τ, hω, hfd, hper⟩` from `exists_reduced (Λ := lamOf D c x) (b := x * a) (τ₀ := τ₀) (mul_ne_zero hx ha) (hlat x)`.

Establish `him : 0 < (τ : ℂ).im` using `τ.im_pos`. Establish `him' : 0 < τ.im` using `τ.im_pos`. Establish `hci : (τ : ℂ).im = τ.im` using `rfl`. Use `⟨ω₁, τ, hω, him, hper, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `hfd.1`.

Establish `h2` using `hfd.2`. Rewrite `h1` using `[Complex.normSq_apply]`. Establish `hre : ((τ : ℂ).re) ^ 2 ≤ 1 / 4`. Use `abs_le.1 h2` as an intermediate fact. Simplify using `only [UpperHalfPlane.re] at this`.

Use polynomial arithmetic with `[this.1, this.2]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hmem : ω₁ ∈ lamOf D c x` using `(hper ω₁).2 ⟨1, 0, by simp⟩`. Take `⟨m, n, hmn⟩` from `(hper _).1 (hst ω₁ hmem)`. Establish `hw : (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = (m : ℂ) + n * τ`.

Use `hmn` as an intermediate fact. Rewrite `this` using `[mul_comm]`. Conclude with `mul_left_cancel₀ hω (by rw [← this])`. Establish `him2` using `congrArg Complex.im hw`. Simplify using `at him2`.

Establish `hd : 0 < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Establish `hn : (0 : ℝ) < n`. Assume the negation of the conclusion as `hn`. Establish `hn' : (n : ℝ) ≤ 0` using `le_of_not_gt hn`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hn1 : (1 : ℝ) ≤ n`. Establish `: (0 : ℤ) < n` using `by exact_mod_cast hn`. Conclude with `this` after adjusting the coercions. Rewrite using `[hci]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem main : ∀ (D : D7) (c : Ideal (𝓞 D.host.K)), c ≠ ⊥ → ∀ x : ℂ, x ≠ 0 →
    (∀ z ∈ lamOf D c x, ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * z ∈ lamOf D c x) ∧
    ∃ ω₁ τ : ℂ, ω₁ ≠ 0 ∧ 0 < τ.im ∧ JacobiThetaHalfCharacteristic.IsPeriodLattice (lamOf D c x) ω₁ τ ∧
      1 / 2 ≤ τ.im ∧ 2 * τ.im ≤ Real.sqrt D.host.d := by
  intro D c hc x hx
  have hst := wK_mul_mem D c x
  refine ⟨hst, ?_⟩
  obtain ⟨a, τ₀, ha, -, hlat⟩ := GlobalTheory.CurveLattice.exists_tau D c hc
  obtain ⟨ω₁, τ, hω, hfd, hper⟩ := exists_reduced (Λ := lamOf D c x) (b := x * a) (τ₀ := τ₀)
    (mul_ne_zero hx ha) (hlat x)
  have him : 0 < (τ : ℂ).im := τ.im_pos
  have him' : 0 < τ.im := τ.im_pos
  have hci : (τ : ℂ).im = τ.im := rfl
  refine ⟨ω₁, τ, hω, him, hper, ?_, ?_⟩
  · have h1 := hfd.1
    have h2 := hfd.2
    rw [Complex.normSq_apply] at h1
    have hre : ((τ : ℂ).re) ^ 2 ≤ 1 / 4 := by
      have := abs_le.1 h2
      simp only [UpperHalfPlane.re] at this
      nlinarith [this.1, this.2]
    nlinarith
  · have hmem : ω₁ ∈ lamOf D c x := (hper ω₁).2 ⟨1, 0, by simp⟩
    obtain ⟨m, n, hmn⟩ := (hper _).1 (hst ω₁ hmem)
    have hw : (1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2 = (m : ℂ) + n * τ := by
      have := hmn
      rw [mul_comm] at this
      exact mul_left_cancel₀ hω (by rw [← this])
    have him2 := congrArg Complex.im hw
    simp at him2
    have hd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
    have hn : (0 : ℝ) < n := by
      by_contra hn
      have hn' : (n : ℝ) ≤ 0 := le_of_not_gt hn
      nlinarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0 : ℤ) < n := by exact_mod_cast hn
      exact_mod_cast this
    rw [hci]
    nlinarith

end GlobalTheory.IdealLattice
