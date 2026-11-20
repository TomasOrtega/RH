import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk

section Scale

variable {k r : ℕ} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]

/- English proof (translation)
Unfold `rconv`. Repeatedly rewrite using `[smul_comm (e _) cc]`. Conclude with `integral_smul cc _`.
-/
lemma rconv_smul (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) : rconv μ e (fun g => cc • A g) x = cc • rconv μ e A x := by
  unfold rconv
  simp_rw [smul_comm (e _) cc]
  exact integral_smul cc _

/- English proof (translation)
Repeatedly rewrite using `[smul_comm (e _) cc]`. Conclude with `h.smul cc`.
-/
lemma integrable_smul_fun (μ : Measure (Formalism.QuantumDeterminants.Mt k r)) (e : Mat k r → ℂ) (A : Mat k r → Vp) (cc : ℂ)
    (x : Mat k r) (h : Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • A (x * Matrix.of g)) μ) :
    Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => e (Matrix.of g) • (fun y => cc • A y) (x * Matrix.of g)) μ := by
  simp_rw [smul_comm (e _) cc]
  exact h.smul cc

/- English proof (translation)
Unfold `l2SG`. Rewrite using `[← lintegral_const_mul' _ _ (by simp)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[nnnorm_smul, ENNReal.coe_mul, mul_pow]`.
-/
lemma l2SG_const_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) :
    l2SG ν (fun g => cc • A g) = (‖cc‖₊ : ℝ≥0∞) ^ 2 * l2SG ν A := by
  unfold l2SG
  rw [← lintegral_const_mul' _ _ (by simp)]
  congr 1
  funext x
  rw [nnnorm_smul, ENNReal.coe_mul, mul_pow]

/- English proof (translation)
Establish `hW : Wf ν A = fun g => (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) • A g`. Use function extensionality and compare the values at `g`. Unfold `Wf`. Use `congr 1`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[hW, l2SG_const_smul]`. Use `set t := (l2SG ν A).toReal with ht_def`. Establish `ht : 0 < t` using `ENNReal.toReal_pos h0 h1.ne`. Establish `hA : l2SG ν A = ENNReal.ofReal t` using `(ENNReal.ofReal_toReal h1.ne).symm`.

Establish `hn : (‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal t⁻¹`. Rewrite using `[ENNReal.ofReal, ← ENNReal.coe_pow]`. Use `congr 1`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]`.

Rewrite using `[hn, hA, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]`.
-/
lemma l2SG_Wf_eq_one (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (h0 : l2SG ν A ≠ 0)
    (h1 : l2SG ν A < ⊤) : l2SG ν (Wf ν A) = 1 := by
  have hW : Wf ν A = fun g => (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) • A g := by
    funext g; unfold Wf; congr 1; push_cast; rfl
  rw [hW, l2SG_const_smul]
  set t := (l2SG ν A).toReal with ht_def
  have ht : 0 < t := ENNReal.toReal_pos h0 h1.ne
  have hA : l2SG ν A = ENNReal.ofReal t := (ENNReal.ofReal_toReal h1.ne).symm
  have hn : (‖(((Real.sqrt t)⁻¹ : ℝ) : ℂ)‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal t⁻¹ := by
    rw [ENNReal.ofReal, ← ENNReal.coe_pow]
    congr 1
    apply NNReal.coe_injective
    rw [NNReal.coe_pow, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr ht.le), Complex.norm_real,
      Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt ht.le]
  rw [hn, hA, ← ENNReal.ofReal_mul (inv_nonneg.mpr ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one]

/- English proof (translation)
Repeatedly rewrite using `[enorm_smul, mul_assoc]`. Rewrite using `[lintegral_const_mul' _ _ enorm_ne_top]`. Conclude with `ENNReal.mul_lt_top enorm_lt_top h`.
-/
lemma lint_smul (ν : Measure (Formalism.QuantumDeterminants.Mt k r)) (A : Mat k r → Vp) (cc : ℂ) (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
    (h : ∫⁻ x, ‖A (Matrix.of x)‖ₑ * f x ∂ν < ⊤) :
    ∫⁻ x, ‖(fun g => cc • A g) (Matrix.of x)‖ₑ * f x ∂ν < ⊤ := by
  simp_rw [enorm_smul, mul_assoc]
  rw [lintegral_const_mul' _ _ enorm_ne_top]
  exact ENNReal.mul_lt_top enorm_lt_top h

end Scale

def WlocShape : Prop :=
  BesselNVGap → CoefWeightedLoc → ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (u : Fin k → ℝ)
    (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ), RealPlaceNumericalSetting k r z c u v b →
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)),
    IsDSHpk k r (eps48 k r) (lam48 k r v b) σ →
  ∀ (Vp : Type) [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp]
    (π : Mat k r → (Vp →L[ℂ] Vp)), IsHCTypeW k r z u π →
  ∀ w : H, IsLowUnitH k r (eps48 k r) (lam48 k r v b) σ w →
  ∀ μG μS ν : MeasureTheory.Measure (Formalism.QuantumDeterminants.Mt k r),
    IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG → IsHaarOn (Formalism.QuantumDeterminants.Sset k r z) μS →
    IsQuotMeas μG μS ν →
  ∃ W : Mat k r → Vp, (ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) ∧ IsSPsiEquiv z (psiGen k r z c) π W ∧
    (∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x) ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ ∂ν < ⊤ ∧ l2SG ν W = 1 ∧
    ∫⁻ x, ‖W (Matrix.of x)‖ₑ * ENNReal.ofReal (nuH k r z (Matrix.of x) ^ N1H k r) ∂ν < ⊤ ∧
    ∃ (α : Mat k r → ℂ) (Ω : Set (Mat k r)) (a : ℝ), IsCompact Ω ∧ (1 : Mat k r) ∈ Ω ∧
      Ω ⊆ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
      Measurable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g)) ∧ (∀ y, α y ≠ 0 → y ∈ Ω) ∧ (∀ y, ‖α y‖ ≤ a) ∧
      ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
        MeasureTheory.Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of g) • W (x * Matrix.of g)) μG ∧
        rconv μG α W x = W x) ∧
  ∃ (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (cc : ℂ) (x₀ : Mat k r) (ξ : Vp),
    IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    x₀ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) ∧
    ∀ x, W x = cc • B0 z c σ π μW μN (σ x₀ w) ξ (σ x w)

/- English proof (translation)
Introduce `hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ`. Take `⟨μW, μN, hW, hN, hWf, hNc⟩` from `hWN k r z hS.2.2.1 hS.2.2.2.1`. Establish `hyp : Hyp k r z c u v b σ π w μG μS ν μW μN` using `⟨hS, hσ, hπ, hw, hG, hSμ, hQ, hW, hN, hWf, hNc⟩`. Take `⟨x₀, hx₀, ξ, hne⟩` from `hNz hBNV k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW`. Establish `hL'` using `hL k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ`.

Use `set A := Af z c σ π μW μN w x₀ ξ with hA_def`. Use `set cc : ℂ := (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) with hcc`. Establish `hW' : Wf ν A = fun g => cc • A g`. Use function extensionality and compare the values at `g`. Unfold `Wf`.

Use `congr 1`. Rewrite using `[hcc]`. Use `push_cast`. Both sides reduce to the same expression. Use `⟨Wf ν A, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, μW, μN, cc, x₀, ξ, hW, hN, hx₀, fun x => by rw [hW']; rfl⟩` and prove the remaining obligations.

Rewrite using `[hW']`. Conclude with `(hC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ).const_smul cc`. Introduce `h hh m hm g hg`. Rewrite using `[hW']`. Use `hEq k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg` as an intermediate fact.

Express the relevant statement in the definitionally equal form `cc • Af z c σ π μW μN w x₀ ξ (h * m * g) = psiGen k r z c m • (π h) (cc • Af z c σ π μW μN w x₀ ξ g)`. Rewrite using `[this, smul_comm cc (psiGen k r z c m), map_smul]`. Introduce `x hx`. Take `⟨hi, he⟩` from `hK k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ x hx`. Rewrite using `[hW']`.

Conclude with `⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩`. Rewrite using `[hW']`. Use `lint_smul ν A cc (fun _ => 1) (by simpa using hL'.1)` as an intermediate fact. Simplify using `using this`. Conclude with `l2SG_Wf_eq_one ν A hne hL'.2`.

Rewrite using `[hW']`. Conclude with `lint_smul ν A cc _ (hWt k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ)`. Take `⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, hα⟩` from `hRp k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ`. Use `⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨hi, he⟩` from `hα x hx`.

Rewrite using `[hW']`. Conclude with `⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩`.
-/
theorem scWlocShape_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocShape := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨μW, μN, hW, hN, hWf, hNc⟩ := hWN k r z hS.2.2.1 hS.2.2.2.1
  have hyp : Hyp k r z c u v b σ π w μG μS ν μW μN :=
    ⟨hS, hσ, hπ, hw, hG, hSμ, hQ, hW, hN, hWf, hNc⟩
  obtain ⟨x₀, hx₀, ξ, hne⟩ := hNz hBNV k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW
  have hL' := hL k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  set A := Af z c σ π μW μN w x₀ ξ with hA_def
  set cc : ℂ := (((Real.sqrt (l2SG ν A).toReal)⁻¹ : ℝ) : ℂ) with hcc
  have hW' : Wf ν A = fun g => cc • A g := by
    funext g; unfold Wf; congr 1; rw [hcc]; push_cast; rfl
  refine ⟨Wf ν A, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, μW, μN, cc, x₀, ξ, hW, hN, hx₀, fun x => by rw [hW']; rfl⟩
  · rw [hW']
    exact (hC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ).const_smul cc
  · intro h hh m hm g hg
    rw [hW']
    have := hEq k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ h hh m hm g hg
    change cc • Af z c σ π μW μN w x₀ ξ (h * m * g) =
      psiGen k r z c m • (π h) (cc • Af z c σ π μW μN w x₀ ξ g)
    rw [this, smul_comm cc (psiGen k r z c m), map_smul]
  · intro x hx
    obtain ⟨hi, he⟩ := hK k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩
  · rw [hW']
    have := lint_smul ν A cc (fun _ => 1) (by simpa using hL'.1)
    simpa using this
  · exact l2SG_Wf_eq_one ν A hne hL'.2
  · rw [hW']
    exact lint_smul ν A cc _ (hWt k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ)
  · obtain ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, hα⟩ :=
      hRp k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
    refine ⟨α, Ω, a, hΩ, h1, hΩG, hαm, hα0, hαa, fun x hx => ?_⟩
    obtain ⟨hi, he⟩ := hα x hx
    rw [hW']
    exact ⟨integrable_smul_fun μG _ A cc x hi, by rw [rconv_smul, he]⟩

/- English proof (translation)
Introduce `hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ`. Take `⟨W, hWc, _⟩` from `scWlocShape_of hWN hEq hC hK hRp hL hWt hNz hR hBNV hCW k r z c u v b hS H σ hσ Vp π hπ w hw μG μS ν hG hSμ hQ`. Conclude with `⟨W, hWc⟩`.
-/
theorem scWlocExists_of (hWN : HaarWN) (hEq : AEquiv) (hC : ACont) (hK : AKind) (hRp : AReprod)
    (hL : WavePacketL1L2) (hWt : AWeighted) (hNz : ANonzero) (hR : Formalism.L2.SG.HCReprodM.HCReprodDSm) :
    WlocExists := by
  intro hBNV hCW k r z c u v b hS H _ _ _ σ hσ Vp _ _ _ π hπ w hw μG μS ν hG hSμ hQ
  obtain ⟨W, hWc, _⟩ := scWlocShape_of hWN hEq hC hK hRp hL hWt hNz hR hBNV hCW k r z c u v b hS H σ hσ
    Vp π hπ w hw μG μS ν hG hSμ hQ
  exact ⟨W, hWc⟩

end WlocSk
