import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2 GodementSectionLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhitLin

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `hc : Continuous fun x : Fin 2 → F => x ᵥ* (g : Matrix (Fin 2) (Fin 2) F)` using `Continuous.matrix_vecMul continuous_id continuous_const`. Establish `hc' : Continuous fun x : Fin 2 → F => x ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)` using `Continuous.matrix_vecMul continuous_id continuous_const`. Establish `hemb : Topology.IsClosedEmbedding fun x : Fin 2 → F => x ᵥ* (g : Matrix (Fin 2) (Fin 2) F)` using `Function.LeftInverse.isClosedEmbedding (f := fun x : Fin 2 → F => x ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) (fun x => by show (x ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = x`. Rewrite using `[Matrix.vecMul_vecMul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]`. Use the proof step `simp) hc' hc`.

Conclude with `⟨hφ.1.comp_continuous hc, hφ.2.comp_isClosedEmbedding hemb⟩`.
-/
theorem rt_mem {φ : (Fin 2 → F) → ℂ} (hφ : φ ∈ schwartzBruhat2 F) (g : GL (Fin 2) F) :
    rt φ g ∈ schwartzBruhat2 F := by
  have hc : Continuous fun x : Fin 2 → F => x ᵥ* (g : Matrix (Fin 2) (Fin 2) F) :=
    Continuous.matrix_vecMul continuous_id continuous_const
  have hc' : Continuous fun x : Fin 2 → F => x ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) :=
    Continuous.matrix_vecMul continuous_id continuous_const
  have hemb : Topology.IsClosedEmbedding fun x : Fin 2 → F => x ᵥ* (g : Matrix (Fin 2) (Fin 2) F) :=
    Function.LeftInverse.isClosedEmbedding
      (f := fun x : Fin 2 → F => x ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
      (fun x => by
        show (x ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) ᵥ* ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = x
        rw [Matrix.vecMul_vecMul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel]
        simp) hc' hc
  exact ⟨hφ.1.comp_continuous hc, hφ.2.comp_isClosedEmbedding hemb⟩

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Rewrite using `[mem_valBall_iff_le_ord h0]`. Rewrite `hx` using `[mem_valBall_iff_le_ord (mul_ne_zero hh h0), ord_mul hh h0]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem mem_valBall_of_mul_mem {h x : F} (hh : h ≠ 0) {M : ℤ} (hx : h * x ∈ valBall F M) :
    x ∈ valBall F (M - ord h) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_mem _
  · rw [mem_valBall_iff_le_ord h0]
    rw [mem_valBall_iff_le_ord (mul_ne_zero hh h0), ord_mul hh h0] at hx
    omega

/- English proof (translation)
Establish `h1 : Continuous fun p : Fˣ × F => (p.1 : F)` using `Units.continuous_val.comp continuous_fst`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Conclude with `h1`. Conclude with `h1.mul continuous_snd`.
-/
theorem continuous_line : Continuous fun p : Fˣ × F => (![(p.1 : F), (p.1 : F) * p.2] : Fin 2 → F) := by
  have h1 : Continuous fun p : Fˣ × F => (p.1 : F) := Units.continuous_val.comp continuous_fst
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact h1
  · exact h1.mul continuous_snd

/- English proof (translation)
The claim follows from `(by first | exact continuous_subtype_val | exact continuous_induced_dom | fun_prop : Continuous fun z : Circle => (z : ℂ)).comp (hψ.comp continuous_neg)`.
-/
theorem continuous_circle {ψ : AddChar F Circle} (hψ : Continuous ψ) :
    Continuous fun x : F => ((ψ (-x) : Circle) : ℂ) :=
  (by first | exact continuous_subtype_val | exact continuous_induced_dom | fun_prop : Continuous fun z : Circle => (z : ℂ)).comp (hψ.comp continuous_neg)

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Take `⟨N, M, -, -, hM⟩` from `exists_invariant_of_mem_schwartzBruhat2 hΦ`. Establish `hc : Continuous fun x : F => Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ)`. Use `(hΦ.1.continuous.comp ?_).mul (continuous_circle hψ)` and prove the remaining obligations. Conclude with `continuous_line.comp (Continuous.prodMk continuous_const continuous_id)`. Use `hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_valBall (M - ord (h : F))) fun x hx => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Establish `h1 : Φ ![(h : F), (h : F) * x] ≠ 0` using `left_ne_zero_of_mul hne`. Use `mem_box.1 (hM _ h1) 1` as an intermediate fact. Conclude with `hx (mem_valBall_of_mul_mem h.ne_zero (by simpa using this))`.
-/
theorem integrable_inner {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) {ψ : AddChar F Circle}
    (hψ : Continuous ψ) (ν : Measure F) [ν.IsAddHaarMeasure] (h : Fˣ) :
    Integrable (fun x : F => Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ)) ν := by
  obtain ⟨N, M, -, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  have hc : Continuous fun x : F => Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) := by
    refine (hΦ.1.continuous.comp ?_).mul (continuous_circle hψ)
    exact continuous_line.comp (Continuous.prodMk continuous_const continuous_id)
  refine hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_valBall (M - ord (h : F))) fun x hx => ?_)
  by_contra hne
  have h1 : Φ ![(h : F), (h : F) * x] ≠ 0 := left_ne_zero_of_mul hne
  have := mem_box.1 (hM _ h1) 1
  exact hx (mem_valBall_of_mul_mem h.ne_zero (by simpa using this))

/- English proof (translation)
Establish `ha : ((ψ (-x₀) : Circle) : ℂ) ≠ 1`. Introduce `h1`. Establish `h2 : ψ (-x₀) = 1` using `Circle.coe_eq_one.mp h1`. Rewrite `h2` using `[AddChar.map_neg_eq_inv, inv_eq_one]`. Conclude with `hx₀ h2`.

Use `eq_zero_of_eq_mul_of_ne_one ha ?_` and prove the remaining obligations. Rewrite using `[← integral_const_mul]`. Use `conv_lhs => rw [← integral_add_right_eq_self _ x₀]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `hd : (![0, (h : F) * x₀] : Fin 2 → F) ∈ box F N`.

Use `mem_box.2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Conclude with `zero_mem _`. Conclude with `hh`. Establish `e : (![(h : F), (h : F) * (x + x₀)] : Fin 2 → F) = ![(h : F), (h : F) * x] + ![0, (h : F) * x₀]`.

Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [mul_add]`. Establish `e2 : ψ (-(x + x₀)) = ψ (-x₀) * ψ (-x)`. Rewrite using `[← AddChar.map_add_eq_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only []`. Rewrite using `[e, hN _ _ hd, e2, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_eq_zero {Φ : (Fin 2 → F) → ℂ} {ψ : AddChar F Circle} (ν : Measure F)
    [ν.IsAddHaarMeasure] {N : ℤ} (hN : ∀ x, ∀ d ∈ box F N, Φ (x + d) = Φ x) {x₀ : F}
    (hx₀ : ψ x₀ ≠ 1) (h : Fˣ) (hh : (h : F) * x₀ ∈ valBall F N) :
    ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν = 0 := by
  have ha : ((ψ (-x₀) : Circle) : ℂ) ≠ 1 := by
    intro h1
    have h2 : ψ (-x₀) = 1 := Circle.coe_eq_one.mp h1
    rw [AddChar.map_neg_eq_inv, inv_eq_one] at h2
    exact hx₀ h2
  refine eq_zero_of_eq_mul_of_ne_one ha ?_
  rw [← integral_const_mul]
  conv_lhs => rw [← integral_add_right_eq_self _ x₀]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hd : (![0, (h : F) * x₀] : Fin 2 → F) ∈ box F N := by
    refine mem_box.2 fun i => ?_
    fin_cases i
    · exact zero_mem _
    · exact hh
  have e : (![(h : F), (h : F) * (x + x₀)] : Fin 2 → F) =
      ![(h : F), (h : F) * x] + ![0, (h : F) * x₀] := by
    ext i
    fin_cases i <;> simp [mul_add]
  have e2 : ψ (-(x + x₀)) = ψ (-x₀) * ψ (-x) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only []
  rw [e, hN _ _ hd, e2, Circle.coe_mul]
  ring

/- English proof (translation)
Establish `: ∀ x : F, Φ ![(h : F), (h : F) * x] = 0`. Introduce `x`. Assume the negation of the conclusion as `hne`. Establish `h0` using `mem_box.1 (hM _ hne) 0`. Establish `h1 : (h : F) ∈ valBall F M` using `by simpa using h0`.

Use `(mem_valBall_iff_le_ord h.ne_zero).1 h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`.
-/
theorem inner_eq_zero_of_lt {Φ : (Fin 2 → F) → ℂ} {ψ : AddChar F Circle} (ν : Measure F) {M : ℤ}
    (hM : ∀ x, Φ x ≠ 0 → x ∈ box F M) (h : Fˣ) (hh : ord (h : F) < M) :
    ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν = 0 := by
  have : ∀ x : F, Φ ![(h : F), (h : F) * x] = 0 := by
    intro x
    by_contra hne
    have h0 := mem_box.1 (hM _ hne) 0
    have h1 : (h : F) ∈ valBall F M := by simpa using h0
    have := (mem_valBall_iff_le_ord h.ne_zero).1 h1
    omega
  simp [this]

/- English proof (translation)
Establish `hz : ∀ x, x ∉ (valBall F (M - B) : Set F) → Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) = 0`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `h1 : Φ ![(h : F), (h : F) * x] ≠ 0` using `left_ne_zero_of_mul hne`. Establish `h2` using `mem_box.1 (hM _ h1) 1`.

Establish `h3 : x ∈ valBall F (M - ord (h : F))` using `mem_valBall_of_mul_mem h.ne_zero (by simpa using h2)`. Conclude with `hx (valBall_antitone (by omega) h3)`. Rewrite using `[← setIntegral_eq_integral_of_forall_compl_eq_zero hz]`. Use `norm_setIntegral_le_of_norm_le_const (isCompact_valBall _).measure_lt_top fun x _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Circle.norm_coe, mul_one]`.

Conclude with `hC _`.
-/
theorem norm_inner_le {Φ : (Fin 2 → F) → ℂ} {ψ : AddChar F Circle} (ν : Measure F)
    [ν.IsAddHaarMeasure] {M B : ℤ} (hM : ∀ x, Φ x ≠ 0 → x ∈ box F M) {C : ℝ}
    (hC : ∀ x, ‖Φ x‖ ≤ C) (h : Fˣ) (hh : ord (h : F) < B) :
    ‖∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν‖ ≤ C * ν.real (valBall F (M - B)) := by
  have hz : ∀ x, x ∉ (valBall F (M - B) : Set F) →
      Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) = 0 := by
    intro x hx
    by_contra hne
    have h1 : Φ ![(h : F), (h : F) * x] ≠ 0 := left_ne_zero_of_mul hne
    have h2 := mem_box.1 (hM _ h1) 1
    have h3 : x ∈ valBall F (M - ord (h : F)) :=
      mem_valBall_of_mul_mem h.ne_zero (by simpa using h2)
    exact hx (valBall_antitone (by omega) h3)
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  refine norm_setIntegral_le_of_norm_le_const (isCompact_valBall _).measure_lt_top fun x _ => ?_
  rw [norm_mul, Circle.norm_coe, mul_one]
  exact hC _

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Conclude with `hψ1 (DFunLike.ext _ _ fun a => (hall a).trans (AddChar.one_apply a).symm)`. Establish `hx₀0 : x₀ ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hx₀ (AddChar.map_zero_eq_one ψ)`. Take `⟨N, M, -, hN, hM⟩` from `exists_invariant_of_mem_schwartzBruhat2 hΦ`. Take `⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C` from `hΦ.2.exists_bound_of_continuous hΦ.1.continuous`. Use `set B : ℤ := N - ord x₀ with hB`.

Use `set S : Set Fˣ := ⋃ k ∈ Set.Ico M B, ordShell F k with hS`. Establish `hSm : MeasurableSet S` using `(Set.finite_Ico M B).measurableSet_biUnion fun k _ => measurableSet_ordShell k`. Establish `hSf : multHaar F S ≠ ⊤` using `(measure_biUnion_lt_top (Set.finite_Ico M B) fun k _ => by`. Rewrite using `[multHaar_ordShell]`. Conclude with `ENNReal.one_lt_top).ne`.

Establish `hmem : ∀ h : Fˣ, h ∈ S ↔ M ≤ ord (h : F) ∧ ord (h : F) < B`. Introduce `h`. Simplify using `[hS, mem_ordShell]`. Establish `hzero : ∀ h : Fˣ, h ∉ S → ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν = 0`. Introduce `h hh`.

Rewrite `hh` using `[hmem, not_and_or, not_le, not_lt]`. Break down `hh with hh | hh` into its components or cases. Conclude with `inner_eq_zero_of_lt ν hM h hh`. Use `inner_eq_zero ν hN hx₀ h ?_` and prove the remaining obligations. Rewrite using `[mem_valBall_iff_le_ord (mul_ne_zero h.ne_zero hx₀0), ord_mul h.ne_zero hx₀0]`.

Use linear arithmetic over natural numbers and integers. Establish `hc1 : Continuous fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ)` using `Units.continuous_val.comp (h₁.1.inv.mul h₂.1)`. Establish `hmp : ∀ h : Fˣ, mp h 1 = ((modulus (h : F) : ℝ) : ℂ)` using `fun h => by simp [mp]`. Establish `hc2 : Continuous fun h : Fˣ => mp h 1`. Simplify using `only [hmp]`.

Conclude with `Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))`. Establish `hI : StronglyMeasurable fun h : Fˣ => ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν`. Use `StronglyMeasurable.integral_prod_right (f := fun (h : Fˣ) (x : F) => Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ)) ?_` and prove the remaining obligations. Use `Continuous.stronglyMeasurable ?_` and prove the remaining obligations. Conclude with `(hΦ.1.continuous.comp continuous_line).mul ((continuous_circle hψ).comp continuous_snd)`.

Establish `hm : AEStronglyMeasurable (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν) (multHaar F)` using `((hc1.mul hc2).stronglyMeasurable.mul hI).aestronglyMeasurable`. Establish `hq : (1 : ℝ) ≤ residueCard F` using `by exact_mod_cast one_lt_residueCard.le`. Establish `hbd : ∀ h ∈ S, ‖(((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν‖ ≤ (residueCard F : ℝ) ^ (-M) * (C * ν.real (valBall F (M - B)))`. Introduce `h hh`. Take `⟨hl, hu⟩` from `(hmem h).1 hh`.

Establish `n1 : ‖(((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ)‖ = 1`. Rewrite using `[Units.val_mul, norm_mul, h₂.2, mul_one, Units.val_inv_eq_inv_val, norm_inv, h₁.2, inv_one]`. Establish `n2 : ‖mp h 1‖ ≤ (residueCard F : ℝ) ^ (-M)`. Rewrite using `[hmp, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _), modulus_of_ne_zero h.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]`. Conclude with `zpow_le_zpow_right₀ hq (by omega)`.

Rewrite using `[norm_mul, norm_mul, n1, one_mul]`. Conclude with `mul_le_mul n2 (norm_inner_le ν hM hC h hu) (norm_nonneg _) (by positivity)`. Establish `hon : IntegrableOn (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν) S (multHaar F)` using `Measure.integrableOn_of_bounded hSf hm ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall hbd))`. Use `(integrableOn_iff_integrable_of_support_subset fun h hh => ?_).1 hon` and prove the remaining obligations. Assume the negation of the conclusion as `hnS`.

Conclude with `hh (by simp [hzero h hnS])`.
-/
theorem integrable_outer {Φ : (Fin 2 → F) → ℂ} (hΦ : Φ ∈ schwartzBruhat2 F) {ψ : AddChar F Circle}
    (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (ν : Measure F) [ν.IsAddHaarMeasure] {μ₁ μ₂ : Fˣ →* ℂˣ}
    (h₁ : IsUnit1 μ₁) (h₂ : IsUnit1 μ₂) :
    Integrable (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν) (multHaar F) := by
  obtain ⟨x₀, hx₀⟩ : ∃ x, ψ x ≠ 1 := by
    by_contra hall
    push Not at hall
    exact hψ1 (DFunLike.ext _ _ fun a => (hall a).trans (AddChar.one_apply a).symm)
  have hx₀0 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  obtain ⟨N, M, -, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat2 hΦ
  obtain ⟨C, hC⟩ : ∃ C, ∀ x, ‖Φ x‖ ≤ C := hΦ.2.exists_bound_of_continuous hΦ.1.continuous
  set B : ℤ := N - ord x₀ with hB
  set S : Set Fˣ := ⋃ k ∈ Set.Ico M B, ordShell F k with hS
  have hSm : MeasurableSet S :=
    (Set.finite_Ico M B).measurableSet_biUnion fun k _ => measurableSet_ordShell k
  have hSf : multHaar F S ≠ ⊤ :=
    (measure_biUnion_lt_top (Set.finite_Ico M B) fun k _ => by
      rw [multHaar_ordShell]; exact ENNReal.one_lt_top).ne
  have hmem : ∀ h : Fˣ, h ∈ S ↔ M ≤ ord (h : F) ∧ ord (h : F) < B := by
    intro h
    simp [hS, mem_ordShell]
  have hzero : ∀ h : Fˣ, h ∉ S → ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν = 0 := by
    intro h hh
    rw [hmem, not_and_or, not_le, not_lt] at hh
    rcases hh with hh | hh
    · exact inner_eq_zero_of_lt ν hM h hh
    · refine inner_eq_zero ν hN hx₀ h ?_
      rw [mem_valBall_iff_le_ord (mul_ne_zero h.ne_zero hx₀0), ord_mul h.ne_zero hx₀0]
      omega
  have hc1 : Continuous fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (h₁.1.inv.mul h₂.1)
  have hmp : ∀ h : Fˣ, mp h 1 = ((modulus (h : F) : ℝ) : ℂ) := fun h => by simp [mp]
  have hc2 : Continuous fun h : Fˣ => mp h 1 := by
    simp only [hmp]
    exact Complex.continuous_ofReal.comp
      (NNReal.continuous_coe.comp (continuous_modulus.comp Units.continuous_val))
  have hI : StronglyMeasurable fun h : Fˣ => ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν := by
    refine StronglyMeasurable.integral_prod_right (f := fun (h : Fˣ) (x : F) =>
      Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ)) ?_
    refine Continuous.stronglyMeasurable ?_
    exact (hΦ.1.continuous.comp continuous_line).mul ((continuous_circle hψ).comp continuous_snd)
  have hm : AEStronglyMeasurable (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν) (multHaar F) :=
    ((hc1.mul hc2).stronglyMeasurable.mul hI).aestronglyMeasurable
  have hq : (1 : ℝ) ≤ residueCard F := by exact_mod_cast one_lt_residueCard.le
  have hbd : ∀ h ∈ S, ‖(((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν‖ ≤
        (residueCard F : ℝ) ^ (-M) * (C * ν.real (valBall F (M - B))) := by
    intro h hh
    obtain ⟨hl, hu⟩ := (hmem h).1 hh
    have n1 : ‖(((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ)‖ = 1 := by
      rw [Units.val_mul, norm_mul, h₂.2, mul_one, Units.val_inv_eq_inv_val, norm_inv, h₁.2, inv_one]
    have n2 : ‖mp h 1‖ ≤ (residueCard F : ℝ) ^ (-M) := by
      rw [hmp, Complex.norm_real, Real.norm_of_nonneg (NNReal.coe_nonneg _),
        modulus_of_ne_zero h.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
      exact zpow_le_zpow_right₀ hq (by omega)
    rw [norm_mul, norm_mul, n1, one_mul]
    exact mul_le_mul n2 (norm_inner_le ν hM hC h hu) (norm_nonneg _) (by positivity)
  have hon : IntegrableOn (fun h : Fˣ => (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
      ∫ x, Φ ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂ν) S (multHaar F) :=
    Measure.integrableOn_of_bounded hSf hm
      ((ae_restrict_iff' hSm).2 (Filter.Eventually.of_forall hbd))
  refine (integrableOn_iff_integrable_of_support_subset fun h hh => ?_).1 hon
  by_contra hnS
  exact hh (by simp [hzero h hnS])

end GlobalTheory.CompanionTheory.WhitLin

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ₁ hφ₁ φ₂ hφ₂`. Take `⟨hc, h1, -⟩` from `hψ`. Use `⟨funext fun g => ?_, fun c => funext fun g => ?_⟩` and prove the remaining obligations. Establish `i1` using `GlobalTheory.CompanionTheory.WhitLin.integrable_outer (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₁ g) hc h1 (selfDualMeasure ψ) h₁ h₂`. Establish `i2` using `GlobalTheory.CompanionTheory.WhitLin.integrable_outer (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₂ g) hc h1 (selfDualMeasure ψ) h₁ h₂`.

Establish `inner : ∀ h : Fˣ, ∫ x, (φ₁ + φ₂) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ = (∫ x, rt φ₁ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) + ∫ x, rt φ₂ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ`. Introduce `h`. Rewrite using `[← integral_add (GlobalTheory.CompanionTheory.WhitLin.integrable_inner (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₁ g) hc _ h) (GlobalTheory.CompanionTheory.WhitLin.integrable_inner (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₂ g) hc _ h)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only [Pi.add_apply, rt, add_mul]`.

Establish `key : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * (∫ x, (φ₁ + φ₂) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F = (∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * ∫ x, rt φ₁ g ![(h : F), (h : F) * x] * (ψ (-x) : …`. Rewrite using `[← integral_add i1 i2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only []`. Rewrite using `[inner h, mul_add]`.

Rewrite using `[Pi.add_apply]`. Unfold `W2`. Rewrite using `[key, mul_add]`. Both sides reduce to the same expression. Establish `key : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * (∫ x, (c • φ₁) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F = c * ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 * ∫ x, φ₁ (![(h : F), (h : F) * x] ᵥ* (g : Matri …`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Unfold `W2`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat : Ad3.SchwartzSpaceL2.SLin := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ₁ hφ₁ φ₂ hφ₂
  obtain ⟨hc, h1, -⟩ := hψ
  refine ⟨funext fun g => ?_, fun c => funext fun g => ?_⟩
  · have i1 := GlobalTheory.CompanionTheory.WhitLin.integrable_outer (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₁ g) hc h1
      (selfDualMeasure ψ) h₁ h₂
    have i2 := GlobalTheory.CompanionTheory.WhitLin.integrable_outer (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₂ g) hc h1
      (selfDualMeasure ψ) h₁ h₂
    have inner : ∀ h : Fˣ, ∫ x, (φ₁ + φ₂) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
          (ψ (-x) : ℂ) ∂selfDualMeasure ψ =
        (∫ x, rt φ₁ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ) +
          ∫ x, rt φ₂ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ := by
      intro h
      rw [← integral_add (GlobalTheory.CompanionTheory.WhitLin.integrable_inner (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₁ g) hc _ h)
        (GlobalTheory.CompanionTheory.WhitLin.integrable_inner (GlobalTheory.CompanionTheory.WhitLin.rt_mem hφ₂ g) hc _ h)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, rt, add_mul]
    have key : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
          (∫ x, (φ₁ + φ₂) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
            (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F =
        (∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
          ∫ x, rt φ₁ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ ∂multHaar F) +
        ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
          ∫ x, rt φ₂ g ![(h : F), (h : F) * x] * (ψ (-x) : ℂ) ∂selfDualMeasure ψ ∂multHaar F := by
      rw [← integral_add i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      simp only []
      rw [inner h, mul_add]
    rw [Pi.add_apply]
    unfold W2
    rw [key, mul_add]
    rfl
  · have key : ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
          (∫ x, (c • φ₁) (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
            (ψ (-x) : ℂ) ∂selfDualMeasure ψ) ∂multHaar F =
        c * ∫ h : Fˣ, (((μ₁ h)⁻¹ * μ₂ h : ℂˣ) : ℂ) * mp h 1 *
          ∫ x, φ₁ (![(h : F), (h : F) * x] ᵥ* (g : Matrix (Fin 2) (Fin 2) F)) *
            (ψ (-x) : ℂ) ∂selfDualMeasure ψ ∂multHaar F := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      ring
    rw [Pi.smul_apply, smul_eq_mul]
    unfold W2
    rw [key]
    ring
