import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagLeviGroup GlobalTheory.GKModule GlobalTheory.RealInd
open scoped InnerProductSpace

namespace GlobalTheory.RealInd

/- English proof (translation)
Introduce `n ε D`. Take `⟨hnt, -, hU, -⟩` from `D.temp`. Set `C : Subgroup (UJ ε)` to `KG ε ⊓ leviOne ε D.W`. Establish `hC : IsCompact (C : Set (UJ ε))` using `(isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne D.flag D.pos)`. Use `haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC`.

Set `μ : Measure C` to `Measure.haarMeasure ⊤`. Take `⟨v, hv⟩` from `exists_ne (0 : D.V)`. Establish `hmat : ∀ c : C, uMat (c : UJ ε) ∈ mats (leviOne ε D.W)` using `fun c => ⟨c, c.2.2, rfl⟩`. Establish `hsc : Continuous fun c : C => D.σ (uMat (c : UJ ε)) v` using `(hU.2.2 v).comp_continuous (continuous_uMat.comp continuous_subtype_val) hmat`. Establish `hσ1 : D.σ (uMat (1 : UJ ε)) v = v` using `by rw [uMat_one, hU.1.1]; rfl`.

Establish `hS : IsOpen {c : C | 0 < RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ}` using `isOpen_lt continuous_const (RCLike.continuous_re.comp (continuous_const.inner hsc))`. Take `⟨U, hUo, hUS⟩` from `isOpen_induced_iff.1 hS`. Establish `h1U : (1 : UJ ε) ∈ U`. Establish `: (1 : C) ∈ Subtype.val ⁻¹' U`. Rewrite using `[hUS]`.

Express the relevant statement in the definitionally equal form `0 < RCLike.re ⟪v, D.σ (uMat (1 : UJ ε)) v⟫_ℂ`. Rewrite using `[hσ1, inner_self_eq_norm_sq]`. Conclude with `pow_pos (norm_pos_iff.2 hv) 2`. Conclude with `this`. Take `⟨f, hf, hf1, hfK⟩` from `CompletelyRegularSpace.completely_regular (1 : UJ ε) Uᶜ hUo.isClosed_compl (fun h => h h1U)`.

Set `b : UJ ε → ℝ` to `fun g => 1 - (f g : ℝ)`. Establish `hb : Continuous b` using `continuous_const.sub (continuous_subtype_val.comp hf)`. Establish `hb0 : ∀ g, 0 ≤ b g` using `fun g => sub_nonneg.2 (f g).2.2`. Establish `hb1 : b 1 = 1` using `by simp [b, hf1]`. Establish `hbU : ∀ g, b g ≠ 0 → g ∈ U` using `fun g hg => by`.

Assume the negation of the conclusion as `h`. Conclude with `hg (by simp [b, hfK h])`. Set `F : UJ ε → C → D.V` to `fun g c => ((b (g⁻¹ * c) : ℝ) : ℂ) • D.σ (uMat (c : UJ ε)) v`. Establish `hF : Continuous (Function.uncurry F)` using `(Complex.continuous_ofReal.comp (hb.comp (continuous_fst.inv.mul (continuous_subtype_val.comp continuous_snd)))).smul (hsc.comp continuous_snd)`. Establish `hFi : ∀ g, Integrable (F g) μ` using `fun g => (hF.comp (Continuous.prodMk_right g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.

Use `⟨fun g => ∫ c, F g c ∂μ, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_parametric_integral_of_continuous (μ := μ) hF (isCompact_univ (X := C))` as an intermediate fact. Simplify `this` using `only [Measure.restrict_univ]`. Introduce `h0 beta_reduce at h0`. Establish `e1 : ∫ c, ⟪v, F 1 c⟫_ℂ ∂μ = 0` using `by rw [integral_inner (hFi 1), h0, inner_zero_right]`.

Establish `e2 : ∫ c, RCLike.re ⟪v, F 1 c⟫_ℂ ∂μ = 0`. Rewrite using `[integral_re ((hFi 1).const_inner v), e1, map_zero]`. Set `G : C → ℝ` to `fun c => b c * RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ`. Establish `eG : ∀ c, RCLike.re ⟪v, F 1 c⟫_ℂ = G c` using `fun c => by`. Simplify using `only [F, G, inv_one, one_mul, inner_smul_right]`.

Simplify using the standard rewrite rules. Establish `hG : Continuous G` using `(hb.comp continuous_subtype_val).mul (RCLike.continuous_re.comp (continuous_const.inner hsc))`. Establish `hG0 : 0 ≤ G` using `fun c => by`. Distinguish the cases in `h : b c = 0`. Simplify using `[G, h]`.

Establish `hc : c ∈ Subtype.val ⁻¹' U` using `hbU _ h`. Rewrite `hc` using `[hUS]`. Conclude with `mul_nonneg (hb0 _) hc.le`. Establish `hG1 : G 1 ≠ 0`. Establish `: G 1 = ‖v‖ ^ 2`.

Simplify using `only [G]`. Rewrite using `[show ((1 : C) : UJ ε) = 1 from rfl, hb1, hσ1, inner_self_eq_norm_sq, one_mul]`. Rewrite using `[this]`. Conclude with `(pow_pos (norm_pos_iff.2 hv) 2).ne'`. Use `hG.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (HasCompactSupport.of_compactSpace _) hG0 hG1` as an intermediate fact.

Rewrite `this` using `[← integral_congr_ae (Filter.Eventually.of_forall eG), e2]`. Conclude with `lt_irrefl _ this`. Introduce `m hmM hmK g`. Set `m' : C` to `⟨m, hmK, hmM⟩`. Use `beta_reduce`.

Establish `e` using `integral_mul_left_eq_self (μ := μ) (F (m * g)) m'`. Rewrite using `[← e, ← ContinuousLinearMap.integral_comp_comm _ (hFi g)]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)` and prove the remaining obligations. Simplify using `only [F]`. Establish `h1 : (m * g)⁻¹ * ((m' * c : C) : UJ ε) = g⁻¹ * (c : UJ ε)`.

Express the relevant statement in the definitionally equal form `(m * g)⁻¹ * (m * (c : UJ ε)) = _`. Use `group`. Establish `h2 : D.σ (uMat ((m' * c : C) : UJ ε)) = D.σ (uMat m) ∘SL D.σ (uMat (c : UJ ε))`. Express the relevant statement in the definitionally equal form `D.σ (uMat (m * (c : UJ ε))) = _`. Rewrite using `[uMat_mul]`.

Conclude with `hU.1.2 _ ⟨m, hmM, rfl⟩ _ (hmat c)`. Rewrite using `[h1, h2, map_smul]`. Both sides reduce to the same expression.
-/
theorem exists_kLevi_equivariant_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), ∃ φ : UJ ε → D.V,
    Continuous φ ∧ φ 1 ≠ 0 ∧
    ∀ m ∈ leviOne ε D.W, m ∈ KG ε → ∀ g, φ (m * g) = D.σ (uMat m) (φ g) := by
  intro n ε D
  obtain ⟨hnt, -, hU, -⟩ := D.temp
  let C : Subgroup (UJ ε) := KG ε ⊓ leviOne ε D.W
  have hC : IsCompact (C : Set (UJ ε)) :=
    (isCompact_iff_compactSpace.2 (instCompactKG n ε)).inter_right (isClosed_leviOne D.flag D.pos)
  haveI : CompactSpace C := isCompact_iff_compactSpace.1 hC
  let μ : Measure C := Measure.haarMeasure ⊤
  obtain ⟨v, hv⟩ := exists_ne (0 : D.V)
  have hmat : ∀ c : C, uMat (c : UJ ε) ∈ mats (leviOne ε D.W) := fun c => ⟨c, c.2.2, rfl⟩
  have hsc : Continuous fun c : C => D.σ (uMat (c : UJ ε)) v :=
    (hU.2.2 v).comp_continuous (continuous_uMat.comp continuous_subtype_val) hmat
  have hσ1 : D.σ (uMat (1 : UJ ε)) v = v := by rw [uMat_one, hU.1.1]; rfl

  have hS : IsOpen {c : C | 0 < RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ} :=
    isOpen_lt continuous_const (RCLike.continuous_re.comp (continuous_const.inner hsc))
  obtain ⟨U, hUo, hUS⟩ := isOpen_induced_iff.1 hS
  have h1U : (1 : UJ ε) ∈ U := by
    have : (1 : C) ∈ Subtype.val ⁻¹' U := by
      rw [hUS]
      change 0 < RCLike.re ⟪v, D.σ (uMat (1 : UJ ε)) v⟫_ℂ
      rw [hσ1, inner_self_eq_norm_sq]
      exact pow_pos (norm_pos_iff.2 hv) 2
    exact this
  obtain ⟨f, hf, hf1, hfK⟩ := CompletelyRegularSpace.completely_regular (1 : UJ ε) Uᶜ hUo.isClosed_compl
    (fun h => h h1U)
  let b : UJ ε → ℝ := fun g => 1 - (f g : ℝ)
  have hb : Continuous b := continuous_const.sub (continuous_subtype_val.comp hf)
  have hb0 : ∀ g, 0 ≤ b g := fun g => sub_nonneg.2 (f g).2.2
  have hb1 : b 1 = 1 := by simp [b, hf1]
  have hbU : ∀ g, b g ≠ 0 → g ∈ U := fun g hg => by
    by_contra h
    exact hg (by simp [b, hfK h])
  let F : UJ ε → C → D.V := fun g c => ((b (g⁻¹ * c) : ℝ) : ℂ) • D.σ (uMat (c : UJ ε)) v
  have hF : Continuous (Function.uncurry F) :=
    (Complex.continuous_ofReal.comp (hb.comp (continuous_fst.inv.mul
      (continuous_subtype_val.comp continuous_snd)))).smul (hsc.comp continuous_snd)
  have hFi : ∀ g, Integrable (F g) μ := fun g =>
    (hF.comp (Continuous.prodMk_right g)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨fun g => ∫ c, F g c ∂μ, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := μ) hF (isCompact_univ (X := C))
    simpa only [Measure.restrict_univ] using this
  · intro h0
    beta_reduce at h0
    have e1 : ∫ c, ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by rw [integral_inner (hFi 1), h0, inner_zero_right]
    have e2 : ∫ c, RCLike.re ⟪v, F 1 c⟫_ℂ ∂μ = 0 := by
      rw [integral_re ((hFi 1).const_inner v), e1, map_zero]
    let G : C → ℝ := fun c => b c * RCLike.re ⟪v, D.σ (uMat (c : UJ ε)) v⟫_ℂ
    have eG : ∀ c, RCLike.re ⟪v, F 1 c⟫_ℂ = G c := fun c => by
      simp only [F, G, inv_one, one_mul, inner_smul_right]
      simp
    have hG : Continuous G :=
      (hb.comp continuous_subtype_val).mul (RCLike.continuous_re.comp (continuous_const.inner hsc))
    have hG0 : 0 ≤ G := fun c => by
      by_cases h : b c = 0
      · simp [G, h]
      · have hc : c ∈ Subtype.val ⁻¹' U := hbU _ h
        rw [hUS] at hc
        exact mul_nonneg (hb0 _) hc.le
    have hG1 : G 1 ≠ 0 := by
      have : G 1 = ‖v‖ ^ 2 := by
        simp only [G]
        rw [show ((1 : C) : UJ ε) = 1 from rfl, hb1, hσ1, inner_self_eq_norm_sq, one_mul]
      rw [this]
      exact (pow_pos (norm_pos_iff.2 hv) 2).ne'
    have := hG.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := μ) (HasCompactSupport.of_compactSpace _) hG0 hG1
    rw [← integral_congr_ae (Filter.Eventually.of_forall eG), e2] at this
    exact lt_irrefl _ this
  · intro m hmM hmK g
    let m' : C := ⟨m, hmK, hmM⟩
    beta_reduce
    have e := integral_mul_left_eq_self (μ := μ) (F (m * g)) m'
    rw [← e, ← ContinuousLinearMap.integral_comp_comm _ (hFi g)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only [F]
    have h1 : (m * g)⁻¹ * ((m' * c : C) : UJ ε) = g⁻¹ * (c : UJ ε) := by
      change (m * g)⁻¹ * (m * (c : UJ ε)) = _
      group
    have h2 : D.σ (uMat ((m' * c : C) : UJ ε)) = D.σ (uMat m) ∘SL D.σ (uMat (c : UJ ε)) := by
      change D.σ (uMat (m * (c : UJ ε))) = _
      rw [uMat_mul]
      exact hU.1.2 _ ⟨m, hmM, rfl⟩ _ (hmat c)
    rw [h1, h2, map_smul]
    rfl

end GlobalTheory.RealInd
