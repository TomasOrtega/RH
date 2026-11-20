import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneMemGoodCT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsGrowthUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin

noncomputable section

namespace GlobalTheory.CompanionTheory.CTFin.Growth

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a r : ℕ}

/- English proof (translation)
Take `⟨K, hK, hcov⟩` from `Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)`. Set `Cm : Set (BlockIx a r → Ad E)` to `Set.univ.pi fun _ => K`. Establish `hCm : IsCompact Cm` using `isCompact_univ_pi fun _ => hK`. Establish `hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm)` using `hCm.image (JointCont.continuous_finPart g)`. Take `⟨C₀, N, hC₀, hgrow⟩` from `GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT`.

Establish `hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x)`. Establish `h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p))` using `continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)`. Conclude with `(JointCont.continuous_unip.comp h1).mul continuous_const`. Take `⟨B, hB⟩` from `(hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove`. Establish `hc : (0 : ℝ) ≤ 1 + 2 * a` using `by positivity`.

Use `⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩` and prove the remaining obligations. Use `choose q hq using fun p => hcov (x p)`. Take `⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x'` from `⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩`. Establish `e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) = ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y))`. Rewrite using `[unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]`.

Rewrite using `[e1, hφ.left]`. Use `(hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_` and prove the remaining obligations. Establish `hb : height (JointCont.infPart g x') ≤ max B 1` using `le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)`. Establish `hy` using `one_le_height y`. Establish `hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y`.

Use `(GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc`. Rewrite using `[mul_assoc, ← mul_pow]`. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀`.
-/
theorem exists_unip_bound {φ : Sm E a} (hφ : IsAutForm φ) (g : GA E a) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ (x : BlockIx a r → Ad E) (y : GL (Fin a) (Cinf E)),
      ‖φ.1 (unip x * (g * infGL E a y))‖ ≤ C * height y ^ N := by
  obtain ⟨K, hK, hcov⟩ := Formalism.IndefR.Eqv.G5.adl_cocompact (F := E)
  let Cm : Set (BlockIx a r → Ad E) := Set.univ.pi fun _ => K
  have hCm : IsCompact Cm := isCompact_univ_pi fun _ => hK
  have hT : IsCompact ((fun x => JointCont.finPart g x) '' Cm) :=
    hCm.image (JointCont.continuous_finPart g)
  obtain ⟨C₀, N, hC₀, hgrow⟩ := GlobalTheory.CompanionTheory.BoxBound.exists_growth_uniform hφ hT
  have hI : Continuous (fun x : BlockIx a r → Ad E => JointCont.infPart g x) := by
    have h1 : Continuous (fun x : BlockIx a r → Ad E => fun p => pInf E (x p)) :=
      continuous_pi fun p => JointCont.continuous_pInf.comp (continuous_apply p)
    exact (JointCont.continuous_unip.comp h1).mul continuous_const
  obtain ⟨B, hB⟩ := (hCm.image (GlobalTheory.CompanionTheory.BoxBound.continuous_height.comp hI)).bddAbove
  have hc : (0 : ℝ) ≤ 1 + 2 * a := by positivity
  refine ⟨C₀ * ((1 + 2 * a) * max B 1) ^ N, N, by positivity, fun x y => ?_⟩
  choose q hq using fun p => hcov (x p)
  obtain ⟨x', hx'm, rfl⟩ : ∃ x' ∈ Cm, x = (fun p => algebraMap E (Ad E) (q p)) + x' :=
    ⟨fun p => x p - algebraMap E (Ad E) (q p), fun p _ => hq p, by funext p; simp⟩
  have e1 : unip ((fun p => algebraMap E (Ad E) (q p)) + x') * (g * infGL E a y) =
      ratGL E a (unip q) * (finGL E a (JointCont.finPart g x') * infGL E a (JointCont.infPart g x' * y)) := by
    rw [unip_add, unip_algebraMap, mul_assoc, ← mul_assoc (unip x'), JointCont.unip_mul_eq, map_mul, mul_assoc]
  rw [e1, hφ.left]
  refine (hgrow _ ⟨x', hx'm, rfl⟩ _).trans ?_
  have hb : height (JointCont.infPart g x') ≤ max B 1 := le_trans (hB ⟨x', hx'm, rfl⟩) (le_max_left _ _)
  have hy := one_le_height y
  have hH : height (JointCont.infPart g x' * y) ≤ (1 + 2 * a) * max B 1 * height y := by
    refine (GlobalTheory.CompanionTheory.BoxBound.height_mul_le' _ _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hb (by linarith)) hc
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith [one_le_height (JointCont.infPart g x' * y)]) hH N) hC₀

/- English proof (translation)
Introduce `E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g`. Use `hμ` as an intermediate fact. Take `⟨C, N, -, h⟩` from `exists_unip_bound (r := r) hφ g`. Use `⟨C * μ.real 𝓕, N, fun y => ?_⟩` and prove the remaining obligations. Use `(norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ct_growth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (φ : Sm E a), IsAutForm φ → ∀ [MeasurableSpace (BlockIx a r → Ad E)] [BorelSpace (BlockIx a r → Ad E)] (μ : Measure (BlockIx a r → Ad E)) (𝓕 : Set (BlockIx a r → Ad E)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratN E a r) 𝓕 μ → ∀ g : GA E a, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖∫ x in 𝓕, φ.1 (unip x * (g * infGL E a y)) ∂μ‖ ≤ C * height y ^ N := by
  intro E _ _ _ a r φ hφ _ _ μ 𝓕 hμ hF g
  have := hμ
  obtain ⟨C, N, -, h⟩ := exists_unip_bound (r := r) hφ g
  refine ⟨C * μ.real 𝓕, N, fun y => ?_⟩
  refine (norm_setIntegral_le_of_norm_le_const (covol_lt_top μ 𝓕 hF) fun x _ => h x y).trans_eq ?_
  ring

end GlobalTheory.CompanionTheory.CTFin.Growth

end
