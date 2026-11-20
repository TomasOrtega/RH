import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadicalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedGainRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOneStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScaleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightDerivativeSmoothCuspidalSameLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

/- English proof (translation)
Assemble the required witnesses or components as `⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩`.
-/
theorem closeR_mono {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
    {u : GA D V} {a a' : ℝ} (h : CloseR θ V u a) (hle : a ≤ a') : CloseR θ V u a' :=
  ⟨h.1, fun τ i j => (h.2 τ i j).trans hle⟩

/- English proof (translation)
Introduce `D θ hθ V U hU A N`. Set `Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ` to `fun p f => Rder θ V p.1 p.2 f`. Set `𝓒 : Set (GA D V → ℂ)` to `{φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧ (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) → GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}`. Take `⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩` from `GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one D θ hθ V`. Take `⟨b, Cn, δn, hδn, hnear⟩` from `GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU`.

Take `⟨H, hH⟩` from `GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀`. Establish `hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒`. Introduce and unpack `ψ ⟨ha, hlev, hs, hg, hc⟩ i hi`. Conclude with `GlobalTheory.T.rightDerivative_smoothCuspidal_same_level D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc`. Establish `hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) → ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒`.

Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => intro _ ψ hψ`. Conclude with `hψ`. Consider the case `cons a l ih`.

Introduce `hl ψ hψ`. Conclude with `hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)`. Use `set Cn' := max Cn 0 with hCn'`. Establish `hCn'0 : 0 ≤ Cn'` using `le_max_right _ _`. Use `set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀`.

Establish `hδ₀pos : 0 < δ₀` using `lt_min hδn (div_pos hδ₁ (by linarith))`. Use `set K := max (max Cn (Cm * Cn')) (max H 1) with hK`. Establish `hK1 : Cn ≤ K` using `(le_max_left _ _).trans (le_max_left _ _)`. Establish `hK2 : Cm * Cn' ≤ K` using `(le_max_right _ _).trans (le_max_left _ _)`. Establish `hK3 : H ≤ K` using `(le_max_left _ _).trans (le_max_right _ _)`.

Establish `hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨ ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧ GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧ ∀ ψ ∈ …`. Introduce `g`. Take `⟨δ, hδ0, hδ1, hq, hcase⟩` from `hnear g`. Use `⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hδ : δ₀ ≤ δ`.

Conclude with `Or.inl hδ`. Use `right`. Use `push_neg at hδ`. Establish `hδn' : ¬ δn ≤ δ` using `fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)`. Take `⟨r, C₀, hC₀, hN⟩` from `hcase.resolve_left hδn'`.

Establish `hsmall : Cn' * δ ≤ δ₁`. Establish `h1 : δ < δ₁ / (Cn' + 1)` using `hδ.trans_le (min_le_right _ _)`. Rewrite `h1` using `[lt_div_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨(g * ·) '' Ω₀, ?_, ?_⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, hw, rfl⟩`. Establish `hq0` using `GlobalTheory.Grow.one_le_quotHeight V g`. Establish `hq1` using `GlobalTheory.Grow.one_le_quotHeight V (g * w)`. Establish `hw1` using `hH w hw`. Prove the components needed by the constructor for the conclusion.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)`. Use `_ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _`. Introduce and unpack `ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'`.

Establish `hsum : 0 ≤ ∑ i ∈ B, c i` using `Finset.sum_nonneg fun i hi => (hc' i hi).1`. Establish `hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p`. Use `GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_` and prove the remaining obligations. Take `⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩` from `hN m hm`. Establish `hval : ψ (m * g) = ψ (g * u)`.

Rewrite using `[hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]`. Rewrite using `[hval]`. Use `hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_` and prove the remaining obligations. Conclude with `(hc' p hp).2 _ ⟨w, hw, rfl⟩`. Use `hmain.trans ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum`. Take `⟨L, C', hLB, hL⟩` from `GlobalTheory.T.exists_rapid_decay_of_iterated_gain (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N`. Use `⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩` and prove the remaining obligations. Introduce `φ ha hlev hs hg hc c hcl g`.

Establish `hφ : φ ∈ 𝓒` using `⟨ha, hlev, hs, hg, hc⟩`. Establish `h` using `hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' => GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g`. Use `h.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cuspDecayBound : GlobalTheory.Published.CuspDecayBound := by
  intro D θ hθ V U hU A N
  let Dr : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → (GA D V → ℂ) → GA D V → ℂ :=
    fun p f => Rder θ V p.1 p.2 f
  let 𝓒 : Set (GA D V → ℂ) := {φ | IsAutFun V φ ∧ (∀ k ∈ U, k ∈ GfC V → ∀ g, φ (g * k) = φ g) ∧ SmoothW θ V φ ∧
    (∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt V p.1) →
      GlobalTheory.Grow.ModGrowthExp V A (l.foldr Dr φ)) ∧ IsCuspFun V φ}
  obtain ⟨B, Ω₀, Cm, δ₁, hB, hΩ₀, hδ₁, hCm, hmv⟩ := GlobalTheory.T.meanValue_ineq_rightTranslate_realPoint_near_one D θ hθ V
  obtain ⟨b, Cn, δn, hδn, hnear⟩ := GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale D θ hθ V U hU
  obtain ⟨H, hH⟩ := GlobalTheory.Grow.exists_height_le_of_isCompact V hΩ₀
  have hstab : ∀ ψ ∈ 𝓒, ∀ i ∈ B, Dr i ψ ∈ 𝓒 := by
    rintro ψ ⟨ha, hlev, hs, hg, hc⟩ i hi
    exact GlobalTheory.T.rightDerivative_smoothCuspidal_same_level D θ hθ V U i.1 i.2 (hB i hi) A ψ ha hlev hs hg hc
  have hwords : ∀ l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ), (∀ i ∈ l, i ∈ B) →
      ∀ ψ ∈ 𝓒, l.foldr Dr ψ ∈ 𝓒 := by
    intro l
    induction l with
    | nil => intro _ ψ hψ; exact hψ
    | cons a l ih =>
      intro hl ψ hψ
      exact hstab _ (ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)) ψ hψ) a (hl a List.mem_cons_self)
  set Cn' := max Cn 0 with hCn'
  have hCn'0 : 0 ≤ Cn' := le_max_right _ _
  set δ₀ := min δn (δ₁ / (Cn' + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min hδn (div_pos hδ₁ (by linarith))
  set K := max (max Cn (Cm * Cn')) (max H 1) with hK
  have hK1 : Cn ≤ K := (le_max_left _ _).trans (le_max_left _ _)
  have hK2 : Cm * Cn' ≤ K := (le_max_right _ _).trans (le_max_left _ _)
  have hK3 : H ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hstep : ∀ g, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ GlobalTheory.Grow.quotHeight V g * δ ^ b ≤ K ∧ (δ₀ ≤ δ ∨
      ∃ Ω : Set (GA D V), (∀ w ∈ Ω, GlobalTheory.Grow.quotHeight V w ≤ K * GlobalTheory.Grow.quotHeight V g ∧
        GlobalTheory.Grow.quotHeight V g ≤ K * GlobalTheory.Grow.quotHeight V w) ∧
      ∀ ψ ∈ 𝓒, ∀ c : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ → ℝ,
        (∀ i ∈ B, 0 ≤ c i ∧ ∀ w ∈ Ω, ‖Dr i ψ w‖ ≤ c i) → ‖ψ g‖ ≤ K * δ * ∑ i ∈ B, c i) := by
    intro g
    obtain ⟨δ, hδ0, hδ1, hq, hcase⟩ := hnear g
    refine ⟨δ, hδ0, hδ1, hq.trans hK1, ?_⟩
    by_cases hδ : δ₀ ≤ δ
    · exact Or.inl hδ
    right
    push_neg at hδ
    have hδn' : ¬ δn ≤ δ := fun h => absurd (hδ.trans_le (min_le_left _ _)) (not_lt.2 h)
    obtain ⟨r, C₀, hC₀, hN⟩ := hcase.resolve_left hδn'
    have hsmall : Cn' * δ ≤ δ₁ := by
      have h1 : δ < δ₁ / (Cn' + 1) := hδ.trans_le (min_le_right _ _)
      rw [lt_div_iff₀ (by linarith)] at h1
      nlinarith
    refine ⟨(g * ·) '' Ω₀, ?_, ?_⟩
    · rintro _ ⟨w, hw, rfl⟩
      have hq0 := GlobalTheory.Grow.one_le_quotHeight V g
      have hq1 := GlobalTheory.Grow.one_le_quotHeight V (g * w)
      have hw1 := hH w hw
      constructor
      · calc GlobalTheory.Grow.quotHeight V (g * w) ≤ GlobalTheory.Grow.quotHeight V g * GlobalTheory.Grow.height V w :=
              GlobalTheory.Grow.quotHeight_mul_le V g w
          _ ≤ GlobalTheory.Grow.quotHeight V g * K := mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V g := mul_comm _ _
      · calc GlobalTheory.Grow.quotHeight V g = GlobalTheory.Grow.quotHeight V (g * w * w⁻¹) := by rw [mul_inv_cancel_right]
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * GlobalTheory.Grow.height V w⁻¹ := GlobalTheory.Grow.quotHeight_mul_le V _ _
          _ ≤ GlobalTheory.Grow.quotHeight V (g * w) * K := by
              rw [GlobalTheory.Grow.height_inv]; exact mul_le_mul_of_nonneg_left (hw1.trans hK3) (by linarith)
          _ = K * GlobalTheory.Grow.quotHeight V (g * w) := mul_comm _ _
    · rintro ψ ⟨ha, hlev, hs, hg, hc⟩ c hc'
      have hsum : 0 ≤ ∑ i ∈ B, c i := Finset.sum_nonneg fun i hi => (hc' i hi).1
      have hmain : ‖ψ g‖ ≤ Cm * (Cn' * δ) * ∑ p ∈ B, c p := by
        refine GlobalTheory.T.norm_le_of_cuspidal_variation_unipotentRadical D V ψ ha hc r C₀ hC₀ g _ fun m hm => ?_
        obtain ⟨γ, hγ, u, k, hu, hkU, hkf, hmg⟩ := hN m hm
        have hval : ψ (m * g) = ψ (g * u) := by
          rw [hmg, show γ * g * u * k = γ * (g * u) * k by group, hlev k hkU hkf, ha.left γ hγ]
        rw [hval]
        refine hmv ψ hs g u (Cn' * δ) (mul_nonneg hCn'0 hδ0.le) hsmall
          (closeR_mono hu (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le)) c fun p hp w hw => ?_
        exact (hc' p hp).2 _ ⟨w, hw, rfl⟩
      refine hmain.trans ?_
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK2 hδ0.le) hsum
  obtain ⟨L, C', hLB, hL⟩ := GlobalTheory.T.exists_rapid_decay_of_iterated_gain (GA D V) (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) B
    (GlobalTheory.Grow.quotHeight V) 𝓒 Dr b K δ₀ hδ₀pos (GlobalTheory.Grow.one_le_quotHeight V) hstab hstep A N
  refine ⟨L, C' * 2 ^ A, fun l hl p hp => hB p (hLB l hl p hp), ?_⟩
  intro φ ha hlev hs hg hc c hcl g
  have hφ : φ ∈ 𝓒 := ⟨ha, hlev, hs, hg, hc⟩
  have h := hL φ hφ (fun l => c l * 2 ^ A) (fun l hl g' =>
    GlobalTheory.Grow.norm_le_quotHeight_pow (hwords l (hLB l hl) φ hφ).1.left (hcl l hl) g') g
  refine h.trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  ring

end GlobalTheory.CuspGeo
