import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordHolomorphicAndUniform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.CircleDop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
Rewrite using `[add_smul]`. Conclude with `Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t)`.
-/
theorem exp_smul_add {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) (s t : ℝ) :
    NormedSpace.exp ((s + t) • Z) = NormedSpace.exp (s • Z) * NormedSpace.exp (t • Z) := by
  rw [add_smul]
  exact Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t)

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
The claim follows from `NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)`.
-/
theorem continuous_exp_smul {m : ℕ} (Z : Matrix (Fin m) (Fin m) ℂ) :
    Continuous fun t : ℝ => NormedSpace.exp (t • Z) :=
  NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

/- English proof (translation)
Take `⟨w, τ, Z, -, hy⟩` from `hγ`. Use `choose y hy1 hy2 using hy`. Establish `inj : ∀ a b : GArch σ J w, GlobalTheory.Orb.archMat σ J τ a = GlobalTheory.Orb.archMat σ J τ b → a = b` using `fun a b e => by`. Rewrite `e` using `[GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h]`. Conclude with `(archEquiv J h τ).injective (Subtype.ext (Units.ext e))`.

Establish `hyadd : ∀ s t, y (s + t) = y s * y t` using `fun s t => inj _ _ (by rw [map_mul, hy2, hy2, hy2, exp_smul_add])`. Use `⟨fun s t => by rw [hy1, hy1, hy1, hyadd, map_mul], ?_⟩` and prove the remaining obligations. Establish `hyc : Continuous y` using `(GlobalTheory.Orb.isEmbedding_archMat _ h τ).continuous_iff.2 (by`. Express the relevant statement in the definitionally equal form `Continuous fun t => fun i j => GlobalTheory.Orb.archMat σ J τ (y t) i j`. Simplify using `only [hy2]`.

Conclude with `continuous_pi fun i => continuous_pi fun j => (continuous_exp_smul Z).matrix_elem i j)`. Rewrite using `[show γ = fun t => embArch σ J w (y t) from funext hy1]`. Conclude with `(continuous_embArch σ J w).comp hyc`.
-/
theorem realLine_hom (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    (∀ s t, γ (s + t) = γ s * γ t) ∧ Continuous γ := by
  obtain ⟨w, τ, Z, -, hy⟩ := hγ
  choose y hy1 hy2 using hy
  have inj : ∀ a b : GArch σ J w, GlobalTheory.Orb.archMat σ J τ a = GlobalTheory.Orb.archMat σ J τ b → a = b := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  have hyadd : ∀ s t, y (s + t) = y s * y t := fun s t =>
    inj _ _ (by rw [map_mul, hy2, hy2, hy2, exp_smul_add])
  refine ⟨fun s t => by rw [hy1, hy1, hy1, hyadd, map_mul], ?_⟩
  have hyc : Continuous y := (GlobalTheory.Orb.isEmbedding_archMat _ h τ).continuous_iff.2 (by
    change Continuous fun t => fun i j => GlobalTheory.Orb.archMat σ J τ (y t) i j
    simp only [hy2]
    exact continuous_pi fun i => continuous_pi fun j => (continuous_exp_smul Z).matrix_elem i j)
  rw [show γ = fun t => embArch σ J w (y t) from funext hy1]
  exact (continuous_embArch σ J w).comp hyc

/- English proof (translation)
Establish `h0 : HasDerivAt (fun u => f (g * γ t * γ u)) (lineDer γ f (g * γ t)) (t - t)`. Rewrite using `[sub_self]`. Conclude with `(GlobalTheory.WeakHolFamily.differentiable_line hf hγ (g * γ t) 0).hasDerivAt`. Establish `h1` using `HasDerivAt.comp_sub_const t t h0`. Establish `e : (fun u => f (g * γ u)) = fun x => f (g * γ t * γ (x - t))` using `funext fun u => by`.

Rewrite using `[mul_assoc, ← hadd, add_sub_cancel]`. Rewrite using `[e]`. Conclude with `h1`.
-/
theorem hasDerivAt_line {f : GAd σ J → ℂ} (hf : GlobalTheory.WeakHolFamily.SmoothLines σ J f) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (hadd : ∀ s t, γ (s + t) = γ s * γ t) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun u => f (g * γ u)) (lineDer γ f (g * γ t)) t := by
  have h0 : HasDerivAt (fun u => f (g * γ t * γ u)) (lineDer γ f (g * γ t)) (t - t) := by
    rw [sub_self]; exact (GlobalTheory.WeakHolFamily.differentiable_line hf hγ (g * γ t) 0).hasDerivAt
  have h1 := HasDerivAt.comp_sub_const t t h0
  have e : (fun u => f (g * γ u)) = fun x => f (g * γ t * γ (x - t)) := funext fun u => by
    rw [mul_assoc, ← hadd, add_sub_cancel]
  rw [e]
  exact h1

/- English proof (translation)
Take `⟨hadd, hγc⟩` from `realLine_hom h hγ`. Take `⟨N, C, hC⟩` from `hbd`. Establish `hγ0 : γ 0 = 1`. Use `hadd 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Conclude with `mul_eq_left.1 this.symm`. Establish `hmem : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r` using `fun θ => circleMap_mem_sphere s₀ hr.le θ`. Take `⟨Mc, hMc⟩` from `(isCompact_sphere s₀ r).exists_bound_of_continuousOn hc`. Establish `hMc0 : 0 ≤ Mc` using `(norm_nonneg _).trans (hMc _ (hmem 0))`. Establish `hht : Continuous fun t => (height σ J (γ t) : ℝ)` using `NNReal.continuous_coe.comp ((continuous_height_GAd σ J).comp hγc)`.

Take `⟨Hγ, hHγ⟩` from `(isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn hht.continuousOn`. Use `set Y : ℝ := (height σ J g : ℝ) * |Hγ| with hY`. Establish `hdc : Continuous fun θ => deriv (circleMap s₀ r) θ`. Rewrite using `[show (fun θ => deriv (circleMap s₀ r) θ) = fun θ => circleMap 0 r θ * Complex.I from`. Use function extensionality and compare the values at `fun θ => deriv_circleMap s₀ r θ]`.

Conclude with `(continuous_circleMap 0 r).mul continuous_const`. Establish `hnd : ∀ θ, ‖deriv (circleMap s₀ r) θ‖ = |r|` using `fun θ => by`. Rewrite using `[deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]`. Set `Fn : ℝ → ℝ → ℂ` to `fun t θ => deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * K (circleMap s₀ r θ) (g * γ t))`. Set `Fn' : ℝ → ℝ → ℂ` to `fun t θ => deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * lineDer γ (K (circleMap s₀ r θ)) (g * γ t))`.

Establish `hcc : Continuous fun θ => c (circleMap s₀ r θ)` using `hc.comp_continuous (continuous_circleMap s₀ r) hmem`. Establish `hFc : ∀ t, Continuous (Fn t)` using `fun t => hdc.smul (hcc.mul ((hcont (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))`. Establish `hFc' : ∀ t, Continuous (Fn' t)` using `fun t => hdc.smul (hcc.mul ((hcont' (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))`. Establish `hL : ∀ w ∈ Metric.sphere s₀ r, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖lineDer γ (K w) (g * γ t)‖ ≤ |C| * Y ^ N`. Introduce `w hw t ht`.

Establish `h1 : (height σ J (g * γ t) : ℝ) ≤ Y`. Establish `e1 : (height σ J (g * γ t) : ℝ) ≤ (height σ J g : ℝ) * (height σ J (γ t) : ℝ)`. Conclude with `height_mul_le σ J g (γ t)` after adjusting the coercions. Establish `e2 : (height σ J (γ t) : ℝ) ≤ |Hγ|`. Use `hHγ t (Metric.ball_subset_closedBall ht)` as an intermediate fact.

Rewrite `this` using `[Real.norm_eq_abs]`. Conclude with `(le_abs_self _).trans (this.trans (le_abs_self _))`. Conclude with `e1.trans (mul_le_mul_of_nonneg_left e2 (NNReal.coe_nonneg _))`. Use `(hC w hw _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) N)).trans ?_)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N) (abs_nonneg C)`.

Establish `key` using `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 2 * Real.pi) (F := Fn) (F' := Fn') (x₀ := (0 : ℝ)) (bound := fun _ => |r| * (Mc * (|C| * Y ^ N))) (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Filter.Eventually.of_forall fun t => (hFc t).ae …`. Simplify using `only [Fn', norm_smul, norm_mul, hnd]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul (hMc _ (hmem θ)) (hL _ (hmem θ) t ht) (norm_nonneg _) hMc0) (abs_nonneg r))`. Use `intervalIntegrable_const`. Use the proof step `(ae_of_all _ fun θ _ t _ => ((hasDerivAt_line (hK _ (hmem θ)) hγ hadd g t).const_mul (c (circleMap s₀ r θ))).const_smul (deriv (circleMap s₀ r) θ))`.

Use `show deriv (fun t => ∫ θ in (0 : ℝ)..2 * Real.pi, Fn t θ) 0 = _`. Rewrite using `[key.2.deriv]`. Simplify using `only [Fn', hγ0, mul_one]`. Both sides reduce to the same expression.
-/
theorem lineDer_circleIntegral (h : IsCMExt F E σ) {K : ℂ → GAd σ J → ℂ} {c : ℂ → ℂ} {s₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hc : ContinuousOn c (Metric.sphere s₀ r))
    (hK : ∀ w ∈ Metric.sphere s₀ r, GlobalTheory.WeakHolFamily.SmoothLines σ J (K w))
    {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ)
    (hcont : ∀ g, ContinuousOn (fun w => K w g) (Metric.sphere s₀ r))
    (hcont' : ∀ g, ContinuousOn (fun w => lineDer γ (K w) g) (Metric.sphere s₀ r))
    (hbd : ∃ (N : ℕ) (C : ℝ), ∀ w ∈ Metric.sphere s₀ r, ∀ g, ‖lineDer γ (K w) g‖ ≤ C * (height σ J g : ℝ) ^ N)
    (g : GAd σ J) :
    lineDer γ (fun g => ∮ w in C(s₀, r), c w * K w g) g = ∮ w in C(s₀, r), c w * lineDer γ (K w) g := by
  obtain ⟨hadd, hγc⟩ := realLine_hom h hγ
  obtain ⟨N, C, hC⟩ := hbd
  have hγ0 : γ 0 = 1 := by
    have := hadd 0 0; rw [add_zero] at this; exact mul_eq_left.1 this.symm
  have hmem : ∀ θ, circleMap s₀ r θ ∈ Metric.sphere s₀ r := fun θ => circleMap_mem_sphere s₀ hr.le θ
  obtain ⟨Mc, hMc⟩ := (isCompact_sphere s₀ r).exists_bound_of_continuousOn hc
  have hMc0 : 0 ≤ Mc := (norm_nonneg _).trans (hMc _ (hmem 0))
  have hht : Continuous fun t => (height σ J (γ t) : ℝ) :=
    NNReal.continuous_coe.comp ((continuous_height_GAd σ J).comp hγc)
  obtain ⟨Hγ, hHγ⟩ := (isCompact_closedBall (0 : ℝ) 1).exists_bound_of_continuousOn hht.continuousOn
  set Y : ℝ := (height σ J g : ℝ) * |Hγ| with hY
  have hdc : Continuous fun θ => deriv (circleMap s₀ r) θ := by
    rw [show (fun θ => deriv (circleMap s₀ r) θ) = fun θ => circleMap 0 r θ * Complex.I from
      funext fun θ => deriv_circleMap s₀ r θ]
    exact (continuous_circleMap 0 r).mul continuous_const
  have hnd : ∀ θ, ‖deriv (circleMap s₀ r) θ‖ = |r| := fun θ => by
    rw [deriv_circleMap, norm_mul, norm_circleMap_zero, Complex.norm_I, mul_one]
  let Fn : ℝ → ℝ → ℂ := fun t θ => deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * K (circleMap s₀ r θ) (g * γ t))
  let Fn' : ℝ → ℝ → ℂ := fun t θ =>
    deriv (circleMap s₀ r) θ • (c (circleMap s₀ r θ) * lineDer γ (K (circleMap s₀ r θ)) (g * γ t))
  have hcc : Continuous fun θ => c (circleMap s₀ r θ) := hc.comp_continuous (continuous_circleMap s₀ r) hmem
  have hFc : ∀ t, Continuous (Fn t) := fun t =>
    hdc.smul (hcc.mul ((hcont (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))
  have hFc' : ∀ t, Continuous (Fn' t) := fun t =>
    hdc.smul (hcc.mul ((hcont' (g * γ t)).comp_continuous (continuous_circleMap s₀ r) hmem))
  have hL : ∀ w ∈ Metric.sphere s₀ r, ∀ t ∈ Metric.ball (0 : ℝ) 1, ‖lineDer γ (K w) (g * γ t)‖ ≤ |C| * Y ^ N := by
    intro w hw t ht
    have h1 : (height σ J (g * γ t) : ℝ) ≤ Y := by
      have e1 : (height σ J (g * γ t) : ℝ) ≤ (height σ J g : ℝ) * (height σ J (γ t) : ℝ) := by
        exact_mod_cast height_mul_le σ J g (γ t)
      have e2 : (height σ J (γ t) : ℝ) ≤ |Hγ| := by
        have := hHγ t (Metric.ball_subset_closedBall ht)
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_abs_self _))
      exact e1.trans (mul_le_mul_of_nonneg_left e2 (NNReal.coe_nonneg _))
    refine (hC w hw _).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg (NNReal.coe_nonneg _) N)).trans ?_)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) h1 N) (abs_nonneg C)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := Fn) (F' := Fn') (x₀ := (0 : ℝ)) (bound := fun _ => |r| * (Mc * (|C| * Y ^ N)))
    (Metric.ball_mem_nhds (0 : ℝ) one_pos) (Filter.Eventually.of_forall fun t => (hFc t).aestronglyMeasurable)
    ((hFc 0).intervalIntegrable _ _) (hFc' 0).aestronglyMeasurable
    (ae_of_all _ fun θ _ t ht => by
      simp only [Fn', norm_smul, norm_mul, hnd]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hMc _ (hmem θ)) (hL _ (hmem θ) t ht) (norm_nonneg _) hMc0)
        (abs_nonneg r))
    intervalIntegrable_const
    (ae_of_all _ fun θ _ t _ =>
      ((hasDerivAt_line (hK _ (hmem θ)) hγ hadd g t).const_mul (c (circleMap s₀ r θ))).const_smul
        (deriv (circleMap s₀ r) θ))
  show deriv (fun t => ∫ θ in (0 : ℝ)..2 * Real.pi, Fn t θ) 0 = _
  rw [key.2.deriv]
  simp only [Fn', hγ0, mul_one]
  rfl

end GlobalTheory.CircleDop

namespace GlobalTheory.CircleDop

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
The claim follows from `| [], _, _ => rfl | γ :: l, hl, g => by have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h') have hγ := hl γ List.mem_cons_self have ih := foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l hl' have hS : Metric.sphere s₀ r ⊆ V := Metric.sphe …`.
-/
theorem foldr_circleIntegral (h : IsCMExt F E σ) (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ)
    (hV : IsOpen V) (hr : 0 < r) (hsub : Metric.closedBall s₀ r ⊆ V) (hH : ∀ s ∈ V, IsSmoothModerate σ J (H₀ s))
    (hμ : ∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) (j : ℤ) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      l.foldr lineDer (fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * H₀ w g) g =
        ∮ w in C(s₀, r), (w - s₀) ^ j * l.foldr lineDer (H₀ w) g
  | [], _, _ => rfl
  | γ :: l, hl, g => by
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
    have hγ := hl γ List.mem_cons_self
    have ih := foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l hl'
    have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
    have W1 := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ l hl'
    have W2 := GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
      (isCompact_sphere s₀ r) hS hH hμ (γ :: l) hl
    obtain ⟨N, C, hC⟩ := W2.2
    rw [List.foldr_cons, show l.foldr lineDer (fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * H₀ w g) =
      fun g => ∮ w in C(s₀, r), (w - s₀) ^ j * l.foldr lineDer (H₀ w) g from funext ih]
    refine lineDer_circleIntegral h hr ?_ (fun w hw => GlobalTheory.WeakHolFamily.smoothLines_foldr (hH w (hS hw)).smooth l hl')
      hγ (fun g => (W1.1 g).continuousOn.mono hS) (fun g => (W2.1 g).continuousOn.mono hS) ⟨N, C, hC⟩ g
    exact (continuousOn_id.sub continuousOn_const).zpow₀ j fun w hw =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere hw hr.ne'))

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J _ H₀ s₀ r V hV hr hsub hH hμ j z hz g`. Establish `hS : Metric.sphere s₀ r ⊆ V` using `Metric.sphere_subset_closedBall.trans hsub`. Establish `hc : ContinuousOn (fun w : ℂ => (w - s₀) ^ j) (Metric.sphere s₀ r)` using `(continuousOn_id.sub continuousOn_const).zpow₀ j fun w hw => Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere hw hr.ne'))`. Establish `hint : ∀ l ∈ z.support, CircleIntegrable (fun w => z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g)) s₀ r` using `fun l hl => ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul (hc.mul (((GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV (isCompact_sphere s₀ r) hS hH hμ l (hz l hl)).1 g).continuousOn.mono hS)))`. Simplify using `only [GlobalTheory.UAut.dop, Finsupp.sum]`.

Rewrite using `[show (fun w => (w - s₀) ^ j * ∑ l ∈ z.support, z l * l.foldr lineDer (H₀ w) g) = fun w => ∑ l ∈ z.support, z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g) from`. Use function extensionality and compare the values at `fun w => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]`. Rewrite using `[circleIntegral.integral_fun_sum hint]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[circleIntegral.integral_const_mul, foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l (hz l hl) g]`.
-/
theorem dop_circleIntegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (H₀ : ℂ → GAd σ J → ℂ) (s₀ : ℂ) (r : ℝ) (V : Set ℂ),
    IsOpen V → 0 < r → Metric.closedBall s₀ r ⊆ V → (∀ s ∈ V, IsSmoothModerate σ J (H₀ s)) →
    (∀ μ, GlobalTheory.EisLine.IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H₀ s)) V) → ∀ j : ℤ,
    ∀ z : List (ℝ → GAd σ J) →₀ ℂ, (∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ) → ∀ g,
      GlobalTheory.UAut.dop z (fun g => circleIntegral (fun w => (w - s₀) ^ j * H₀ w g) s₀ r) g =
        circleIntegral (fun w => (w - s₀) ^ j * GlobalTheory.UAut.dop z (H₀ w) g) s₀ r := by
  intro F E _ _ _ _ _ σ h n J _ H₀ s₀ r V hV hr hsub hH hμ j z hz g
  have hS : Metric.sphere s₀ r ⊆ V := Metric.sphere_subset_closedBall.trans hsub
  have hc : ContinuousOn (fun w : ℂ => (w - s₀) ^ j) (Metric.sphere s₀ r) :=
    (continuousOn_id.sub continuousOn_const).zpow₀ j fun w hw =>
      Or.inl (sub_ne_zero.2 (Metric.ne_of_mem_sphere hw hr.ne'))
  have hint : ∀ l ∈ z.support,
      CircleIntegrable (fun w => z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g)) s₀ r := fun l hl =>
    ContinuousOn.circleIntegrable hr.le (continuousOn_const.mul (hc.mul
      (((GlobalTheory.WeakHolFamily.word_holomorphic_and_uniform F E σ n J H₀ V (Metric.sphere s₀ r) hV
        (isCompact_sphere s₀ r) hS hH hμ l (hz l hl)).1 g).continuousOn.mono hS)))
  simp only [GlobalTheory.UAut.dop, Finsupp.sum]
  rw [show (fun w => (w - s₀) ^ j * ∑ l ∈ z.support, z l * l.foldr lineDer (H₀ w) g) =
      fun w => ∑ l ∈ z.support, z l * ((w - s₀) ^ j * l.foldr lineDer (H₀ w) g) from
    funext fun w => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring]
  rw [circleIntegral.integral_fun_sum hint]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [circleIntegral.integral_const_mul, foldr_circleIntegral h H₀ s₀ r V hV hr hsub hH hμ j l (hz l hl) g]

end GlobalTheory.CircleDop
