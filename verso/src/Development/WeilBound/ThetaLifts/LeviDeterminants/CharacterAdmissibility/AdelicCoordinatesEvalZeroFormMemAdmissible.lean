import Development.WeilBound.ThetaLifts.LeviDeterminants.CharacterAdmissibility.ResAdm
import Development.WeilBound.ThetaLifts.LeviDeterminants.ExistsNeOfSurjOn
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.RealTest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace PositivityTheory.ThKF0.Chr

open GlobalTheory.SchwartzBox in

/- English proof (translation)
Establish `hs₁ : ∀ f₁ : SchwartzMap (κ → V) ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl))` using `fun f₁ => (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff`. Establish `hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr))` using `(f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff`. Use `⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f x => f (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr)) (fun f g x => by simp [add_mul]) (fun a f x => by simp [mul_assoc]) (fun f => (hs₁ f).mul hs₂) ?_, fun _ _ => rfl⟩` and prove the remaining obligations. Introduce and unpack `⟨k, n⟩`. Use `⟨Finset.Iic (k, n), ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (SchwartzMap.seminorm ℂ 0 (n - i) f₂ + SchwartzMap.seminorm ℂ k (n - i) f₂), by positivity, fun f₁ x => ?_⟩` and prove the remaining obligations.

Use `set N := (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ (κ → V) ℂ) f₁`. Establish `hN : ∀ a ≤ k, ∀ b ≤ n, SchwartzMap.seminorm ℂ a b f₁ ≤ N` using `fun a ha b hb => Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → V) ℂ) (i := (a, b)) (Finset.mem_Iic.2 (Prod.mk_le_mk.2 ⟨ha, hb⟩))`. Establish `hN0 : 0 ≤ N` using `apply_nonneg _ _`. Establish `hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k`. Establish `h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k` using `pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k`.

Use `h0.trans ?_` and prove the remaining obligations. Establish `p1` using `pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k`. Establish `p2` using `pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k`. Break down `le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h` into its components or cases. Rewrite using `[max_eq_right h]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[max_eq_left h]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL` using `norm_iteratedFDeriv_mul_le (hs₁ f₁) hs₂ x (n := n) (by exact_mod_cast le_top)`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)` and prove the remaining obligations. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `norm_iteratedFDeriv_restr_le Sum.inl f₁ i x`. Conclude with `norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x`.

Use `_ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ + ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by`. Rewrite using `[Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`. Use `_ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (N * SchwartzMap.seminorm ℂ 0 (n - i) f₂ + N * SchwartzMap.seminorm ℂ k (n - i) f₂) := by`. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`.

Use `gcongr`. Conclude with `(SchwartzMap.le_seminorm ℂ k i f₁ _).trans (hN k le_rfl i hi')`. Conclude with `SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _`. Conclude with `(SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _).trans (hN 0 (Nat.zero_le _) i hi')`. Conclude with `SchwartzMap.le_seminorm ℂ k (n - i) f₂ _`.

Use `_ = _ := by`. Rewrite using `[Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem exists_boxCLM {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (f₂ : SchwartzMap (κ' → V) ℂ) :
    ∃ T : SchwartzMap (κ → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ' → V) ℂ, ∀ f x, T f x = f (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr) := by
  have hs₁ : ∀ f₁ : SchwartzMap (κ → V) ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₁ (y ∘ Sum.inl)) :=
    fun f₁ => (f₁.smooth ⊤).comp (restr V (Sum.inl : κ → κ ⊕ κ')).contDiff
  have hs₂ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : κ ⊕ κ' → V => f₂ (y ∘ Sum.inr)) :=
    (f₂.smooth ⊤).comp (restr V (Sum.inr : κ' → κ ⊕ κ')).contDiff
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f x => f (x ∘ Sum.inl) * f₂ (x ∘ Sum.inr))
    (fun f g x => by simp [add_mul]) (fun a f x => by simp [mul_assoc]) (fun f => (hs₁ f).mul hs₂) ?_, fun _ _ => rfl⟩
  rintro ⟨k, n⟩
  refine ⟨Finset.Iic (k, n), ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ 0 (n - i) f₂ + SchwartzMap.seminorm ℂ k (n - i) f₂), by positivity, fun f₁ x => ?_⟩
  set N := (Finset.Iic (k, n)).sup (schwartzSeminormFamily ℂ (κ → V) ℂ) f₁
  have hN : ∀ a ≤ k, ∀ b ≤ n, SchwartzMap.seminorm ℂ a b f₁ ≤ N := fun a ha b hb =>
    Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → V) ℂ) (i := (a, b))
      (Finset.mem_Iic.2 (Prod.mk_le_mk.2 ⟨ha, hb⟩))
  have hN0 : 0 ≤ N := apply_nonneg _ _
  have hx : ‖x‖ ^ k ≤ ‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k := by
    have h0 : ‖x‖ ^ k ≤ (max ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖) ^ k :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_max_comp x) k
    refine h0.trans ?_
    have p1 := pow_nonneg (norm_nonneg (x ∘ Sum.inl)) k
    have p2 := pow_nonneg (norm_nonneg (x ∘ Sum.inr)) k
    rcases le_total ‖x ∘ Sum.inl‖ ‖x ∘ Sum.inr‖ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hL := norm_iteratedFDeriv_mul_le (hs₁ f₁) hs₂ x (n := n) (by exact_mod_cast le_top)
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f₁ (y ∘ Sum.inl) * f₂ (y ∘ Sum.inr)) x‖
      ≤ (‖x ∘ Sum.inl‖ ^ k + ‖x ∘ Sum.inr‖ ^ k) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ := by
        refine mul_le_mul hx (hL.trans ?_) (norm_nonneg _) (by positivity)
        refine Finset.sum_le_sum fun i _ => ?_
        gcongr
        · exact norm_iteratedFDeriv_restr_le Sum.inl f₁ i x
        · exact norm_iteratedFDeriv_restr_le Sum.inr f₂ (n - i) x
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          ((‖x ∘ Sum.inl‖ ^ k * ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖) *
              ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖ +
           ‖iteratedFDeriv ℝ i f₁ (x ∘ Sum.inl)‖ *
              (‖x ∘ Sum.inr‖ ^ k * ‖iteratedFDeriv ℝ (n - i) f₂ (x ∘ Sum.inr)‖)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
          (N * SchwartzMap.seminorm ℂ 0 (n - i) f₂ + N * SchwartzMap.seminorm ℂ k (n - i) f₂) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        gcongr
        · exact (SchwartzMap.le_seminorm ℂ k i f₁ _).trans (hN k le_rfl i hi')
        · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₂ _ _
        · exact (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f₁ _ _).trans (hN 0 (Nat.zero_le _) i hi')
        · exact SchwartzMap.le_seminorm ℂ k (n - i) f₂ _
    _ = _ := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by ring

variable {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ}

/- English proof (translation)
Introduce `g _`. Use `⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩` and prove the remaining obligations. Establish `h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0`. Use function extensionality and compare the values at `i`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`.

Use `show f (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) * g 0 = g 0 * f 0`. Rewrite using `[h1, mul_comm]`.
-/
theorem adelicCoordinatesEvalZeroForm_mem_admissible (κ : Type) [Fintype κ] : ev0 (AF F) κ ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
    funext i; exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
  show f (fun i : κ => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) * g 0 = g 0 * f 0
  rw [h1, mul_comm]

/- English proof (translation)
Introduce `φ₂ h₂ l hl g hg`. Proceed by induction on `h₂ using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨f₂, g₂, hg₂, rfl⟩` from `hx`. Take `⟨T, hT⟩` from `hl _ (GlobalTheory.SchwartzBox.sb_box hg hg₂)`.

Take `⟨U, hU⟩` from `exists_boxCLM (κ := κ) f₂`. Use `⟨T.comp U, fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[ContinuousLinearMap.comp_apply, ← hT]`. Use `congrArg l (funext fun x => ?_)` and prove the remaining obligations. Use `show pureA F f g _ * pureA F f₂ g₂ _ = _`.

Simplify using `only [pureA, hU]`. Rewrite using `[mul_mul_mul_comm]`. Both sides reduce to the same expression. Consider the case `zero => exact ⟨0, fun f => by show l (boxFun _ 0) = 0`. Rewrite using `[GlobalTheory.SchwartzBox.boxFun_zero_right, map_zero]⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨T, hT⟩` from `hx`. Take `⟨T', hT'⟩` from `hy`. Use `⟨T + T', fun f => ?_⟩` and prove the remaining obligations. Use `show l (boxFun _ (x + y)) = T f + T' f`.

Rewrite using `[GlobalTheory.SchwartzBox.boxFun_add_right, map_add, ← hT, ← hT']`. Both sides reduce to the same expression. Consider the case `smul c x _ hx`. Take `⟨T, hT⟩` from `hx`. Use `⟨c • T, fun f => ?_⟩` and prove the remaining obligations.

Use `show l (boxFun _ (c • x)) = c • T f`. Rewrite using `[GlobalTheory.SchwartzBox.boxFun_smul_right, map_smul, ← hT]`. Both sides reduce to the same expression.
-/
theorem box_adm (κ κ' : Type) [Fintype κ] [Fintype κ'] : ∀ φ₂ ∈ schA F κ', ∀ l ∈ (adeleClass F).adm (κ ⊕ κ'),
    l ∘ₗ boxL κ φ₂ ∈ (adeleClass F).adm κ := by
  intro φ₂ h₂ l hl g hg
  induction h₂ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f₂, g₂, hg₂, rfl⟩ := hx
    obtain ⟨T, hT⟩ := hl _ (GlobalTheory.SchwartzBox.sb_box hg hg₂)
    obtain ⟨U, hU⟩ := exists_boxCLM (κ := κ) f₂
    refine ⟨T.comp U, fun f => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← hT]
    refine congrArg l (funext fun x => ?_)
    show pureA F f g _ * pureA F f₂ g₂ _ = _
    simp only [pureA, hU]
    rw [mul_mul_mul_comm]
    rfl
  | zero => exact ⟨0, fun f => by
      show l (boxFun _ 0) = 0
      rw [GlobalTheory.SchwartzBox.boxFun_zero_right, map_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := hx
    obtain ⟨T', hT'⟩ := hy
    refine ⟨T + T', fun f => ?_⟩
    show l (boxFun _ (x + y)) = T f + T' f
    rw [GlobalTheory.SchwartzBox.boxFun_add_right, map_add, ← hT, ← hT']
    rfl
  | smul c x _ hx =>
    obtain ⟨T, hT⟩ := hx
    refine ⟨c • T, fun f => ?_⟩
    show l (boxFun _ (c • x)) = c • T f
    rw [GlobalTheory.SchwartzBox.boxFun_smul_right, map_smul, ← hT]
    rfl

/- English proof (translation)
The claim follows from `(GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1 ne κ _ := by obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ exact ⟨φ, h, fun e => h0 (congrFun e 0)⟩ ev0 κ _ := adelicCoordinatesEvalZeroForm_mem_admissible κ …`.
-/
theorem axB (hψ : IsStd ψ) : AxB (adeleClass F) ψ where
  schr κ _ := (GlobalTheory.T.theta_distribution_heisenberg_invariant F κ ψ hψ.1 (isStd_ne_one hψ) hψ.2.1).1
  ne κ _ := by
    obtain ⟨φ, h, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
    exact ⟨φ, h, fun e => h0 (congrFun e 0)⟩
  ev0 κ _ := adelicCoordinatesEvalZeroForm_mem_admissible κ
  res κ₁ κ _ _ j hj φ hφ := GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj φ hφ
  res_adm κ₁ κ _ _ j hj l hl g hg := by
    obtain ⟨T, hT⟩ := hl _ (GlobalTheory.RestrSchA.sb_comp_extend F hj hg)
    refine ⟨T.comp (GlobalTheory.RestrSchA.restrS F hj), fun f => ?_⟩
    rw [ContinuousLinearMap.comp_apply, ← hT]
    exact congrArg l (funext fun y => GlobalTheory.RestrSchA.pureA_extend F hj f g y)
  box κ κ' _ _ := GlobalTheory.SchwartzBox.boxFun_mem_schA F κ κ'
  box_adm κ κ' _ _ := box_adm κ κ'

/- English proof (translation)
Introduce `κ _ l hl hinv`. Take `⟨φ, hφ, h0⟩` from `GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ`. Establish `hz : ∀ (t : AF F), ∀ w ∈ LinearMap.ker (LinearMap.fst F (κ → F) (κ → F)), t • (((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) : (κ → AF F) × (κ → AF F)) = (0, t • fun i => algebraMap F (AF F) (w.2 i))` using `fun t w hw => by`. Establish `: w.1 = 0` using `hw`. Use `Prod.ext (funext fun i => ?_) rfl` and prove the remaining obligations.

Simplify using `[this]`. Use `h F ψ hψ κ (LinearMap.ker (LinearMap.fst F (κ → F) (κ → F))) (fun a => ⟨fun ha b hb => ?_, fun ha => ?_⟩) l hl (ev0 (AF F) κ) (adelicCoordinatesEvalZeroForm_mem_admissible κ) (fun t w hw φ hφ => ?_) (fun t w hw φ hφ => ?_) ⟨φ, hφ, h0⟩` and prove the remaining obligations. Establish `h1 : a.1 = 0` using `ha`. Establish `h2 : b.1 = 0` using `hb`. Rewrite using `[h1, h2, zero_dotProduct, zero_dotProduct]`.

Use `show a.1 = 0`. Use function extensionality and compare the values at `i`. Simplify using `using ha (0, Pi.single i 1) rfl`. Rewrite using `[hz t w hw]`. Conclude with `hinv _ φ hφ`.

Rewrite using `[hz t w hw]`. Simplify using `[ev0, schr]`.
-/
theorem axDelta_of (h : LagLine) (hψ : IsStd ψ) : AxDelta (adeleClass F) ψ := by
  intro κ _ l hl hinv
  obtain ⟨φ, hφ, h0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F κ
  have hz : ∀ (t : AF F), ∀ w ∈ LinearMap.ker (LinearMap.fst F (κ → F) (κ → F)),
      t • (((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i))) : (κ → AF F) × (κ → AF F)) =
        (0, t • fun i => algebraMap F (AF F) (w.2 i)) := fun t w hw => by
    have : w.1 = 0 := hw
    refine Prod.ext (funext fun i => ?_) rfl
    simp [this]
  refine h F ψ hψ κ (LinearMap.ker (LinearMap.fst F (κ → F) (κ → F))) (fun a => ⟨fun ha b hb => ?_, fun ha => ?_⟩) l hl
    (ev0 (AF F) κ) (adelicCoordinatesEvalZeroForm_mem_admissible κ) (fun t w hw φ hφ => ?_) (fun t w hw φ hφ => ?_) ⟨φ, hφ, h0⟩
  · have h1 : a.1 = 0 := ha
    have h2 : b.1 = 0 := hb
    rw [h1, h2, zero_dotProduct, zero_dotProduct]
  · show a.1 = 0
    funext i
    simpa using ha (0, Pi.single i 1) rfl
  · rw [hz t w hw]; exact hinv _ φ hφ
  · rw [hz t w hw]; simp [ev0, schr]

/- English proof (translation)
Introduce `κ _ S hS`. Take `⟨e, e', he, -, -, h1, -⟩` from `tw_bij h hψ (⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩ : Darboux (fun w w' : V (AF F) κ => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ) ⟨S, fun w w' => (hS w w').symm⟩`. Use `⟨e, he.maps, he.adm, he.Heisenberg₂, fun φ hφ h0 => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1 φ hφ, h0, map_zero]`.
-/
theorem axImp_of (h : PositivityTheory.Mix.AdelSt) (hψ : IsStd ψ) : AxImp (adeleClass F) ψ := by
  intro κ _ S hS
  obtain ⟨e, e', he, -, -, h1, -⟩ := tw_bij h hψ
    (⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩ : Darboux (fun w w' : V (AF F) κ => w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2) κ)
    ⟨S, fun w w' => (hS w w').symm⟩
  refine ⟨e, he.maps, he.adm, he.Heisenberg₂, fun φ hφ h0 => ?_⟩
  rw [← h1 φ hφ, h0, map_zero]

end PositivityTheory.ThKF0.Chr
