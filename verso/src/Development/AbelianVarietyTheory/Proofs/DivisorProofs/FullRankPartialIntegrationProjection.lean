import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv MeasureTheory

noncomputable section

namespace GlobalTheory.FibreLinear

/- English proof (translation)
Establish `hvan : ∀ x y, g (x, y) ≠ 0 → (x, y) ∈ tsupport g` using `fun x y h => subset_tsupport g h`. Use `⟨fun x => ⟨hlc.comp_continuous (Continuous.prodMk continuous_const continuous_id), ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hcs.isCompact.image continuous_snd) ?_` and prove the remaining obligations. Introduce `y hy`. Assume the negation of the conclusion as `hne`.

Conclude with `hy ⟨(x, y), hvan x y hne, rfl⟩`. Use `set K := Prod.snd '' tsupport g`. Establish `hK : IsCompact K` using `hcs.isCompact.image continuous_snd`. Rewrite using `[IsLocallyConstant.iff_eventually_eq _]`. Introduce `x₀`.

Establish `h1 : ∀ y ∈ K, ∀ᶠ z : X × Y in nhds (x₀, y), (fun x y => g (x, y) = g (x₀, y)) z.1 z.2`. Introduce `y _`. Establish `h0` using `(IsLocallyConstant.iff_eventually_eq _).mp hlc (x₀, y)`. Establish `hc : Continuous (fun z : X × Y => (x₀, z.2))` using `continuous_const.prodMk continuous_snd`. Establish `h3 : ∀ᶠ z : X × Y in nhds (x₀, y), g (x₀, z.2) = g (x₀, y)` using `(hc.tendsto (x₀, y)).eventually h0`.

Use `filter_upwards [h0, h3] with z hz hz'`. Conclude with `hz.trans hz'.symm`. Establish `h2` using `hK.eventually_forall_of_forall_eventually (P := fun x y => g (x, y) = g (x₀, y)) h1`. Use `filter_upwards [h2] with x hx`. Use function extensionality and compare the values at `y`.

Distinguish the cases in `hy : y ∈ K`. Conclude with `hx y hy`. Establish `hz : ∀ x', g (x', y) = 0`. Introduce `x'`. Assume the negation of the conclusion as `hne`.

Conclude with `hy ⟨(x', y), hvan x' y hne, rfl⟩`. Rewrite using `[hz, hz]`. Introduce `x hx y`. Assume the negation of the conclusion as `hne`. Conclude with `hx ⟨(x, y), hvan x y hne, rfl⟩`.
-/
theorem slice_props {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {g : X × Y → ℂ}
    (hlc : IsLocallyConstant g) (hcs : HasCompactSupport g) :
    (∀ x, IsLocallyConstant (fun y => g (x, y)) ∧ HasCompactSupport (fun y => g (x, y))) ∧
      IsLocallyConstant (fun x => fun y => g (x, y)) ∧
      ∀ x, x ∉ Prod.fst '' tsupport g → ∀ y, g (x, y) = 0 := by
  have hvan : ∀ x y, g (x, y) ≠ 0 → (x, y) ∈ tsupport g := fun x y h => subset_tsupport g h
  refine ⟨fun x => ⟨hlc.comp_continuous (Continuous.prodMk continuous_const continuous_id), ?_⟩, ?_, ?_⟩
  · refine HasCompactSupport.intro (hcs.isCompact.image continuous_snd) ?_
    intro y hy
    by_contra hne
    exact hy ⟨(x, y), hvan x y hne, rfl⟩
  · set K := Prod.snd '' tsupport g
    have hK : IsCompact K := hcs.isCompact.image continuous_snd
    rw [IsLocallyConstant.iff_eventually_eq _]
    intro x₀
    have h1 : ∀ y ∈ K, ∀ᶠ z : X × Y in nhds (x₀, y),
        (fun x y => g (x, y) = g (x₀, y)) z.1 z.2 := by
      intro y _
      have h0 := (IsLocallyConstant.iff_eventually_eq _).mp hlc (x₀, y)
      have hc : Continuous (fun z : X × Y => (x₀, z.2)) := continuous_const.prodMk continuous_snd
      have h3 : ∀ᶠ z : X × Y in nhds (x₀, y), g (x₀, z.2) = g (x₀, y) :=
        (hc.tendsto (x₀, y)).eventually h0
      filter_upwards [h0, h3] with z hz hz'
      exact hz.trans hz'.symm
    have h2 := hK.eventually_forall_of_forall_eventually (P := fun x y => g (x, y) = g (x₀, y)) h1
    filter_upwards [h2] with x hx
    funext y
    by_cases hy : y ∈ K
    · exact hx y hy
    · have hz : ∀ x', g (x', y) = 0 := by
        intro x'
        by_contra hne
        exact hy ⟨(x', y), hvan x' y hne, rfl⟩
      rw [hz, hz]
  · intro x hx y
    by_contra hne
    exact hx ⟨(x, y), hvan x y hne, rfl⟩

variable {k : Type} [Field k] [TopologicalSpace k]

def stack {ρ e d : ℕ} (p : Matrix (Fin ρ) (Fin d) k × Matrix (Fin e) (Fin d) k) : Matrix (Fin (ρ + e)) (Fin d) k :=
  (Matrix.fromRows p.1 p.2).submatrix finSumFinEquiv.symm id

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Unfold `stack`. Break down `h : finSumFinEquiv.symm i with a | a` into its components or cases. Simplify using `only [Matrix.submatrix_apply, h, Matrix.fromRows_apply_inl, id]`. Conclude with `(continuous_apply_apply a j).comp continuous_fst`.

Simplify using `only [Matrix.submatrix_apply, h, Matrix.fromRows_apply_inr, id]`. Conclude with `(continuous_apply_apply a j).comp continuous_snd`.
-/
theorem continuous_stack {ρ e d : ℕ} [IsTopologicalRing k] :
    Continuous (stack (k := k) (ρ := ρ) (e := e) (d := d)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold stack
  rcases h : finSumFinEquiv.symm i with a | a
  · simp only [Matrix.submatrix_apply, h, Matrix.fromRows_apply_inl, id]
    exact (continuous_apply_apply a j).comp continuous_fst
  · simp only [Matrix.submatrix_apply, h, Matrix.fromRows_apply_inr, id]
    exact (continuous_apply_apply a j).comp continuous_snd

def stackHomeo (ρ e d : ℕ) [IsTopologicalRing k] :
    Matrix (Fin ρ) (Fin d) k × Matrix (Fin e) (Fin d) k ≃ₜ Matrix (Fin (ρ + e)) (Fin d) k where
  toFun := stack
  invFun Z := (Matrix.toRows₁ (Z.submatrix finSumFinEquiv id), Matrix.toRows₂ (Z.submatrix finSumFinEquiv id))
  left_inv p := by
    ext i j <;> simp [stack, Matrix.toRows₁, Matrix.toRows₂]
  right_inv Z := by
    ext i j
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    rcases s with a | a <;> simp [stack, Matrix.toRows₁, Matrix.toRows₂]
  continuous_toFun := continuous_stack
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _
    · exact continuous_pi fun i => continuous_pi fun j => continuous_apply_apply _ _

/- English proof (translation)
Establish `hli : LinearIndependent k (stack (Y₁, Y₂)).row`. Rewrite using `[linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_row, h]`. Establish `hli1 : LinearIndependent k Y₁.row`. Use `hli.comp (fun i : Fin ρ => finSumFinEquiv (Sum.inl i)) (fun a b hab => Sum.inl_injective (finSumFinEquiv.injective hab))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `i j`. Simplify using `[stack, Matrix.row, Function.comp]`. Rewrite using `[Matrix.rank_eq_finrank_span_row, ← Set.finrank, ← linearIndependent_iff_card_eq_finrank_span.mp hli1, Fintype.card_fin]`.
-/
theorem rank_of_stack {ρ e d : ℕ} (Y₁ : Matrix (Fin ρ) (Fin d) k) (Y₂ : Matrix (Fin e) (Fin d) k)
    (h : (stack (Y₁, Y₂)).rank = ρ + e) : Y₁.rank = ρ := by
  have hli : LinearIndependent k (stack (Y₁, Y₂)).row := by
    rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, Set.finrank, ← Matrix.rank_eq_finrank_span_row, h]
  have hli1 : LinearIndependent k Y₁.row := by
    have := hli.comp (fun i : Fin ρ => finSumFinEquiv (Sum.inl i))
      (fun a b hab => Sum.inl_injective (finSumFinEquiv.injective hab))
    convert this using 1
    ext i j
    simp [stack, Matrix.row, Function.comp]
  rw [Matrix.rank_eq_finrank_span_row, ← Set.finrank, ← linearIndependent_iff_card_eq_finrank_span.mp hli1,
    Fintype.card_fin]

end GlobalTheory.FibreLinear

namespace GlobalTheory.FibreLinear

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

local instance t2Space_of_isNonarchimedeanLocalField' [ValuativeRel k] [IsNonarchimedeanLocalField k] : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

/- English proof (translation)
Establish `hlc : IsLocallyConstant (Θ ∘ stackHomeo (k` using `k) ρ e d) := hΘ.1.comp_continuous (stackHomeo ρ e d).continuous`. Establish `hcs : HasCompactSupport (Θ ∘ stackHomeo (k` using `k) ρ e d) := hΘ.2.comp_homeomorph _`. Take `⟨h1, h2, h3⟩` from `slice_props hlc hcs`. Conclude with `⟨h1, h2, ⟨_, hcs.isCompact.image continuous_fst, h3⟩⟩`.
-/
theorem sliceData {ρ e d : ℕ} (Θ : Matrix (Fin (ρ + e)) (Fin d) k → ℂ)
    (hΘ : Θ ∈ GlobalTheory.WeilM.SB (Matrix (Fin (ρ + e)) (Fin d) k)) :
    (∀ Y₁, IsLocallyConstant (fun Y₂ => Θ (stack (Y₁, Y₂))) ∧ HasCompactSupport (fun Y₂ => Θ (stack (Y₁, Y₂)))) ∧
      IsLocallyConstant (fun Y₁ => fun Y₂ => Θ (stack (Y₁, Y₂))) ∧
      ∃ K : Set (Matrix (Fin ρ) (Fin d) k), IsCompact K ∧ ∀ Y₁, Y₁ ∉ K → ∀ Y₂, Θ (stack (Y₁, Y₂)) = 0 := by
  have hlc : IsLocallyConstant (Θ ∘ stackHomeo (k := k) ρ e d) := hΘ.1.comp_continuous (stackHomeo ρ e d).continuous
  have hcs : HasCompactSupport (Θ ∘ stackHomeo (k := k) ρ e d) := hΘ.2.comp_homeomorph _
  obtain ⟨h1, h2, h3⟩ := slice_props hlc hcs
  exact ⟨h1, h2, ⟨_, hcs.isCompact.image continuous_fst, h3⟩⟩

/- English proof (translation)
Take `⟨h1, h2, K, hK, h3⟩` from `sliceData Θ.1 Θ.2.1`. Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `h2.comp (fun f => ∫ Y₂, f Y₂ ∂μ)`. Use `HasCompactSupport.intro hK fun Y₁ hY₁ => ?_` and prove the remaining obligations. Simplify using `only [h3 Y₁ hY₁, integral_zero]`.

Introduce `Y₁ hY₁`. Establish `: ∀ Y₂, Θ.1 (stack (Y₁, Y₂)) = 0` using `fun Y₂ => Θ.2.2 _ fun h => hY₁ (rank_of_stack Y₁ Y₂ h)`. Simplify using `only [this, integral_zero]`.
-/
theorem integral_mem {ρ e d : ℕ}
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (Θ : fullRk k (ρ + e) d) :
    (fun Y₁ : Matrix (Fin ρ) (Fin d) k => ∫ Y₂, Θ.1 (stack (Y₁, Y₂)) ∂μ) ∈ fullRk k ρ d := by
  obtain ⟨h1, h2, K, hK, h3⟩ := sliceData Θ.1 Θ.2.1
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact h2.comp (fun f => ∫ Y₂, f Y₂ ∂μ)
  · refine HasCompactSupport.intro hK fun Y₁ hY₁ => ?_
    simp only [h3 Y₁ hY₁, integral_zero]
  · intro Y₁ hY₁
    have : ∀ Y₂, Θ.1 (stack (Y₁, Y₂)) = 0 := fun Y₂ =>
      Θ.2.2 _ fun h => hY₁ (rank_of_stack Y₁ Y₂ h)
    simp only [this, integral_zero]

/- English proof (translation)
Take `⟨h1, -, -⟩` from `sliceData Θ.1 Θ.2.1`. Conclude with `(h1 Y₁).1.continuous.integrable_of_hasCompactSupport (h1 Y₁).2`.
-/
theorem slice_integrable {ρ e d : ℕ}
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure]
    (Θ : fullRk k (ρ + e) d) (Y₁ : Matrix (Fin ρ) (Fin d) k) :
    Integrable (fun Y₂ => Θ.1 (stack (Y₁, Y₂))) μ := by
  obtain ⟨h1, -, -⟩ := sliceData Θ.1 Θ.2.1
  exact (h1 Y₁).1.continuous.integrable_of_hasCompactSupport (h1 Y₁).2

end GlobalTheory.FibreLinear

/- English proof (translation)
Introduce `k _ _ _ _ ρ e d _ _ μ _`. Use `⟨{ toFun := fun Θ => ⟨_, GlobalTheory.FibreLinear.integral_mem μ Θ⟩ map_add' := ?_ map_smul' := ?_ }, fun Θ Y₁ => rfl⟩` and prove the remaining obligations. Introduce `Θ Θ'`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `Y₁`.

Conclude with `integral_add (GlobalTheory.FibreLinear.slice_integrable μ Θ Y₁) (GlobalTheory.FibreLinear.slice_integrable μ Θ' Y₁)`. Introduce `c Θ`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `Y₁`. Conclude with `integral_smul c _`.
-/
theorem GlobalTheory.FibreLinear.fibre_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ρ e d : ℕ)
    [MeasurableSpace (Matrix (Fin e) (Fin d) k)] [BorelSpace (Matrix (Fin e) (Fin d) k)]
    (μ : Measure (Matrix (Fin e) (Fin d) k)) [μ.IsAddHaarMeasure],
    ∃ P : fullRk k (ρ + e) d →ₗ[ℂ] fullRk k ρ d, ∀ (Θ : fullRk k (ρ + e) d) (Y₁ : Matrix (Fin ρ) (Fin d) k),
      (P Θ).1 Y₁ = ∫ Y₂, Θ.1 ((Matrix.fromRows Y₁ Y₂).submatrix finSumFinEquiv.symm id) ∂μ := by
  intro k _ _ _ _ ρ e d _ _ μ _
  refine ⟨{ toFun := fun Θ => ⟨_, GlobalTheory.FibreLinear.integral_mem μ Θ⟩
            map_add' := ?_
            map_smul' := ?_ }, fun Θ Y₁ => rfl⟩
  · intro Θ Θ'
    apply Subtype.ext
    funext Y₁
    exact integral_add (GlobalTheory.FibreLinear.slice_integrable μ Θ Y₁) (GlobalTheory.FibreLinear.slice_integrable μ Θ' Y₁)
  · intro c Θ
    apply Subtype.ext
    funext Y₁
    exact integral_smul c _
