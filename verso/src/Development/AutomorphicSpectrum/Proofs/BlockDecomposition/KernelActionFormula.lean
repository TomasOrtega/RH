import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `e1 : cls μ a = ha.toLp _` using `dif_pos ha`. Establish `e2 : cls μ b = hb.toLp _` using `dif_pos hb`. Rewrite using `[e1, e2, L2.inner_def]`. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2`.

Rewrite using `[h1, h2]`.
-/
theorem inner_cls_eq {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] {a b : Mat n → V} (ha : MemLp (fun y : G n => a y.val) 2 μ)
    (hb : MemLp (fun y : G n => b y.val) 2 μ) :
    ⟪cls μ a, cls μ b⟫_ℂ = ∫ y : G n, ⟪a y.val, b y.val⟫_ℂ ∂μ := by
  have e1 : cls μ a = ha.toLp _ := dif_pos ha
  have e2 : cls μ b = hb.toLp _ := dif_pos hb
  rw [e1, e2, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

/- English proof (translation)
Establish `h` using `L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) (hb.toLp _)`. Use `h.congr ?_` and prove the remaining obligations. Use `filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2`. Rewrite using `[h1, h2]`.
-/
theorem integrable_inner_of_memLp {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {a b : G n → V} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    Integrable (fun y => ⟪a y, b y⟫_ℂ) μ := by
  have h := L2.integrable_inner (𝕜 := ℂ) (ha.toLp _) (hb.toLp _)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with y h1 h2
  rw [h1, h2]

/- English proof (translation)
Set `b` to `stdOrthonormalBasis ℂ V`. Establish `key : (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) = fun y => ∑ i, ⟪A y (b i), φ y⟫_ℂ • b i`. Use function extensionality and compare the values at `y`. Rewrite using `[← b.sum_repr' (ContinuousLinearMap.adjoint (A y) (φ y))]`. Simplify using `only [ContinuousLinearMap.adjoint_inner_right]`.

Rewrite using `[key]`. Conclude with `integrable_finsetSum _ fun i _ => (integrable_inner_of_memLp μ (hA (b i)) hφ).smul_const _`.
-/
theorem integrable_adjoint_apply {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
    {A : G n → (V →L[ℂ] V)} {φ : G n → V} (hA : ∀ v, MemLp (fun y => A y v) 2 μ) (hφ : MemLp φ 2 μ) :
    Integrable (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) μ := by
  classical
  let b := stdOrthonormalBasis ℂ V
  have key : (fun y => ContinuousLinearMap.adjoint (A y) (φ y)) =
      fun y => ∑ i, ⟪A y (b i), φ y⟫_ℂ • b i := by
    funext y
    rw [← b.sum_repr' (ContinuousLinearMap.adjoint (A y) (φ y))]
    simp only [ContinuousLinearMap.adjoint_inner_right]
  rw [key]
  exact integrable_finsetSum _ fun i _ => (integrable_inner_of_memLp μ (hA (b i)) hφ).smul_const _

/- English proof (translation)
Introduce `n _ _ μ _ E _ Ω T F c hStd h A hRow f hf hCpt f' hSob' hSec' hcls x hx`. Establish `hStd0` using `hStd`. Take `⟨hLg, hUni, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, -⟩` from `hStd0`. Take `⟨-, -, -, -, -, -, hCptSob, -⟩` from `hCS`. Establish `hdet : x.det ≠ 0` using `hx`.

Set `x₀ : G n` to `Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet`. Establish `hx₀ : x₀.val = x` using `rfl`. Establish `hfS : Sob μ f` using `(hCptSob n μ E.V hLg hRC f hf.1 hCpt).1`. Establish `hmul : ∀ g ∈ GLs n, x * g ∈ GLs n` using `fun g hg => by`. Establish `hg' : g.det ≠ 0` using `hg`.

Use `show (x * g).det ≠ 0`. Rewrite using `[Matrix.det_mul]`. Conclude with `mul_ne_zero hdet hg'`. Establish `hφS : Sob μ (lTr x₀ f)` using `(hLt n μ E.V hLg hUni hRC x₀ f hfS).1`. Establish `hψS : Sob μ (lTr x₀ f')` using `(hLt n μ E.V hLg hUni hRC x₀ f' hSob').1`.

Establish `hφE : IsSec E (lTr x₀ f)` using `fun g hg k => by show f (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f (x₀.val * g))`. Rewrite using `[hx₀, ← mul_assoc]`. Conclude with `hf.2 _ (hmul g hg) k`. Establish `hψE : IsSec E (lTr x₀ f')` using `fun g hg k => by show f' (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f' (x₀.val * g))`. Rewrite using `[hx₀, ← mul_assoc]`.

Conclude with `hSec' _ (hmul g hg) k`. Establish `hclsT : cls μ (lTr x₀ f') = F.Φ h (cls μ (lTr x₀ f))` using `hComm n μ E Ω T F c hStd h x₀ f f' hfS hSob' hcls`. Establish `hφL : MemLp (fun y : G n => lTr x₀ f y.val) 2 μ` using `hφS.2 []`. Establish `hAL : ∀ v, MemLp (fun y : G n => A y.val v) 2 μ` using `fun v => (hRow v).1.2 []`. Establish `hint : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (lTr x₀ f y.val)) μ` using `integrable_adjoint_apply μ (A := fun y : G n => A y.val) hAL hφL`.

Use `ext_inner_left ℂ fun v => ?_` and prove the remaining obligations. Establish `hrow` using `(hRow v).2.2 (lTr x₀ f) (lTr x₀ f') hφS hφE hψS hψE hclsT`. Rewrite `hrow` using `[inner_cls_eq μ (hAL v) hφL]`. Establish `hval : lTr x₀ f' 1 = f' x` using `by show f' (x₀.val * 1) = f' x`. Rewrite using `[hx₀, mul_one]`.

Rewrite `hrow` using `[hval]`. Rewrite using `[← hrow]`. Use `show ⟪v, ∫ y : G n, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val)) ∂μ⟫_ℂ = _`. Establish `hint' : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))) μ` using `hint`. Rewrite using `[← integral_inner hint' v]`.

Use `integral_congr_ae (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Use `show ⟪v, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))⟫_ℂ = ⟪A y.val v, f (x₀.val * y.val)⟫_ℂ`. Rewrite using `[hx₀, ContinuousLinearMap.adjoint_inner_right]`.
-/
theorem actFormula (hLt : LtSob) (hComm : LtComm) : ActFormula := by
  intro n _ _ μ _ E _ Ω T F c hStd h A hRow f hf hCpt f' hSob' hSec' hcls x hx
  have hStd0 := hStd
  obtain ⟨hLg, hUni, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, -⟩ := hStd0
  obtain ⟨-, -, -, -, -, -, hCptSob, -⟩ := hCS
  have hdet : x.det ≠ 0 := hx
  let x₀ : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hdet
  have hx₀ : x₀.val = x := rfl
  have hfS : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hCpt).1
  have hmul : ∀ g ∈ GLs n, x * g ∈ GLs n := fun g hg => by
    have hg' : g.det ≠ 0 := hg
    show (x * g).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero hdet hg'
  have hφS : Sob μ (lTr x₀ f) := (hLt n μ E.V hLg hUni hRC x₀ f hfS).1
  have hψS : Sob μ (lTr x₀ f') := (hLt n μ E.V hLg hUni hRC x₀ f' hSob').1
  have hφE : IsSec E (lTr x₀ f) := fun g hg k => by
    show f (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hf.2 _ (hmul g hg) k
  have hψE : IsSec E (lTr x₀ f') := fun g hg k => by
    show f' (x₀.val * (g * k.1)) = E.ρ k⁻¹ (f' (x₀.val * g))
    rw [hx₀, ← mul_assoc]
    exact hSec' _ (hmul g hg) k
  have hclsT : cls μ (lTr x₀ f') = F.Φ h (cls μ (lTr x₀ f)) :=
    hComm n μ E Ω T F c hStd h x₀ f f' hfS hSob' hcls
  have hφL : MemLp (fun y : G n => lTr x₀ f y.val) 2 μ := hφS.2 []
  have hAL : ∀ v, MemLp (fun y : G n => A y.val v) 2 μ := fun v => (hRow v).1.2 []
  have hint : Integrable
      (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (lTr x₀ f y.val)) μ :=
    integrable_adjoint_apply μ (A := fun y : G n => A y.val) hAL hφL
  refine ext_inner_left ℂ fun v => ?_
  have hrow := (hRow v).2.2 (lTr x₀ f) (lTr x₀ f') hφS hφE hψS hψE hclsT
  rw [inner_cls_eq μ (hAL v) hφL] at hrow
  have hval : lTr x₀ f' 1 = f' x := by
    show f' (x₀.val * 1) = f' x
    rw [hx₀, mul_one]
  rw [hval] at hrow
  rw [← hrow]
  show ⟪v, ∫ y : G n, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val)) ∂μ⟫_ℂ = _
  have hint' : Integrable (fun y : G n => ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))) μ := hint
  rw [← integral_inner hint' v]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  show ⟪v, ContinuousLinearMap.adjoint (A y.val) (f (x * y.val))⟫_ℂ = ⟪A y.val v, f (x₀.val * y.val)⟫_ℂ
  rw [hx₀, ContinuousLinearMap.adjoint_inner_right]

end GlobalTheory.CompanionTheory.KerFc
