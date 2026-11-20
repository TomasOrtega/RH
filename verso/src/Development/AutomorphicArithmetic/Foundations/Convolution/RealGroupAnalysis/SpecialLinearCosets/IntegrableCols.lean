import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.CompCoordMem
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.JmMeasurable
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.PsiLaws

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

variable {F : Type} [Field F] [NumberField F] {v : P F}

private def colsH : ((Fin 2 → Kv v) × (Fin 2 → Kv v)) ≃ₜ M2 v where
  toFun p := cols p.1 p.2
  invFun m := (fun i => m i 0, fun i => m i 1)
  left_inv p := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;> simp [cols]
  right_inv m := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [cols]
  continuous_toFun := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [cols] <;> simp <;> fun_prop
  continuous_invFun :=
    (continuous_pi fun i => continuous_id.matrix_elem i 0).prodMk
      (continuous_pi fun i => continuous_id.matrix_elem i 1)

/- English proof (translation)
Use `haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance`. Establish `hc : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2)` using `hb.1.continuous.comp (colsH (v := v)).continuous`. Establish `hs : HasCompactSupport fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2)` using `hb.2.comp_homeomorph (colsH (v := v))`. Conclude with `(hc.mul hg).integrable_of_hasCompactSupport hs.mul_right`.
-/
private theorem integrable_cols {b : M2 v → ℂ} (hb : b ∈ SB (M2 v)) {g : (Fin 2 → Kv v) × (Fin 2 → Kv v) → ℂ}
    (hg : Continuous g) :
    Integrable (fun p => b (cols p.1 p.2) * g p) ((μ2 v).prod (μ2 v)) := by
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hc : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2) :=
    hb.1.continuous.comp (colsH (v := v)).continuous
  have hs : HasCompactSupport fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => b (cols p.1 p.2) :=
    hb.2.comp_homeomorph (colsH (v := v))
  exact (hc.mul hg).integrable_of_hasCompactSupport hs.mul_right

end UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

namespace UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

variable {F : Type} [Field F] [NumberField F] {v : P F}

/- English proof (translation)
Establish `h` using `(UpperTheory.ConvolutionTheory.R2.I.ptInv F v a ha).1 (cols e c)`. Use `Eq.trans ?_ h` and prove the remaining obligations. Establish `hP : ∀ (g : M2 v → ℂ) (Y : M2 v), Pt g Y = ∫ c', g (cols (fun i => Y i 1) c') * ψl v (Y 0 0 * c' 1 - Y 1 0 * c' 0) ∂(μ2 v)` using `fun _ _ => rfl`. Rewrite using `[hP (fun X => Pt a (sw X))]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations.

Establish `h1 : (fun i => sw (cols e c) i 1) = e`. Apply the tactic sequence `funext i; fin_cases i <;> simp [sw, cols]`. Establish `h2 : ∀ y : Fin 2 → Kv v, sw (cols e y) = cols y e`. Apply the tactic sequence `intro y; ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]`. Establish `h3 : sw (cols e c) 0 0 = c 0` using `by simp [sw, cols]`.

Establish `h4 : sw (cols e c) 1 0 = c 1` using `by simp [sw, cols]`. Simplify using `only [h1, h3, h4]`. Rewrite using `[h2]`.
-/
private theorem inv_col {a : M2 v → ℂ} (ha : a ∈ SB (M2 v)) (e c : Fin 2 → Kv v) :
    ∫ e₁, Pt a (cols e₁ e) * ψl v (c 0 * e₁ 1 - c 1 * e₁ 0) ∂(μ2 v) = a (cols e c) := by
  have h := (UpperTheory.ConvolutionTheory.R2.I.ptInv F v a ha).1 (cols e c)
  refine Eq.trans ?_ h
  have hP : ∀ (g : M2 v → ℂ) (Y : M2 v), Pt g Y =
      ∫ c', g (cols (fun i => Y i 1) c') * ψl v (Y 0 0 * c' 1 - Y 1 0 * c' 0) ∂(μ2 v) := fun _ _ => rfl
  rw [hP (fun X => Pt a (sw X))]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have h1 : (fun i => sw (cols e c) i 1) = e := by
    funext i; fin_cases i <;> simp [sw, cols]
  have h2 : ∀ y : Fin 2 → Kv v, sw (cols e y) = cols y e := by
    intro y; ext i j; fin_cases i <;> fin_cases j <;> simp [sw, cols]
  have h3 : sw (cols e c) 0 0 = c 0 := by simp [sw, cols]
  have h4 : sw (cols e c) 1 0 = c 1 := by simp [sw, cols]
  simp only [h1, h3, h4]
  rw [h2]

/- English proof (translation)
Use `fun_prop`.
-/
private theorem cont_lin {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (s t u w : R) :
    Continuous fun p : (Fin 2 → R) × (Fin 2 → R) => (s * p.2 0 - t * p.2 1) + (u * p.1 1 - w * p.1 0) := by
  fun_prop

/- English proof (translation)
Simplify using `[BM, cols]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem bm_cols (X : M2 v) (x e : Fin 2 → Kv v) :
    BM (cols x e) X = (X 1 0 * e 0 - X 0 0 * e 1) + (X 0 1 * x 1 - X 1 1 * x 0) := by
  simp [BM, cols]; ring

/- English proof (translation)
Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [cols, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem cols_mul_w (c c' : Fin 2 → Kv v) :
    cols c c' * !![0, 1; -1, 0] = cols (-c') c := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [cols, Matrix.mul_apply, Fin.sum_univ_two]

end UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability

open UpperTheory.ConvolutionTheory.R2.I.ColumnIntegrability in
/- English proof (translation)
Introduce `F _ _ v a ha X`. Take `⟨T, hT⟩` from `UpperTheory.ConvolutionTheory.R2.I.ptMem F v`. Establish `hb : Pt a ∈ SB (M2 v)`. Use `(T ⟨a, ha⟩).2` as an intermediate fact. Rewrite `this` using `[hT ⟨a, ha⟩]`. Then use the resulting hypothesis.

Take `⟨-, -, hadd, hlc, -, -⟩` from `UpperTheory.ConvolutionTheory.R2.I.psiLaws F v`. Use `haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance`. Establish `hcont : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => ψl v (BM (cols p.1 p.2) X)`. Simplify using `only [bm_cols]`. Conclude with `hlc.continuous.comp (cont_lin _ _ _ _)`.

Establish `hint` using `integrable_cols hb hcont`. Unfold `IM`. Rewrite using `[integral_prod_symm _ hint]`. Use `set c : Fin 2 → Kv v := fun i => X i 1 with hc`. Establish `hin : ∀ e : Fin 2 → Kv v, ∫ e₁, Pt a (cols e₁ e) * ψl v (BM (cols e₁ e) X) ∂(μ2 v) = ψl v (X 1 0 * e 0 - X 0 0 * e 1) * a (cols e c)`.

Introduce `e`. Rewrite using `[← inv_col ha e c, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `beta_reduce`. Establish `hc0 : c 0 = X 0 1` using `rfl`.

Establish `hc1 : c 1 = X 1 1` using `rfl`. Rewrite using `[bm_cols, hadd, hc0, hc1]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hin]`. Rewrite using `[← integral_neg_eq_self]`.

Simplify using `only [Pt]`. Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[cols_mul_w]`. Establish `: X 1 0 * (-x) 0 - X 0 0 * (-x) 1 = X 0 0 * x 1 - X 1 0 * x 0` using `by simp; ring`.

Rewrite using `[this]`. Conclude with `mul_comm _ _`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.ptW :
    ∀ (F : Type) [Field F] [NumberField F] (v : P F), ∀ a ∈ SB (M2 v), ∀ X, IM (fun Y => Pt a Y * ψl v (BM Y X)) = Pt (fun m => a (m * !![0, 1; -1, 0])) X := by
  intro F _ _ v a ha X
  obtain ⟨T, hT⟩ := UpperTheory.ConvolutionTheory.R2.I.ptMem F v
  have hb : Pt a ∈ SB (M2 v) := by
    have := (T ⟨a, ha⟩).2
    rwa [hT ⟨a, ha⟩] at this
  obtain ⟨-, -, hadd, hlc, -, -⟩ := UpperTheory.ConvolutionTheory.R2.I.psiLaws F v
  haveI : (μ2 v).IsAddHaarMeasure := by unfold μ2; infer_instance
  have hcont : Continuous fun p : (Fin 2 → Kv v) × (Fin 2 → Kv v) => ψl v (BM (cols p.1 p.2) X) := by
    simp only [bm_cols]
    exact hlc.continuous.comp (cont_lin _ _ _ _)
  have hint := integrable_cols hb hcont
  unfold IM
  rw [integral_prod_symm _ hint]
  set c : Fin 2 → Kv v := fun i => X i 1 with hc
  have hin : ∀ e : Fin 2 → Kv v,
      ∫ e₁, Pt a (cols e₁ e) * ψl v (BM (cols e₁ e) X) ∂(μ2 v) =
        ψl v (X 1 0 * e 0 - X 0 0 * e 1) * a (cols e c) := by
    intro e
    rw [← inv_col ha e c, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    have hc0 : c 0 = X 0 1 := rfl
    have hc1 : c 1 = X 1 1 := rfl
    rw [bm_cols, hadd, hc0, hc1]
    ring
  simp only [hin]
  rw [← integral_neg_eq_self]
  simp only [Pt]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [cols_mul_w]
  have : X 1 0 * (-x) 0 - X 0 0 * (-x) 1 = X 0 0 * x 1 - X 1 0 * x 0 := by
    simp; ring
  rw [this]
  exact mul_comm _ _
