import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses

open MeasureTheory Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.Ux13

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

/- English proof (translation)
Establish `hint : ∀ m ≤ q, ∀ x, Integrable (fun a => ph a x m) μ` using `fun m hm x => hb.mono' (hmeas m hm x) (Filter.Eventually.of_forall fun a => hle m hm a x)`. Use `⟨fun x => ?_, fun m hm x => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Establish `h0` using `hint 0 (Nat.zero_le _) x show (∫ a, ph a x 0 ∂μ) 0 = ∫ a, H a x ∂μ`. Rewrite using `[ContinuousMultilinearMap.integral_apply h0]`. Conclude with `integral_congr_ae (Filter.Eventually.of_forall fun a => (hT a).zero_eq x)`.

Establish `hmq' : m < q` using `by exact_mod_cast hm`. Establish `hm' : m + 1 ≤ q` using `hmq'`. Establish `hmq : m ≤ q` using `hmq'.le`. Establish `key` using `hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (s := Set.univ) (x₀ := x) (F := fun y a => ph a y m) (F' := fun y a => (ph a y (m + 1)).curryLeft) (bound := bound) Filter.univ_mem (Filter.Eventually.of_forall fun y => hmeas m hmq y) (hint m hmq x) ((continuousMultilinearC …`. Establish `hn` using `(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).norm_map (ph a y (m + 1))`.

Conclude with `(le_of_eq hn).trans (hle (m + 1) hm' a y))`. Use `hb (Filter.Eventually.of_forall fun a y _ => (hT a).fderiv m hm y)`. Establish `hc` using `(continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).toContinuousLinearEquiv.integral_comp_comm (μ := μ) (fun a => ph a x (m + 1))`. Conclude with `key.congr_fderiv hc`. Establish `hmq : m ≤ q` using `by exact_mod_cast hm`.

Conclude with `continuous_of_dominated (fun x => hmeas m hmq x) (fun x => Filter.Eventually.of_forall fun a => hle m hmq a x) hb (Filter.Eventually.of_forall fun a => (hT a).cont m hm)`.
-/
theorem taylor_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {q : ℕ} (H : α → X → W) (ph : α → X → FormalMultilinearSeries ℝ X W)
    (hT : ∀ a, HasFTaylorSeriesUpTo q (H a) (ph a))
    (hmeas : ∀ m ≤ q, ∀ x, AEStronglyMeasurable (fun a => ph a x m) μ)
    (bound : α → ℝ) (hb : Integrable bound μ) (hle : ∀ m ≤ q, ∀ a x, ‖ph a x m‖ ≤ bound a) :
    HasFTaylorSeriesUpTo q (fun x => ∫ a, H a x ∂μ) (fun x m => ∫ a, ph a x m ∂μ) := by
  have hint : ∀ m ≤ q, ∀ x, Integrable (fun a => ph a x m) μ := fun m hm x =>
    hb.mono' (hmeas m hm x) (Filter.Eventually.of_forall fun a => hle m hm a x)
  refine ⟨fun x => ?_, fun m hm x => ?_, fun m hm => ?_⟩
  · have h0 := hint 0 (Nat.zero_le _) x
    show (∫ a, ph a x 0 ∂μ) 0 = ∫ a, H a x ∂μ
    rw [ContinuousMultilinearMap.integral_apply h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => (hT a).zero_eq x)
  · have hmq' : m < q := by exact_mod_cast hm
    have hm' : m + 1 ≤ q := hmq'
    have hmq : m ≤ q := hmq'.le
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ) (s := Set.univ) (x₀ := x)
      (F := fun y a => ph a y m) (F' := fun y a => (ph a y (m + 1)).curryLeft) (bound := bound)
      Filter.univ_mem (Filter.Eventually.of_forall fun y => hmeas m hmq y) (hint m hmq x)
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).continuous.comp_aestronglyMeasurable
        (hmeas (m + 1) hm' x))
      (Filter.Eventually.of_forall fun a y _ => by
        have hn := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).norm_map (ph a y (m + 1))
        exact (le_of_eq hn).trans (hle (m + 1) hm' a y))
      hb (Filter.Eventually.of_forall fun a y _ => (hT a).fderiv m hm y)
    have hc := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => X) W).toContinuousLinearEquiv.integral_comp_comm
      (μ := μ) (fun a => ph a x (m + 1))
    exact key.congr_fderiv hc
  · have hmq : m ≤ q := by exact_mod_cast hm
    exact continuous_of_dominated (fun x => hmeas m hmq x)
      (fun x => Filter.Eventually.of_forall fun a => hle m hmq a x) hb
      (Filter.Eventually.of_forall fun a => (hT a).cont m hm)

/- English proof (translation)
Unfold `blk2`. Rewrite using `[← Matrix.fromBlocks_add]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem block2_add {p s : ℕ} (A A' : Matrix (Fin p) (Fin p) ℂ) (B B' : Matrix (Fin p) (Fin s) ℂ)
    (C C' : Matrix (Fin s) (Fin p) ℂ) (D D' : Matrix (Fin s) (Fin s) ℂ) :
    blk2 A B C D + blk2 A' B' C' D' = blk2 (A + A') (B + B') (C + C') (D + D') := by
  unfold blk2
  rw [← Matrix.fromBlocks_add]
  ext i j
  simp

/- English proof (translation)
Unfold `blk2`. Rewrite using `[← Matrix.fromBlocks_smul]`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem smul_block_two {p s : ℕ} (r : ℝ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ)
    (C : Matrix (Fin s) (Fin p) ℂ) (D : Matrix (Fin s) (Fin s) ℂ) :
    r • blk2 A B C D = blk2 (r • A) (r • B) (r • C) (r • D) := by
  unfold blk2
  rw [← Matrix.fromBlocks_smul]
  ext i j
  simp

def iotaL (p s : ℕ) : G.Mat s →ₗ[ℝ] G.Mat (p + s) where
  toFun CC := Matrix.of.symm (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of CC))
  map_add' x y := by
    have h : (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of (x + y)) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) =
        blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of x) + blk2 0 0 0 (Matrix.of y) := by
      rw [block2_add]; simp
    exact h
  map_smul' r x := by
    have h : (blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of (r • x)) : Matrix (Fin (p + s)) (Fin (p + s)) ℂ) =
        r • blk2 (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (Matrix.of x) := by
      rw [smul_block_two]; simp
    exact h

/- English proof (translation)
Establish `h : ∀ (H : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ) (D Z : Matrix (Fin s) (Fin s) ℂ), blk2 H B C (D + Z) = blk2 H B C (D + 0) + blk2 0 0 0 Z`. Introduce `H B C D Z`. Rewrite using `[block2_add]`. Simplify using the standard rewrite rules. Unfold `ZjH`.

Rewrite using `[hZ, hZ, h _ _ _ _ (Matrix.of CC)]`. Both sides reduce to the same expression.
-/
theorem zjH_split (hZ : ZjAffine) {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : XiH p s σ)
    (CC : G.Mat s) :
    (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Matrix.of.symm (ZjH σ d η 0) + iotaL p s CC := by
  have h : ∀ (H : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin s) ℂ) (C : Matrix (Fin s) (Fin p) ℂ)
      (D Z : Matrix (Fin s) (Fin s) ℂ), blk2 H B C (D + Z) = blk2 H B C (D + 0) + blk2 0 0 0 Z := by
    intro H B C D Z
    rw [block2_add]
    simp
  unfold ZjH
  rw [hZ, hZ, h _ _ _ _ (Matrix.of CC)]
  rfl

/- English proof (translation)
Conclude with `(hA.matrix_fromBlocks hB hC hD).matrix_reindex _ _`.
-/
theorem continuous_block2 {α : Type*} [TopologicalSpace α] {p s : ℕ} {A : α → Matrix (Fin p) (Fin p) ℂ}
    {B : α → Matrix (Fin p) (Fin s) ℂ} {C : α → Matrix (Fin s) (Fin p) ℂ} {D : α → Matrix (Fin s) (Fin s) ℂ}
    (hA : Continuous A) (hB : Continuous B) (hC : Continuous C) (hD : Continuous D) :
    Continuous fun x => blk2 (A x) (B x) (C x) (D x) := by
  exact (hA.matrix_fromBlocks hB hC hD).matrix_reindex _ _

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : b < a ∧ σ.symm b < σ.symm a`. Simplify using `only [lowW, Matrix.add_apply, Matrix.of_apply, dif_pos h]`. Conclude with `continuous_const.add (continuous_apply _)`. Simplify using `only [lowW, Matrix.add_apply, Matrix.of_apply, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_lowW {p : ℕ} (σ : Equiv.Perm (Fin p)) : Continuous (lowW σ) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : b < a ∧ σ.symm b < σ.symm a
  · simp only [lowW, Matrix.add_apply, Matrix.of_apply, dif_pos h]
    exact continuous_const.add (continuous_apply _)
  · simp only [lowW, Matrix.add_apply, Matrix.of_apply, dif_neg h]
    exact continuous_const

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h : a < b`. Simplify using `only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_pos h]`. Conclude with `continuous_const.add (continuous_apply _)`. Simplify using `only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_upper {p : ℕ} : Continuous (G.upper (d := p)) := by
  refine continuous_matrix fun a b => ?_
  by_cases h : a < b
  · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_pos h]
    exact continuous_const.add (continuous_apply _)
  · simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, dif_neg h]
    exact continuous_const

/- English proof (translation)
Use `show Continuous fun l : Matrix (Fin p) (Fin p) ℂ => subS l`. Unfold `subS`. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i.val + 1 < p`. Simplify using `only [dif_pos h]`.

Conclude with `continuous_id.matrix_elem _ _`. Simplify using `only [dif_neg h]`. Conclude with `continuous_const`.
-/
theorem continuous_subS {p : ℕ} : Continuous (subS (p := p)) := by
  show Continuous fun l : Matrix (Fin p) (Fin p) ℂ => subS l
  unfold subS
  refine continuous_finset_sum _ fun i _ => ?_
  by_cases h : i.val + 1 < p
  · simp only [dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [dif_neg h]
    exact continuous_const

/- English proof (translation)
Use `show Continuous fun l : Matrix (Fin p) (Fin p) ℂ => supS l`. Unfold `supS`. Use `continuous_finset_sum _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i.val + 1 < p`. Simplify using `only [dif_pos h]`.

Conclude with `continuous_id.matrix_elem _ _`. Simplify using `only [dif_neg h]`. Conclude with `continuous_const`.
-/
theorem continuous_supS {p : ℕ} : Continuous (supS (p := p)) := by
  show Continuous fun l : Matrix (Fin p) (Fin p) ℂ => supS l
  unfold supS
  refine continuous_finset_sum _ fun i _ => ?_
  by_cases h : i.val + 1 < p
  · simp only [dif_pos h]
    exact continuous_id.matrix_elem _ _
  · simp only [dif_neg h]
    exact continuous_const

/- English proof (translation)
Use `show Continuous fun a : Fin s → Fin p → ℂ => cornerA a`. Distinguish the cases in `h : 0 < s ∧ 0 < p`. Simplify using `only [cornerA, dif_pos h]`. Conclude with `continuous_apply_apply _ _`. Simplify using `only [cornerA, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_cornerA {p s : ℕ} : Continuous (cornerA (p := p) (s := s)) := by
  show Continuous fun a : Fin s → Fin p → ℂ => cornerA a
  by_cases h : 0 < s ∧ 0 < p
  · simp only [cornerA, dif_pos h]
    exact continuous_apply_apply _ _
  · simp only [cornerA, dif_neg h]
    exact continuous_const

/- English proof (translation)
Use `show Continuous fun b : Fin p → Fin s → ℂ => cornerB b`. Distinguish the cases in `h : 0 < s ∧ 0 < p`. Simplify using `only [cornerB, dif_pos h]`. Conclude with `continuous_apply_apply _ _`. Simplify using `only [cornerB, dif_neg h]`.

Conclude with `continuous_const`.
-/
theorem continuous_cornerB {p s : ℕ} : Continuous (cornerB (p := p) (s := s)) := by
  show Continuous fun b : Fin p → Fin s → ℂ => cornerB b
  by_cases h : 0 < s ∧ 0 < p
  · simp only [cornerB, dif_pos h]
    exact continuous_apply_apply _ _
  · simp only [cornerB, dif_neg h]
    exact continuous_const

/- English proof (translation)
Establish `h1 : Continuous fun η : XiH p s σ => subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹)` using `continuous_subS.comp ((continuous_const.matrix_mul ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul continuous_const)`. Establish `h2 : Continuous fun η : XiH p s σ => supS (G.upper η.2.2)` using `continuous_supS.comp (continuous_upper.comp (continuous_snd.comp continuous_snd))`. Establish `h3 : Continuous fun η : XiH p s σ => cornerA η.1.1` using `continuous_cornerA.comp (continuous_fst.comp continuous_fst)`. Establish `h4 : Continuous fun η : XiH p s σ => cornerB η.1.2` using `continuous_cornerB.comp (continuous_snd.comp continuous_fst)`. Simplify using `only [psiH, G.psi]`.

Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul (((h1.add h2).add h3).add h4)))))`.
-/
theorem continuous_psiH {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) :
    Continuous fun η : XiH p s σ => psiH β σ η := by
  have h1 : Continuous fun η : XiH p s σ => subS (wP σ * lowW σ η.2.1 * (wP σ)⁻¹) :=
    continuous_subS.comp ((continuous_const.matrix_mul
      ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul continuous_const)
  have h2 : Continuous fun η : XiH p s σ => supS (G.upper η.2.2) :=
    continuous_supS.comp (continuous_upper.comp (continuous_snd.comp continuous_snd))
  have h3 : Continuous fun η : XiH p s σ => cornerA η.1.1 :=
    continuous_cornerA.comp (continuous_fst.comp continuous_fst)
  have h4 : Continuous fun η : XiH p s σ => cornerB η.1.2 :=
    continuous_cornerB.comp (continuous_snd.comp continuous_fst)
  simp only [psiH, G.psi]
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_const.mul (((h1.add h2).add h3).add h4)))))

/- English proof (translation)
Establish `hof1 : Continuous fun η : XiH p s σ => (Matrix.of η.1.1 : Matrix (Fin s) (Fin p) ℂ)` using `continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_fst.comp continuous_fst)`. Establish `hof2 : Continuous fun η : XiH p s σ => (Matrix.of η.1.2 : Matrix (Fin p) (Fin s) ℂ)` using `continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_snd.comp continuous_fst)`. Establish `hH : Continuous fun η : XiH p s σ => headH σ d η.2.1 η.2.2`. Unfold `headH`. Conclude with `((continuous_const.matrix_mul ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul continuous_const).matrix_mul (continuous_upper.comp (continuous_snd.comp continuous_snd))`.

Establish `hZ : Continuous fun η : XiH p s σ => ZjH σ d η CC`. Unfold `ZjH Zj`. Conclude with `((continuous_block2 continuous_const continuous_const hof1 continuous_const).matrix_mul (continuous_block2 hH continuous_const continuous_const continuous_const)).matrix_mul (continuous_block2 continuous_const hof2 continuous_const continuous_const)`. Conclude with `hZ`.
-/
theorem continuous_zjH {p s : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (CC : G.Mat s) :
    Continuous fun η : XiH p s σ => (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) := by
  have hof1 : Continuous fun η : XiH p s σ => (Matrix.of η.1.1 : Matrix (Fin s) (Fin p) ℂ) :=
    continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_fst.comp continuous_fst)
  have hof2 : Continuous fun η : XiH p s σ => (Matrix.of η.1.2 : Matrix (Fin p) (Fin s) ℂ) :=
    continuous_matrix fun i j => (continuous_apply_apply i j).comp (continuous_snd.comp continuous_fst)
  have hH : Continuous fun η : XiH p s σ => headH σ d η.2.1 η.2.2 := by
    unfold headH
    exact ((continuous_const.matrix_mul ((continuous_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul
      continuous_const).matrix_mul (continuous_upper.comp (continuous_snd.comp continuous_snd))
  have hZ : Continuous fun η : XiH p s σ => ZjH σ d η CC := by
    unfold ZjH Zj
    exact ((continuous_block2 continuous_const continuous_const hof1 continuous_const).matrix_mul
      (continuous_block2 hH continuous_const continuous_const continuous_const)).matrix_mul
      (continuous_block2 continuous_const hof2 continuous_const continuous_const)
  exact hZ

def iotaC (p s : ℕ) : G.Mat s →L[ℝ] G.Mat (p + s) := LinearMap.toContinuousLinearMap (iotaL p s)

def gA {p s : ℕ} (T : G.Mat (p + s)) : G.Mat s →ᴬ[ℝ] G.Mat (p + s) where
  toFun x := T + iotaC p s x
  linear := iotaL p s
  map_vadd' x v := by
    show T + iotaL p s (v + x) = iotaL p s v + (T + iotaL p s x)
    rw [map_add]; abel
  cont := continuous_const.add (iotaC p s).continuous

def Lc {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ) : V →L[ℝ] V :=
  (c • ContinuousLinearMap.id ℂ V).restrictScalars ℝ

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Lc_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (c : ℂ) (v : V) : Lc c v = c • v := rfl

/- English proof (translation)
Simplify using `only [psiH, G.psi]`. Rewrite using `[mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_psiH {p s : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin p)) (η : XiH p s σ) : ‖psiH β σ η‖ = 1 := by
  simp only [psiH, G.psi]
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/- English proof (translation)
Unfold `wtH`. Check the signs of the components of the expression.
-/
theorem wtH_pos {p s : ℕ} {σ : Equiv.Perm (Fin p)} (η : XiH p s σ) : 0 < wtH η := by
  unfold wtH
  positivity

/- English proof (translation)
Establish `hm' : ((m : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞)` using `by exact_mod_cast hm`. Establish `h1 : ContDiff ℝ q (fun z => f (T + z))` using `hf.comp (contDiff_const.add contDiff_id)`. Establish `h2 : ContDiff ℝ q ((fun z => f (T + z)) ∘ ι)` using `h1.comp ι.contDiff`. Establish `e1` using `L.iteratedFDeriv_comp_left (h2.contDiffAt (x := x)) hm'`. Establish `e2` using `ι.iteratedFDeriv_comp_right h1 x hm'`.

Establish `e3` using `iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) m T (ι x)`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem iter_lemma {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {q : ℕ} {f : Y → V} (hf : ContDiff ℝ q f) (L : V →L[ℝ] V) (T : Y) (ι : X →L[ℝ] Y)
    {m : ℕ} (hm : m ≤ q) (x : X) :
    iteratedFDeriv ℝ m (fun y => L (f (T + ι y))) x =
      L.compContinuousMultilinearMap ((iteratedFDeriv ℝ m f (T + ι x)).compContinuousLinearMap fun _ => ι) := by
  have hm' : ((m : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞) := by exact_mod_cast hm
  have h1 : ContDiff ℝ q (fun z => f (T + z)) := hf.comp (contDiff_const.add contDiff_id)
  have h2 : ContDiff ℝ q ((fun z => f (T + z)) ∘ ι) := h1.comp ι.contDiff
  have e1 := L.iteratedFDeriv_comp_left (h2.contDiffAt (x := x)) hm'
  have e2 := ι.iteratedFDeriv_comp_right h1 x hm'
  have e3 := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) m T (ι x)
  calc iteratedFDeriv ℝ m (fun y => L (f (T + ι y))) x
      = L.compContinuousMultilinearMap (iteratedFDeriv ℝ m ((fun z => f (T + z)) ∘ ι) x) := e1
    _ = _ := by rw [e2, e3]

/- English proof (translation)
Introduce `p s β σ d hd hs q e he`. Use `haveI i1 : OpensMeasurableSpace (Fin s → Fin p → ℂ) := inferInstance`. Use `haveI i2 : OpensMeasurableSpace (Fin p → Fin s → ℂ) := inferInstance`. Use `haveI i3 : OpensMeasurableSpace (LW σ → ℂ) := inferInstance`. Use `haveI i4 : OpensMeasurableSpace (G.UT p → ℂ) := inferInstance`.

Use `haveI i5 : SecondCountableTopology (Fin s → Fin p → ℂ) := inferInstance`. Use `haveI i6 : SecondCountableTopology (Fin p → Fin s → ℂ) := inferInstance`. Use `haveI i7 : SecondCountableTopology (LW σ → ℂ) := inferInstance`. Use `haveI i8 : SecondCountableTopology (G.UT p → ℂ) := inferInstance`. Use `haveI i9 : OpensMeasurableSpace ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance`.

Use `haveI i10 : OpensMeasurableSpace ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance`. Use `haveI i11 : SecondCountableTopology ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance`. Use `haveI i12 : SecondCountableTopology ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance`. Use `haveI : OpensMeasurableSpace (XiH p s σ) := inferInstance`. Establish `hN : (1 : ℝ) ≤ ((p + s : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ p + s)`.

Establish `h5N : (0 : ℝ) < 5 * ((p + s : ℕ) : ℝ)` using `by positivity`. Establish `hepos : ∀ i ≤ q, 0 ≤ e i`. Introduce `i hi`. Establish `h1` using `he i hi`. Establish `h2 : (0 : ℝ) ≤ 2 * ((p + s : ℕ) : ℝ) ^ 2` using `by positivity`.

Establish `h3 : 0 < e i / (5 * ((p + s : ℕ) : ℝ))` using `by linarith`. Conclude with `le_of_lt ((div_pos_iff_of_pos_right h5N).mp h3)`. Use `choose C hC using fun i : ℕ => hST p s σ d hd hs (max (e i) 0) (le_max_right _ _)`. Take `⟨Tm, hTm⟩ : ∃ Tm : XiH p s σ → G.Mat (p + s), Tm = fun η => Matrix.of.symm (ZjH σ d η 0)` from `⟨_, rfl⟩`. Establish `hTc : Continuous Tm` using `by rw [hTm]; exact continuous_zjH σ d 0`.

Establish `hsplit : ∀ (η : XiH p s σ) (CC : G.Mat s), (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Tm η + iotaC p s CC`. Introduce `η CC`. Rewrite using `[hTm]`. Conclude with `zjH_split hZ σ d η CC`. Use `⟨∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * |C k| * ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ), ?_⟩` and prove the remaining obligations.

Introduce `V _ _ _ Φ0 K hΦ`. Unfold `DecayAll at hΦ ⊢`. Take `⟨hcd, hbd⟩` from `hΦ`. Establish `hK : 0 ≤ K`. Establish `h` using `hbd 0 (Nat.zero_le _) 0`.

Establish `h'` using `(norm_nonneg _).trans h`. Simplify using `using h'`. Establish `hexp : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s), iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x = (Lc (psiH β σ η)).compContinuousMultilinearMap ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s)` using `fun m hm η x => iter_lemma hcd (Lc (psiH β σ η)) (Tm η) (iotaC p s) hm x`. Establish `hLc : ∀ η : XiH p s σ, ‖(Lc (psiH β σ η) : V →L[ℝ] V)‖ ≤ 1`. Introduce `η`.

Use `ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_` and prove the remaining obligations. Rewrite using `[Lc_apply, norm_smul, norm_psiH, one_mul]`. Establish `hpt : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s), ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤ ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))`. Introduce `m hm η x`. Rewrite using `[hexp m hm η x]`.

Establish `h1` using `ContinuousLinearMap.norm_compContinuousMultilinearMap_le (Lc (psiH β σ η) : V →L[ℝ] V) ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s)`. Establish `h2` using `ContinuousMultilinearMap.norm_compContinuousLinearMap_le (iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)) (fun _ : Fin m => iotaC p s)`. Rewrite `h2` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Establish `h3` using `hbd m hm (Tm η + iotaC p s x)`. Establish `hmx : mx (ZjH σ d η x) = ‖Tm η + iotaC p s x‖`.

Unfold `mx`. Rewrite using `[hsplit]`. Establish `h4` using `hC m η x`. Rewrite `h4` using `[max_eq_left (hepos m hm), hmx]`. Establish `hw` using `wtH_pos η`.

Establish `h5 : (wtH η * (1 + ‖x‖)) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) = wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))` using `Real.mul_rpow hw.le (by positivity)`. Rewrite `h4` using `[h5]`. Establish `hA : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))` using `by positivity`. Establish `hCabs : C m * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) ≤ |C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))))` using `mul_le_mul_of_nonneg_right (le_abs_self _) hA`. Establish `hι : 0 ≤ ‖iotaC p s‖ ^ m` using `by positivity`.

Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul_of_nonneg_left ?_ zero_le_one` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right h3 hι`. Use `_ ≤ 1 * ((K * (|C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))))) * ‖iotaC p s‖ ^ m) := by`. Use `mul_le_mul_of_nonneg_left ?_ zero_le_one` and prove the remaining obligations.

Use `mul_le_mul_of_nonneg_right ?_ hι` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (h4.trans hCabs) hK`. Use `_ = _ := by ring`. Establish `hmeasI : ∀ m ≤ q, ∀ x : G.Mat s, AEStronglyMeasurable (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) (muXiH p s σ)`. Introduce `m hm x`.

Establish `hfun : (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) = fun η => psiH β σ η • ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s)`. Use function extensionality and compare the values at `η`. Rewrite using `[hexp m hm η x]`. Use extensionality with `v`. Both sides reduce to the same expression.

Rewrite using `[hfun]`. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Use `(continuous_psiH β σ).smul ?_` and prove the remaining obligations. Conclude with `(ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => iotaC p s)).continuous.comp ((hcd.continuous_iteratedFDeriv (by exact_mod_cast hm)).comp (hTc.add continuous_const))`. Establish `hbndI : Integrable (fun η : XiH p s σ => ∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ)` using `integrable_finset_sum _ fun k hk => by`.

Establish `hkq : k ≤ q` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Conclude with `(hIT p s σ _ (he k hkq)).const_mul _`. Establish `hle : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s), ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤ ∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ))))`. Introduce `m hm η x`. Use `(hpt m hm η x).trans ?_` and prove the remaining obligations.

Establish `hx1 : (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (neg_nonpos.mpr (div_nonneg (hepos m hm) h5N.le))`. Establish `h0 : 0 ≤ ‖iotaC p s‖ ^ m * K * |C m|` using `mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _)`. Establish `hw : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))` using `Real.rpow_nonneg (wtH_pos η).le _`. Establish `hterm : ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤ ‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hterm.trans (Finset.single_le_sum (f := fun k => ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ))))) (fun k _ => mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _)) (Real.rpow_nonneg (wtH_pos η).le _)) (Finset.mem_range.mpr (Nat.lt_succ_of …`. Establish `hTI` using `taylor_integral (μ := muXiH p s σ) (q := q) (fun η x => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x))) (fun η x m => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) (fun η => ContDiff.ftaylorSeries (by`. Conclude with `(Lc (psiH β σ η) : V →L[ℝ] V).contDiff.comp ((hcd.comp (contDiff_const.add contDiff_id)).comp (iotaC p s).contDiff)))`. Use `hmeasI _ hbndI hle`. Establish `hPhi : PhiTop β σ d Φ0 = fun x => ∫ η, Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x)) ∂(muXiH p s σ)`.

Use function extensionality and compare the values at `x`. Unfold `PhiTop`. Use `integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)` and prove the remaining obligations. Use `show psiH β σ η • Φ0 (ZjH σ d η x) = psiH β σ η • Φ0 (Tm η + iotaC p s x)`. Rewrite using `[← hsplit η x]`.

Both sides reduce to the same expression. Use `⟨fun CC => ?_, ?_, fun i hi Z => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun η : XiH p s σ => psiH β σ η • Φ0 (ZjH σ d η CC)` using `(continuous_psiH β σ).smul (hcd.continuous.comp (continuous_zjH σ d CC))`. Use `((hIT p s σ _ (he 0 (Nat.zero_le _))).const_mul (‖iotaC p s‖ ^ 0 * K * |C 0| * (1 + ‖CC‖) ^ (-(e 0 / (5 * ((p + s : ℕ) : ℝ)))))).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun η => ?_)` and prove the remaining obligations. Establish `h` using `hpt 0 (Nat.zero_le _) η CC`.

Rewrite `h` using `[norm_iteratedFDeriv_zero]`. Establish `e1 : Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s CC)) = psiH β σ η • Φ0 (ZjH σ d η CC)`. Rewrite using `[Lc_apply, ← hsplit η CC]`. Both sides reduce to the same expression. Rewrite `h` using `[e1]`.

Conclude with `h`. Rewrite using `[hPhi]`. Conclude with `hTI.contDiff`. Use `beta_reduce`. Establish `hiq : ((i : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞)` using `by exact_mod_cast hi`.

Establish `heq` using `hTI.eq_iteratedFDeriv hiq Z`. Rewrite using `[hPhi, ← heq]`. Use `beta_reduce`. Establish `hI : Integrable (fun η : XiH p s σ => (‖iotaC p s‖ ^ i * K * |C i| * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) * wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ)` using `(hIT p s σ _ (he i hi)).const_mul _`. Use `(norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun η => hpt i hi η Z)).trans ?_` and prove the remaining obligations.

Rewrite using `[integral_const_mul]`. Establish `hsum` using `Finset.single_le_sum (s := Finset.range (q + 1)) (f := fun k => ‖iotaC p s‖ ^ k * |C k| * ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ)) (fun k _ => mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (integral_nonneg fun η => Real.rpow_nonneg (wtH_pos η).le _ …`. Establish `hr : 0 ≤ (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hK) hr`.
-/
theorem topCells_of (hZ : ZjAffine) (hST : SizesTop) (hIT : IntTop) : TopCells := by
  intro p s β σ d hd hs q e he
  haveI i1 : OpensMeasurableSpace (Fin s → Fin p → ℂ) := inferInstance
  haveI i2 : OpensMeasurableSpace (Fin p → Fin s → ℂ) := inferInstance
  haveI i3 : OpensMeasurableSpace (LW σ → ℂ) := inferInstance
  haveI i4 : OpensMeasurableSpace (G.UT p → ℂ) := inferInstance
  haveI i5 : SecondCountableTopology (Fin s → Fin p → ℂ) := inferInstance
  haveI i6 : SecondCountableTopology (Fin p → Fin s → ℂ) := inferInstance
  haveI i7 : SecondCountableTopology (LW σ → ℂ) := inferInstance
  haveI i8 : SecondCountableTopology (G.UT p → ℂ) := inferInstance
  haveI i9 : OpensMeasurableSpace ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance
  haveI i10 : OpensMeasurableSpace ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance
  haveI i11 : SecondCountableTopology ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) := inferInstance
  haveI i12 : SecondCountableTopology ((LW σ → ℂ) × (G.UT p → ℂ)) := inferInstance
  haveI : OpensMeasurableSpace (XiH p s σ) := inferInstance
  have hN : (1 : ℝ) ≤ ((p + s : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ p + s)
  have h5N : (0 : ℝ) < 5 * ((p + s : ℕ) : ℝ) := by positivity
  have hepos : ∀ i ≤ q, 0 ≤ e i := by
    intro i hi
    have h1 := he i hi
    have h2 : (0 : ℝ) ≤ 2 * ((p + s : ℕ) : ℝ) ^ 2 := by positivity
    have h3 : 0 < e i / (5 * ((p + s : ℕ) : ℝ)) := by linarith
    exact le_of_lt ((div_pos_iff_of_pos_right h5N).mp h3)
  choose C hC using fun i : ℕ => hST p s σ d hd hs (max (e i) 0) (le_max_right _ _)
  obtain ⟨Tm, hTm⟩ : ∃ Tm : XiH p s σ → G.Mat (p + s), Tm = fun η => Matrix.of.symm (ZjH σ d η 0) :=
    ⟨_, rfl⟩
  have hTc : Continuous Tm := by rw [hTm]; exact continuous_zjH σ d 0
  have hsplit : ∀ (η : XiH p s σ) (CC : G.Mat s),
      (Matrix.of.symm (ZjH σ d η CC) : G.Mat (p + s)) = Tm η + iotaC p s CC := by
    intro η CC
    rw [hTm]
    exact zjH_split hZ σ d η CC
  refine ⟨∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * |C k| *
      ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ), ?_⟩
  intro V _ _ _ Φ0 K hΦ
  unfold DecayAll at hΦ ⊢
  obtain ⟨hcd, hbd⟩ := hΦ
  have hK : 0 ≤ K := by
    have h := hbd 0 (Nat.zero_le _) 0
    have h' := (norm_nonneg _).trans h
    simpa using h'
  have hexp : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x =
        (Lc (psiH β σ η)).compContinuousMultilinearMap
          ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s) :=
    fun m hm η x => iter_lemma hcd (Lc (psiH β σ η)) (Tm η) (iotaC p s) hm x
  have hLc : ∀ η : XiH p s σ, ‖(Lc (psiH β σ η) : V →L[ℝ] V)‖ ≤ 1 := by
    intro η
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    rw [Lc_apply, norm_smul, norm_psiH, one_mul]
  have hpt : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤
        ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by
    intro m hm η x
    rw [hexp m hm η x]
    have h1 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le (Lc (psiH β σ η) : V →L[ℝ] V)
      ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s)
    have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)) (fun _ : Fin m => iotaC p s)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
    have h3 := hbd m hm (Tm η + iotaC p s x)
    have hmx : mx (ZjH σ d η x) = ‖Tm η + iotaC p s x‖ := by
      unfold mx
      rw [hsplit]
    have h4 := hC m η x
    rw [max_eq_left (hepos m hm), hmx] at h4
    have hw := wtH_pos η
    have h5 : (wtH η * (1 + ‖x‖)) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) = wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) :=
      Real.mul_rpow hw.le (by positivity)
    rw [h5] at h4
    have hA : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by positivity
    have hCabs : C m * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) ≤
        |C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hA
    have hι : 0 ≤ ‖iotaC p s‖ ^ m := by positivity
    calc _ ≤ ‖(Lc (psiH β σ η) : V →L[ℝ] V)‖ *
          ‖(iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s‖ := h1
      _ ≤ 1 * (‖iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)‖ * ‖iotaC p s‖ ^ m) :=
          mul_le_mul (hLc η) h2 (norm_nonneg _) zero_le_one
      _ ≤ 1 * ((K * (1 + ‖Tm η + iotaC p s x‖) ^ (-e m)) * ‖iotaC p s‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_one
          exact mul_le_mul_of_nonneg_right h3 hι
      _ ≤ 1 * ((K * (|C m| * (wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))))) * ‖iotaC p s‖ ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_one
          refine mul_le_mul_of_nonneg_right ?_ hι
          exact mul_le_mul_of_nonneg_left (h4.trans hCabs) hK
      _ = _ := by ring
  have hmeasI : ∀ m ≤ q, ∀ x : G.Mat s, AEStronglyMeasurable
      (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) (muXiH p s σ) := by
    intro m hm x
    have hfun : (fun η : XiH p s σ => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x) =
        fun η => psiH β σ η •
          ((iteratedFDeriv ℝ m Φ0 (Tm η + iotaC p s x)).compContinuousLinearMap fun _ => iotaC p s) := by
      funext η
      rw [hexp m hm η x]
      ext v
      rfl
    rw [hfun]
    refine Continuous.aestronglyMeasurable ?_
    refine (continuous_psiH β σ).smul ?_
    exact (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => iotaC p s)).continuous.comp
      ((hcd.continuous_iteratedFDeriv (by exact_mod_cast hm)).comp (hTc.add continuous_const))
  have hbndI : Integrable (fun η : XiH p s σ => ∑ k ∈ Finset.range (q + 1),
      ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ) :=
    integrable_finset_sum _ fun k hk => by
      have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      exact (hIT p s σ _ (he k hkq)).const_mul _
  have hle : ∀ m ≤ q, ∀ (η : XiH p s σ) (x : G.Mat s),
      ‖iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x‖ ≤
        ∑ k ∈ Finset.range (q + 1), ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) := by
    intro m hm η x
    refine (hpt m hm η x).trans ?_
    have hx1 : (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
        (neg_nonpos.mpr (div_nonneg (hepos m hm) h5N.le))
    have h0 : 0 ≤ ‖iotaC p s‖ ^ m * K * |C m| :=
      mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _)
    have hw : 0 ≤ wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := Real.rpow_nonneg (wtH_pos η).le _
    have hterm : ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) ≤
        ‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by
      calc ‖iotaC p s‖ ^ m * K * |C m| * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))
          = (‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) * (1 + ‖x‖) ^ (-(e m / (5 * ((p + s : ℕ) : ℝ)))) := by ring
        _ ≤ (‖iotaC p s‖ ^ m * K * |C m| * wtH η ^ (-(e m / (5 * ((p + s : ℕ) : ℝ))))) * 1 :=
          mul_le_mul_of_nonneg_left hx1 (mul_nonneg h0 hw)
        _ = _ := mul_one _
    exact hterm.trans (Finset.single_le_sum
      (f := fun k => ‖iotaC p s‖ ^ k * K * |C k| * wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))))
      (fun k _ => mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hK) (abs_nonneg _))
        (Real.rpow_nonneg (wtH_pos η).le _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)))
  have hTI := taylor_integral (μ := muXiH p s σ) (q := q)
    (fun η x => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x)))
    (fun η x m => iteratedFDeriv ℝ m (fun y => Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s y))) x)
    (fun η => ContDiff.ftaylorSeries (by
      exact (Lc (psiH β σ η) : V →L[ℝ] V).contDiff.comp
        ((hcd.comp (contDiff_const.add contDiff_id)).comp (iotaC p s).contDiff)))
    hmeasI _ hbndI hle
  have hPhi : PhiTop β σ d Φ0 =
      fun x => ∫ η, Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s x)) ∂(muXiH p s σ) := by
    funext x
    unfold PhiTop
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show psiH β σ η • Φ0 (ZjH σ d η x) = psiH β σ η • Φ0 (Tm η + iotaC p s x)
    rw [← hsplit η x]
    rfl
  refine ⟨fun CC => ?_, ?_, fun i hi Z => ?_⟩
  · have hc : Continuous fun η : XiH p s σ => psiH β σ η • Φ0 (ZjH σ d η CC) :=
      (continuous_psiH β σ).smul (hcd.continuous.comp (continuous_zjH σ d CC))
    refine ((hIT p s σ _ (he 0 (Nat.zero_le _))).const_mul
      (‖iotaC p s‖ ^ 0 * K * |C 0| * (1 + ‖CC‖) ^ (-(e 0 / (5 * ((p + s : ℕ) : ℝ)))))).mono' hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => ?_)
    have h := hpt 0 (Nat.zero_le _) η CC
    rw [norm_iteratedFDeriv_zero] at h
    have e1 : Lc (psiH β σ η) (Φ0 (Tm η + iotaC p s CC)) = psiH β σ η • Φ0 (ZjH σ d η CC) := by
      rw [Lc_apply, ← hsplit η CC]
      rfl
    rw [e1] at h
    exact h
  · rw [hPhi]
    exact hTI.contDiff
  · beta_reduce
    have hiq : ((i : ℕ) : WithTop ℕ∞) ≤ (q : WithTop ℕ∞) := by exact_mod_cast hi
    have heq := hTI.eq_iteratedFDeriv hiq Z
    rw [hPhi, ← heq]
    beta_reduce
    have hI : Integrable (fun η : XiH p s σ => (‖iotaC p s‖ ^ i * K * |C i| * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) *
        wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ))))) (muXiH p s σ) :=
      (hIT p s σ _ (he i hi)).const_mul _
    refine (norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun η => hpt i hi η Z)).trans ?_
    rw [integral_const_mul]
    have hsum := Finset.single_le_sum (s := Finset.range (q + 1))
      (f := fun k => ‖iotaC p s‖ ^ k * |C k| * ∫ η, wtH η ^ (-(e k / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ))
      (fun k _ => mul_nonneg (mul_nonneg (by positivity) (abs_nonneg _))
        (integral_nonneg fun η => Real.rpow_nonneg (wtH_pos η).le _))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hr : 0 ≤ (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) := by positivity
    calc ‖iotaC p s‖ ^ i * K * |C i| * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) * ∫ η, wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ)
        = (‖iotaC p s‖ ^ i * |C i| * ∫ η, wtH η ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) ∂(muXiH p s σ)) * K * (1 + ‖Z‖) ^ (-(e i / (5 * ((p + s : ℕ) : ℝ)))) := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsum hK) hr

/- English proof (translation)
Introduce `hZ _ hST hIT`. Conclude with `topCells_of hZ hST hIT`.
-/
theorem topCellsOfParts : TopCellsOfParts := by
  intro hZ _ hST hIT
  exact topCells_of hZ hST hIT

end Formalism.FourierDecayAlt.P.Ux13

/- English proof (translation)
Conclude with `Formalism.FourierDecayAlt.P.Ux13.topCellsOfParts`.
-/
theorem Formalism.FourierDecayAlt.P.top_cells_of_parts : Formalism.FourierDecayAlt.U.TopCellsOfParts := by
  exact Formalism.FourierDecayAlt.P.Ux13.topCellsOfParts

/- English proof (translation)
Conclude with `Formalism.FourierDecayAlt.P.Ux13.topCells_of Formalism.FourierDecayAlt.P.level_z_affine Formalism.FourierDecayAlt.P.sizes_top_level Formalism.FourierDecayAlt.P.integrability_top_level`.
-/
theorem Formalism.FourierDecayAlt.P.top_cells : Formalism.FourierDecayAlt.U.TopCells := by
  exact Formalism.FourierDecayAlt.P.Ux13.topCells_of Formalism.FourierDecayAlt.P.level_z_affine Formalism.FourierDecayAlt.P.sizes_top_level Formalism.FourierDecayAlt.P.integrability_top_level
