import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.VcStHolds
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LocAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.EntEmpty
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `⟨continuous_zero, HasCompactSupport.zero⟩`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.sum_insert hj]`.

Establish `h1` using `h j (Finset.mem_insert_self j s)`. Establish `h2` using `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`. Conclude with `⟨h1.1.add h2.1, h1.2.add h2.2⟩`.
-/
private theorem isTestH_sum {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {J : Type} (s : Finset J)
    (f : J → H E a b → ℂ) (h : ∀ j ∈ s, IsTestH (f j)) : IsTestH (∑ j ∈ s, f j) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact ⟨continuous_zero, HasCompactSupport.zero⟩
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have h1 := h j (Finset.mem_insert_self j s)
    have h2 := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    exact ⟨h1.1.add h2.1, h1.2.add h2.2⟩

/- English proof (translation)
Establish `e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i`. Use function extensionality and compare the values at `y`. Simplify using `[trM, Finset.sum_apply]`. Rewrite using `[e]`. Use `isTestH_sum _ _ fun i _ => isTestH_sum _ _ fun j _ => ?_` and prove the remaining obligations.

Conclude with `⟨(h i j).1.mul continuous_const, (h i j).2.mul_right⟩`.
-/
private theorem isTestH_trM {a b : ℕ} {E : Type} [Field E] [NumberField E] [IsCMField E] {ι : Type} [Fintype ι]
    (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) (h : IsTestM Φ) : IsTestH (trM Φ M) := by
  have e : trM Φ M = ∑ i, ∑ j, fun y => Φ i j y * M j i := by
    funext y
    simp [trM, Finset.sum_apply]
  rw [e]
  refine isTestH_sum _ _ fun i _ => isTestH_sum _ _ fun j _ => ?_
  exact ⟨(h i j).1.mul continuous_const, (h i j).2.mul_right⟩

/- English proof (translation)
Use `haveI : BorelSpace (G 0) := ⟨rfl⟩`. Establish `h` using `((lefModel 0 lam (fun i => i.elim0)).2.2.2 μ k val T hm).2 1 (fun i => i.elim0) (Subsingleton.elim _ _) (fun a => a.elim0) (Function.injective_of_subsingleton _)`. Establish `e : (fun x : G 0 => phiOf (lefE 0 lam) (lefT 0 lam) k (PositivityTheory.RgTw.tw x 1)) = fun _ => phiOf (lefE 0 lam) (lefT 0 lam) k 1`. Use function extensionality and compare the values at `x`. Rewrite using `[Subsingleton.elim (PositivityTheory.RgTw.tw x 1) 1]`.

Establish `h2` using `h.2`. Rewrite `h2` using `[e, integral_const]`. Simplify `h2` using `[weylChar]`.
-/
private theorem lef_zero (lam : Fin 0 → ℤ) (μ : Measure (G 0)) [μ.IsHaarMeasure] (k : Mat 0 → ((lefE 0 lam).V →L[ℂ] (lefE 0 lam).V))
    (val : Inf 0 → ℂ) (T : ℝ) (hm : IsMult μ (lefE 0 lam) k val T) :
    (μ.real Set.univ : ℂ) * phiOf (lefE 0 lam) (lefT 0 lam) k 1 = val (infOf lam) := by
  haveI : BorelSpace (G 0) := ⟨rfl⟩
  have h := ((lefModel 0 lam (fun i => i.elim0)).2.2.2 μ k val T hm).2 1 (fun i => i.elim0)
    (Subsingleton.elim _ _) (fun a => a.elim0) (Function.injective_of_subsingleton _)
  have e : (fun x : G 0 => phiOf (lefE 0 lam) (lefT 0 lam) k (PositivityTheory.RgTw.tw x 1)) =
      fun _ => phiOf (lefE 0 lam) (lefT 0 lam) k 1 := by
    funext x
    rw [Subsingleton.elim (PositivityTheory.RgTw.tw x 1) 1]
  have h2 := h.2
  rw [e, integral_const] at h2
  simpa [weylChar] using h2

/- English proof (translation)
Establish `h1 : μ Set.univ ≠ 0` using `(isOpen_univ.measure_pos μ Set.univ_nonempty).ne'`. Establish `h2 : μ Set.univ ≠ ⊤` using `(Set.subsingleton_of_subsingleton.isCompact.measure_lt_top).ne`. Conclude with `(ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩)` after adjusting the coercions.
-/
private theorem real_univ_ne (μ : Measure (G 0)) [μ.IsHaarMeasure] : (μ.real Set.univ : ℂ) ≠ 0 := by
  have h1 : μ Set.univ ≠ 0 := (isOpen_univ.measure_pos μ Set.univ_nonempty).ne'
  have h2 : μ Set.univ ≠ ⊤ := (Set.subsingleton_of_subsingleton.isCompact.measure_lt_top).ne
  exact_mod_cast (ENNReal.toReal_ne_zero.2 ⟨h1, h2⟩)

/- English proof (translation)
Introduce `hPi hSum E _ _ _ hU n hn π hreg hdual`. Take `⟨l, hl, hP⟩` from `hPi E hU n hn π hreg hdual`. Use `⟨l, hl, ?_⟩` and prove the remaining obligations. Introduce `l₂ D A S hS Z hZ B τ hB hτ u₁ u₂ hu₁`. Use `haveI := A.ha`.

Use `haveI := A.hb`. Establish `hμ : D.μ.IsHaarMeasure`. Take `⟨h1, -, h3, h4⟩` from `D.haar`. Conclude with `{ }`. Take `⟨c₀, hc₀, hc⟩` from `hP S hS Z hZ B τ hB hτ u₁ hu₁ A.μa D.μ A.ha hμ`.

Establish `hvol : A.blk.vol ≠ 0` using `(ffAlg E n 0 l l₂ D A S hS).1`. Establish `hm` using `real_univ_ne A.μb`. Generalize the expression as in `hmdef : (A.μb.real Set.univ : ℂ) = m at hm`. Use `⟨c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E), mul_ne_zero (mul_ne_zero hc₀ (inv_ne_zero hvol)) (pow_ne_zero _ (inv_ne_zero hm)), ?_⟩` and prove the remaining obligations. Introduce `L φ T e₁ e₂ C R hφ hTE hTZ hC`.

Establish `hLc : ∀ w ∈ Z, Lc (K2 n 0 w) (φ w) ∧ Lc (K2 n 0 w) (L.ln w)`. Introduce `w hw`. Establish `h` using `positionTest E n 0 S Z L hZ`. Conclude with `⟨(h.2.2 φ hφ).1 w hw, (h.2.2 L.ln h.1).1 w hw⟩`. Establish `hseen : ∀ w ∈ Z, (fun g => seen φ L.ln w (g, 1)) = fun g => φ w (g, 1)`.

Introduce `w hw`. Establish `h` using `((locAlg E n 0 Z L w).2.2.2.1 (φ w) (hφ w hw)).1`. Use function extensionality and compare the values at `g`. Simplify using `only [seen, if_pos (hZ w hw).2]`. Conclude with `congrFun h (g, 1)`.

Establish `hX : (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ L.ln w (g, 1)) = ∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)` using `Finset.prod_congr rfl fun w hw => by rw [hseen w hw]`. Generalize the expression as in `(∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) = X at hX ⊢`. Establish `term : ∀ j ∈ C.s, IsTestH (trM (C.t j).Φ A.tw) ∧ IsTwTr D.μ π (trM (C.t j).Φ A.tw) (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X * val T e₁ e₂ B 0)`. Introduce `j hj`. Take `⟨ok, hψ, -, -⟩` from `hC j hj`.

Generalize the expression as in `C.t j = t at ok hψ ⊢`. Establish `hPt` using `hc φ L.ln hLc T hTZ e₁ e₂ t.ka t.va t.T hTE ok.ka`. Rewrite `hPt` using `[hX]`. Establish `hf : trM t.Φ A.tw = ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) • phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))`. Use function extensionality and compare the values at `g`.

Establish `h1` using `tensTr E n 0 (Ml l) (Ml l₂) Unit t.ka t.kb (Tl l) (Tl l₂) t.ψ 1 g`. Establish `hp : (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹ : Hf E n 0) = (finOf E n g.1 * (ratF E n u₁)⁻¹, 1)` using `Prod.ext rfl (Subsingleton.elim _ _)`. Establish `hg : ∀ v, gInf v g.2 = 1` using `fun v => Subsingleton.elim _ _`. Establish `h2 : ∑ x, ∑ y, t.ψ x y (hFin g) * (1 : Matrix Unit Unit ℂ) y x = A.blk.vol⁻¹ * finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (finOf E n g.1)`. Rewrite using `[hψ]`.

Simplify using `only [Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq, mul_one]`. Use `show A.blk.vol⁻¹ * finFn S _ _ (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹) = _`. Rewrite using `[hp]`. Both sides reduce to the same expression. Use `h1.trans ?_` and prove the remaining obligations.

Rewrite using `[h2]`. Simplify using `only [hg, Pi.smul_apply, smul_eq_mul, phiProd]`. Use `show (∏ v, phiOf (lefE n (l v).w) (lefT n (l v).w) (t.ka v) (gInf v g.1)) * _ * _ = _`. Establish `h3 : ∀ v, gInf v g.1 = infAt E n v g.1` using `fun v => rfl`. Simplify using `only [h3]`.

Use `show _ * (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * _ = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hval : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * t.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 = ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) * (c₀ * (∏ v, t.va v (infOf (l v).w)) * X * val T e₁ e₂ B 0)`. Establish `hb : ∀ v, t.vb v (chi l₂ v) = m * phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1` using `fun v => by`. Rewrite using `[← hmdef]`.

Conclude with `(lef_zero (l₂ v).w A.μb (t.kb v) (t.vb v) t.T (ok.kb v)).symm`. Establish `e : t.val (chi l) (chi l₂) = (∏ v, t.va v (infOf (l v).w)) * (m ^ Fintype.card (InfinitePlace E) * ∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1)` using `by show (∏ v, t.va v (chi l v)) * ∏ v, t.vb v (chi l₂ v) = _`. Simplify using `only [hb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`. Both sides reduce to the same expression. Rewrite using `[e, inv_pow]`.

Clear the denominators using the available nonvanishing facts. Establish `htest : IsTestH (trM t.Φ A.tw)` using `isTestH_trM _ _ (BlockFiniteConvolution.blkOp₀ E A.blk t t ok ok).1`. Use `⟨htest, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, hf]`. Distinguish the cases in `h0 : (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹ = 0`.

Establish `h` using `hSum E n D π Empty ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) (by simp)`. Rewrite using `[h0, zero_smul, zero_mul]`. Simplify using `using h`. Rewrite `htest` using `[hf]`. Establish `hPtest : IsTestH (phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)))`.

Use `⟨(continuous_const_smul_iff₀ h0).1 htest.1, ?_⟩` and prove the remaining obligations. Establish `h1` using `htest.2.mul_left (f := fun _ => ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹)`. Establish `e : phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) = fun y => ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹ * (((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v) …`. Use function extensionality and compare the values at `y`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[inv_mul_cancel_left₀ h0]`. Rewrite using `[e]`. Conclude with `h1`. Establish `key : ∀ (s : ℂ) (P : H E n 0 → ℂ) (x : ℂ), IsTestH P → IsTwTr D.μ π P x → IsTwTr D.μ π (s • P) (s * x)`. Introduce `s P x h1 h2`.

Establish `h` using `hSum E n D π Unit {()} (fun _ => s) (fun _ => P) (fun _ => x) (fun _ _ => ⟨h1, h2⟩)`. Simplify using `using h`. Conclude with `key _ _ _ hPtest hPt`. Establish `hS'` using `hSum E n D π C.J C.s C.c (fun j => trM (C.t j).Φ A.tw) _ term`. Establish `e1 : trM C.Φ A.tw = ∑ j ∈ C.s, C.c j • trM (C.t j).Φ A.tw` using `Growth.trM_sum _ _ _ _`.

Establish `e2 : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * C.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 = ∑ j ∈ C.s, C.c j * (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X * val T e₁ e₂ B 0)`. Rewrite using `[Cmb.val, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[e1, e2]`. Conclude with `hS'`.
-/
theorem cmbPi : PiTerm → TwTrSum → CmbPi := by
  intro hPi hSum E _ _ _ hU n hn π hreg hdual
  obtain ⟨l, hl, hP⟩ := hPi E hU n hn π hreg hdual
  refine ⟨l, hl, ?_⟩
  intro l₂ D A S hS Z hZ B τ hB hτ u₁ u₂ hu₁
  haveI := A.ha
  haveI := A.hb
  have hμ : D.μ.IsHaarMeasure := by
    obtain ⟨h1, -, h3, h4⟩ := D.haar
    exact { }
  obtain ⟨c₀, hc₀, hc⟩ := hP S hS Z hZ B τ hB hτ u₁ hu₁ A.μa D.μ A.ha hμ
  have hvol : A.blk.vol ≠ 0 := (ffAlg E n 0 l l₂ D A S hS).1
  have hm := real_univ_ne A.μb
  generalize hmdef : (A.μb.real Set.univ : ℂ) = m at hm
  refine ⟨c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E),
    mul_ne_zero (mul_ne_zero hc₀ (inv_ne_zero hvol)) (pow_ne_zero _ (inv_ne_zero hm)), ?_⟩
  intro L φ T e₁ e₂ C R hφ hTE hTZ hC
  have hLc : ∀ w ∈ Z, Lc (K2 n 0 w) (φ w) ∧ Lc (K2 n 0 w) (L.ln w) := by
    intro w hw
    have h := positionTest E n 0 S Z L hZ
    exact ⟨(h.2.2 φ hφ).1 w hw, (h.2.2 L.ln h.1).1 w hw⟩
  have hseen : ∀ w ∈ Z, (fun g => seen φ L.ln w (g, 1)) = fun g => φ w (g, 1) := by
    intro w hw
    have h := ((locAlg E n 0 Z L w).2.2.2.1 (φ w) (hφ w hw)).1
    funext g
    simp only [seen, if_pos (hZ w hw).2]
    exact congrFun h (g, 1)
  have hX : (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ L.ln w (g, 1)) =
      ∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1) :=
    Finset.prod_congr rfl fun w hw => by rw [hseen w hw]
  generalize (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) = X at hX ⊢
  have term : ∀ j ∈ C.s, IsTestH (trM (C.t j).Φ A.tw) ∧ IsTwTr D.μ π (trM (C.t j).Φ A.tw)
      (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X * val T e₁ e₂ B 0) := by
    intro j hj
    obtain ⟨ok, hψ, -, -⟩ := hC j hj
    generalize C.t j = t at ok hψ ⊢
    have hPt := hc φ L.ln hLc T hTZ e₁ e₂ t.ka t.va t.T hTE ok.ka
    rw [hX] at hPt
    have hf : trM t.Φ A.tw = ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
        phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) := by
      funext g
      have h1 := tensTr E n 0 (Ml l) (Ml l₂) Unit t.ka t.kb (Tl l) (Tl l₂) t.ψ 1 g
      have hp : (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹ : Hf E n 0) = (finOf E n g.1 * (ratF E n u₁)⁻¹, 1) :=
        Prod.ext rfl (Subsingleton.elim _ _)
      have hg : ∀ v, gInf v g.2 = 1 := fun v => Subsingleton.elim _ _
      have h2 : ∑ x, ∑ y, t.ψ x y (hFin g) * (1 : Matrix Unit Unit ℂ) y x =
          A.blk.vol⁻¹ * finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂) (finOf E n g.1) := by
        rw [hψ]
        simp only [Finset.univ_unique, Finset.sum_singleton, Matrix.one_apply_eq, mul_one]
        show A.blk.vol⁻¹ * finFn S _ _ (hFin g * (ratF E n u₁, ratF E 0 u₂)⁻¹) = _
        rw [hp]
        rfl
      refine h1.trans ?_
      rw [h2]
      simp only [hg, Pi.smul_apply, smul_eq_mul, phiProd]
      show (∏ v, phiOf (lefE n (l v).w) (lefT n (l v).w) (t.ka v) (gInf v g.1)) * _ * _ = _
      have h3 : ∀ v, gInf v g.1 = infAt E n v g.1 := fun v => rfl
      simp only [h3]
      show _ * (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * _ = _
      ring
    have hval : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * t.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
        ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) *
          (c₀ * (∏ v, t.va v (infOf (l v).w)) * X * val T e₁ e₂ B 0) := by
      have hb : ∀ v, t.vb v (chi l₂ v) = m * phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1 := fun v => by
        rw [← hmdef]
        exact (lef_zero (l₂ v).w A.μb (t.kb v) (t.vb v) t.T (ok.kb v)).symm
      have e : t.val (chi l) (chi l₂) = (∏ v, t.va v (infOf (l v).w)) *
          (m ^ Fintype.card (InfinitePlace E) * ∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) := by
        show (∏ v, t.va v (chi l v)) * ∏ v, t.vb v (chi l₂ v) = _
        simp only [hb, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
        rfl
      rw [e, inv_pow]
      field_simp
    have htest : IsTestH (trM t.Φ A.tw) := isTestH_trM _ _ (BlockFiniteConvolution.blkOp₀ E A.blk t t ok ok).1
    refine ⟨htest, ?_⟩
    rw [hval, hf]
    by_cases h0 : (∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹ = 0
    · have h := hSum E n D π Empty ∅ (fun _ => 0) (fun _ => 0) (fun _ => 0) (by simp)
      rw [h0, zero_smul, zero_mul]
      simpa using h
    · rw [hf] at htest
      have hPtest : IsTestH (phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) := by
        refine ⟨(continuous_const_smul_iff₀ h0).1 htest.1, ?_⟩
        have h1 := htest.2.mul_left (f := fun _ => ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹)
        have e : phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂)) = fun y =>
            ((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹)⁻¹ *
              (((∏ v, phiOf (lefE 0 (l₂ v).w) (lefT 0 (l₂ v).w) (t.kb v) 1) * A.blk.vol⁻¹) •
                phiProd (fun v => (l v).w) t.ka (finU S u₁ (intersection_update_fsHerm_neg_one Z T φ e₁) (intersection_update_fsHerm_neg_one Z T L.ln e₂))) y := by
          funext y
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [inv_mul_cancel_left₀ h0]
        rw [e]
        exact h1
      have key : ∀ (s : ℂ) (P : H E n 0 → ℂ) (x : ℂ), IsTestH P → IsTwTr D.μ π P x → IsTwTr D.μ π (s • P) (s * x) := by
        intro s P x h1 h2
        have h := hSum E n D π Unit {()} (fun _ => s) (fun _ => P) (fun _ => x) (fun _ _ => ⟨h1, h2⟩)
        simpa using h
      exact key _ _ _ hPtest hPt
  have hS' := hSum E n D π C.J C.s C.c (fun j => trM (C.t j).Φ A.tw) _ term
  have e1 : trM C.Φ A.tw = ∑ j ∈ C.s, C.c j • trM (C.t j).Φ A.tw := Growth.trM_sum _ _ _ _
  have e2 : c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * C.val (chi l) (chi l₂) * X * val T e₁ e₂ B 0 =
      ∑ j ∈ C.s, C.c j * (c₀ * A.blk.vol⁻¹ * (m⁻¹) ^ Fintype.card (InfinitePlace E) * (C.t j).val (chi l) (chi l₂) * X *
        val T e₁ e₂ B 0) := by
    rw [Cmb.val, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2]
  exact hS'

end UpperTheory.Zero.ConvolutionTheory.EB
