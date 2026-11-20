import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsStmt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

/- English proof (translation)
Introduce `V F _ _ _ _ q k c`. Take `⟨C, hC, h⟩` from `compSz V V (V [⋀^Fin q]→L[ℝ] F) k c`. Use `⟨|c| * |c| ^ q * C, by positivity, fun A B w p b hA hB hw hs => ?_⟩` and prove the remaining obligations. Establish `hA' : ‖A‖ ≤ |c|` using `hA.trans (le_abs_self c)`. Establish `hB' : ‖B‖ ≤ |c|` using `hB.trans (le_abs_self c)`.

Establish `h1 : Sz k (fun y => w (A y)) p (C * b)`. Use `h w A p b A.contDiff.contDiffAt hw (fun i hi _ => ?_) hs` and prove the remaining obligations. Take `⟨j, rfl⟩ : ∃ j, i = j + 1` from `⟨i - 1, by omega⟩`. Rewrite using `[← norm_iteratedFDeriv_fderiv]`. Establish `e : fderiv ℝ (A : V → V) = fun _ => A` using `funext fun x => A.fderiv`.

Rewrite using `[e]`. Break down `j with _ | j` into its components or cases. Simplify using `using hA`. Rewrite using `[iteratedFDeriv_succ_const]`. Simplify using `using (norm_nonneg A).trans hA`.

Set `L₀ : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] (V [⋀^Fin q]→L[ℝ] F)` to `{ toFun := fun m => B.compContinuousAlternatingMap (m.compContinuousLinearMap A) map_add' := fun m n => by ext v; simp map_smul' := fun r m => by ext v; simp }`. Establish `hL : ∀ m, ‖L₀ m‖ ≤ |c| * |c| ^ q * ‖m‖` using `fun m => by`. Use `ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_` and prove the remaining obligations. Establish `a1 : ‖m fun i => A (v i)‖ ≤ ‖m‖ * ∏ i, ‖A (v i)‖` using `m.le_opNorm _`. Establish `a2 : ∏ i, ‖A (v i)‖ ≤ ∏ i, (|c| * ‖v i‖)` using `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => A.le_of_opNorm_le hA' _`.

Rewrite `a2` using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `a1.trans (mul_le_mul_of_nonneg_left a2 (norm_nonneg _))`. Use `_ = _ := by ring`. Establish `hn : ‖L₀.mkContinuous _ hL‖ ≤ |c| * |c| ^ q` using `L₀.mkContinuous_norm_le (by positivity) hL`.

Establish `h2` using `(appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).2.1 (L₀.mkContinuous _ hL) (fun y => w (A y)) (C * b) (hw.comp p A.contDiff.contDiffAt) h1`. Use `Sz.mono h2 ?_` and prove the remaining obligations. Rewrite using `[mul_assoc (|c| * |c| ^ q)]`. Conclude with `mul_le_mul_of_nonneg_right hn h1.nonneg`.
-/
theorem UpperTheory.V.Lit.Geo.Cs.tpSz :
    TpSz := by
  intro V F _ _ _ _ q k c
  obtain ⟨C, hC, h⟩ := compSz V V (V [⋀^Fin q]→L[ℝ] F) k c
  refine ⟨|c| * |c| ^ q * C, by positivity, fun A B w p b hA hB hw hs => ?_⟩
  have hA' : ‖A‖ ≤ |c| := hA.trans (le_abs_self c)
  have hB' : ‖B‖ ≤ |c| := hB.trans (le_abs_self c)
  have h1 : Sz k (fun y => w (A y)) p (C * b) := by
    refine h w A p b A.contDiff.contDiffAt hw (fun i hi _ => ?_) hs
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [← norm_iteratedFDeriv_fderiv]
    have e : fderiv ℝ (A : V → V) = fun _ => A := funext fun x => A.fderiv
    rw [e]
    rcases j with _ | j
    · simpa using hA
    · rw [iteratedFDeriv_succ_const]
      simpa using (norm_nonneg A).trans hA
  let L₀ : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] (V [⋀^Fin q]→L[ℝ] F) :=
    { toFun := fun m => B.compContinuousAlternatingMap (m.compContinuousLinearMap A)
      map_add' := fun m n => by ext v; simp
      map_smul' := fun r m => by ext v; simp }
  have hL : ∀ m, ‖L₀ m‖ ≤ |c| * |c| ^ q * ‖m‖ := fun m => by
    refine ContinuousAlternatingMap.opNorm_le_bound _ (by positivity) fun v => ?_
    have a1 : ‖m fun i => A (v i)‖ ≤ ‖m‖ * ∏ i, ‖A (v i)‖ := m.le_opNorm _
    have a2 : ∏ i, ‖A (v i)‖ ≤ ∏ i, (|c| * ‖v i‖) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => A.le_of_opNorm_le hA' _
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at a2
    calc ‖L₀ m v‖ = ‖B (m fun i => A (v i))‖ := rfl
      _ ≤ |c| * ‖m fun i => A (v i)‖ := B.le_of_opNorm_le hB' _
      _ ≤ |c| * (‖m‖ * (|c| ^ q * ∏ i, ‖v i‖)) := by
        gcongr
        exact a1.trans (mul_le_mul_of_nonneg_left a2 (norm_nonneg _))
      _ = _ := by ring
  have hn : ‖L₀.mkContinuous _ hL‖ ≤ |c| * |c| ^ q := L₀.mkContinuous_norm_le (by positivity) hL
  have h2 := (appSz V (V [⋀^Fin q]→L[ℝ] F) (V [⋀^Fin q]→L[ℝ] F) k p).2.1 (L₀.mkContinuous _ hL)
    (fun y => w (A y)) (C * b) (hw.comp p A.contDiff.contDiffAt) h1
  refine Sz.mono h2 ?_
  rw [mul_assoc (|c| * |c| ^ q)]
  exact mul_le_mul_of_nonneg_right hn h1.nonneg
