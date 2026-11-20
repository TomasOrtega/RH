import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Ker.HeisDeriv

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}
  {μ : Measure (WO V W)} {𝓕 : Set (WO V W)} {f : WO V W → ℂ}

/- English proof (translation)
Take `⟨σ, hσ⟩` from `GlobalTheory.FockCompare.exists_chart hθ`. Establish `hsm` using `GlobalTheory.OrientedHeis.theta_sm hσ hf`. Establish `key : ∀ y : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (GlobalTheory.FockCompare.piW θ W V (lin …` using `fun y => by`. Rewrite using `[GlobalTheory.OrientedHeis.dRho_eq_dLine, GlobalTheory.OrientedHeis.dLine_eq_hD hσ hψ (GlobalTheory.OrientedHeis.isRealDir_lineAt hθ τ y)]`. Establish `hlin_add : ∀ u u' : GlobalTheory.FockCompare.RW W V, GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (u + u') f = GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (Global …`.

Introduce `u u'`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.add_apply, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlin_smul : ∀ (t : ℝ) (u : GlobalTheory.FockCompare.RW W V), GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (t • u) f = (t : ℂ) • GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iot …`. Introduce `t u`. Use function extensionality and compare the values at `w`. Simplify using `only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_smul, Complex.real_smul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hadd_u : ∀ y y' : Matrix (Fin W.rank) (Fin V.rank) ℂ, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ (y + y') 1) = GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) + GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y' 1)`. Introduce `y y'`. Rewrite using `[GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]`. Conclude with `Pi.single_add (f := fun _ => Matrix (Fin W.rank) (Fin V.rank) ℂ) τ y y'`.

Establish `hsmul_u : ∀ (t : ℝ) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ), GlobalTheory.FockCompare.piW θ W V (lineAt θ τ ((t : ℂ) • y) 1) = t • GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1)`. Introduce `t y`. Rewrite using `[GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]`. Establish `e : ((t : ℂ) • y) = t • y`. Use extensionality with `a b`.

Simplify using `[Complex.real_smul]`. Rewrite using `[e]`. Conclude with `Pi.single_smul' τ t y`. Use `⟨fun y y' => ?_, fun t y => ?_⟩` and prove the remaining obligations. Rewrite using `[key, key, key, hadd_u, hlin_add]`.

Rewrite using `[key, key, hsmul_u, hlin_smul]`.
-/
theorem dRho_dir_linear (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau) :
    (∀ z z' : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ (z + z') f =
      Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f + Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z' f) ∧
    ∀ (t : ℝ) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ ((t : ℂ) • z) f =
      (t : ℂ) • Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsm := GlobalTheory.OrientedHeis.theta_sm hσ hf
  have key : ∀ y : Matrix (Fin W.rank) (Fin V.rank) ℂ, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f =
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W)
        (GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1)) f := fun y => by
    rw [GlobalTheory.OrientedHeis.dRho_eq_dLine, GlobalTheory.OrientedHeis.dLine_eq_hD hσ hψ (GlobalTheory.OrientedHeis.isRealDir_lineAt hθ τ y)]
  have hlin_add : ∀ u u' : GlobalTheory.FockCompare.RW W V,
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (u + u') f =
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u f +
        GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) u' f := by
    intro u u'
    funext w
    simp only [Pi.add_apply, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_add]
    push_cast
    ring
  have hlin_smul : ∀ (t : ℝ) (u : GlobalTheory.FockCompare.RW W V),
      GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V) (GlobalTheory.OrientedHeis.omO V W) (t • u) f =
        (t : ℂ) • GlobalTheory.FockCompare.hD (GlobalTheory.FockCompare.iotaW σ W V) (GlobalTheory.FockCompare.piW θ W V)
          (GlobalTheory.OrientedHeis.omO V W) u f := by
    intro t u
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.FockCompare.hD_eq_fderiv _ _ _ f hsm, map_smul, Complex.real_smul]
    push_cast
    ring
  have hadd_u : ∀ y y' : Matrix (Fin W.rank) (Fin V.rank) ℂ, GlobalTheory.FockCompare.piW θ W V (lineAt θ τ (y + y') 1) =
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) + GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y' 1) := by
    intro y y'
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    exact Pi.single_add (f := fun _ => Matrix (Fin W.rank) (Fin V.rank) ℂ) τ y y'
  have hsmul_u : ∀ (t : ℝ) (y : Matrix (Fin W.rank) (Fin V.rank) ℂ),
      GlobalTheory.FockCompare.piW θ W V (lineAt θ τ ((t : ℂ) • y) 1) = t • GlobalTheory.FockCompare.piW θ W V (lineAt θ τ y 1) := by
    intro t y
    rw [GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ, GlobalTheory.Ker.HeisDeriv.pi_lineAt hθ]
    have e : ((t : ℂ) • y) = t • y := by
      ext a b
      simp [Complex.real_smul]
    rw [e]
    exact Pi.single_smul' τ t y
  refine ⟨fun y y' => ?_, fun t y => ?_⟩
  · rw [key, key, key, hadd_u, hlin_add]
  · rw [key, key, hsmul_u, hlin_smul]

/- English proof (translation)
Use `conv_lhs => rw [Matrix.matrix_eq_sum_single z]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, smul_eq_mul, mul_one, Complex.re_add_im]`.
-/
theorem matrix_eq_sum_re_im {m n : ℕ} (z : Matrix (Fin m) (Fin n) ℂ) :
    z = ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • Matrix.single i j (1 : ℂ) +
      (((z i j).im : ℝ) : ℂ) • Matrix.single i j Complex.I) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single z]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul, smul_eq_mul, mul_one,
    Complex.re_add_im]

/- English proof (translation)
Take `⟨hadd, hsm⟩` from `dRho_dir_linear hψ hθ hf τ`. Set `L : Matrix (Fin W.rank) (Fin V.rank) ℂ →+ (WO V W → ℂ)` to `AddMonoidHom.mk' (fun y => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f) hadd`. Establish `hL : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = L y` using `fun _ => rfl`. Rewrite using `[hL]`. Use `conv_lhs => rw [matrix_eq_sum_re_im z]`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_add, ← hL, ← hL, hsm, hsm]`.

Simplify using `[heisDer]`.
-/
theorem dRho_eq_sum_heisDer (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) :
    Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f =
      ∑ i, ∑ j, ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
        (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := by
  obtain ⟨hadd, hsm⟩ := dRho_dir_linear hψ hθ hf τ
  let L : Matrix (Fin W.rank) (Fin V.rank) ℂ →+ (WO V W → ℂ) :=
    AddMonoidHom.mk' (fun y => Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f) hadd
  have hL : ∀ y, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ y f = L y := fun _ => rfl
  rw [hL]
  conv_lhs => rw [matrix_eq_sum_re_im z]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_add, ← hL, ← hL, hsm, hsm]
  simp [heisDer]

/- English proof (translation)
Use `revert hg`. Use `Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact theta_zero) ?_` and prove the remaining obligations. Introduce `a t ha ih hg`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `theta_add (hg a (Finset.mem_insert_self a t)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))`.
-/
theorem theta_finsetSum {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ} (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) :
    IsThetaFunO ψ V W (∑ i ∈ s, g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => by rw [Finset.sum_empty]; exact theta_zero) ?_
  intro a t ha ih hg
  rw [Finset.sum_insert ha]
  exact theta_add (hg a (Finset.mem_insert_self a t)) (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Use `revert hg`. Use `Finset.induction_on s (fun _ => ?_) ?_` and prove the remaining obligations. Establish `h0` using `sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := (0 : WO V W → ℂ)) d 0`. Simplify using `only [smul_zero, enorm_zero, zero_mul] at h0`. Simplify using `[h0]`.

Introduce `a t ha ih hg`. Establish `ha' : IsThetaFunO ψ V W (g a)` using `hg a (Finset.mem_insert_self a t)`. Establish `ht : ∀ i ∈ t, IsThetaFunO ψ V W (g i)` using `fun i hi => hg i (Finset.mem_insert_of_mem hi)`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `(sobO_add_le hψ hθ ha' (theta_finsetSum t ht) d).trans (add_le_add le_rfl (ih ht))`.
-/
theorem sobO_sum_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ι : Type} (s : Finset ι) {g : ι → WO V W → ℂ}
    (hg : ∀ i ∈ s, IsThetaFunO ψ V W (g i)) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (∑ i ∈ s, g i) ≤ ∑ i ∈ s, sobO ψ θ μ 𝓕 d (g i) := by
  classical
  revert hg
  refine Finset.induction_on s (fun _ => ?_) ?_
  · have h0 := sobO_smul (ψ := ψ) (θ := θ) (μ := μ) (𝓕 := 𝓕) (f := (0 : WO V W → ℂ)) d 0
    simp only [smul_zero, enorm_zero, zero_mul] at h0
    simp [h0]
  · intro a t ha ih hg
    have ha' : IsThetaFunO ψ V W (g a) := hg a (Finset.mem_insert_self a t)
    have ht : ∀ i ∈ t, IsThetaFunO ψ V W (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sobO_add_le hψ hθ ha' (theta_finsetSum t ht) d).trans (add_le_add le_rfl (ih ht))

/- English proof (translation)
Establish `hD : ∀ a, IsThetaFunO ψ V W (heisDer ψ θ a f)` using `fun a => by`. Simplify `theta_word hψ hθ [a] hf` using `[wordAct]`. Establish `hT : ∀ i j, IsThetaFunO ψ V W ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f + (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f)` using `fun i j => theta_add (theta_smul _ (hD _)) (theta_smul _ (hD _))`. Establish `hre : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r|` using `fun r => by`. Rewrite using `[← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]`.

Rewrite using `[dRho_eq_sum_heisDer hψ hθ hf τ z]`. Use `(sobO_sum_le hψ hθ Finset.univ (fun i _ => theta_finsetSum Finset.univ fun j _ => hT i j) d).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Use `(sobO_sum_le hψ hθ Finset.univ (fun j _ => hT i j) d).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations.

Use `(sobO_add_le hψ hθ (theta_smul _ (hD _)) (theta_smul _ (hD _)) d).trans ?_` and prove the remaining obligations. Rewrite using `[sobO_smul, sobO_smul, hre, hre, add_mul]`. Apply the tactic sequence `gcongr <;> exact sobO_heisDer_le d _`. Use `_ = _ := by`. Repeatedly rewrite using `[← Finset.sum_mul]`.

Use `congr 1`. Rewrite using `[ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]`. Conclude with `Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm`.
-/
theorem sobO_dRho_le (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hf : IsThetaFunO ψ V W f) (τ : D.what₂.Tau)
    (z : Matrix (Fin W.rank) (Fin V.rank) ℂ) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z f) ≤
      ENNReal.ofReal (∑ i, ∑ j, (|(z i j).re| + |(z i j).im|)) * sobO ψ θ μ 𝓕 (d + 1) f := by
  classical
  have hD : ∀ a, IsThetaFunO ψ V W (heisDer ψ θ a f) := fun a => by
    simpa [wordAct] using theta_word hψ hθ [a] hf
  have hT : ∀ i j, IsThetaFunO ψ V W ((((z i j).re : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, false) f +
      (((z i j).im : ℝ) : ℂ) • heisDer ψ θ (τ, i, j, true) f) := fun i j =>
    theta_add (theta_smul _ (hD _)) (theta_smul _ (hD _))
  have hre : ∀ r : ℝ, ‖(r : ℂ)‖ₑ = ENNReal.ofReal |r| := fun r => by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs]
  rw [dRho_eq_sum_heisDer hψ hθ hf τ z]
  refine (sobO_sum_le hψ hθ Finset.univ (fun i _ => theta_finsetSum Finset.univ fun j _ => hT i j) d).trans ?_
  calc _ ≤ ∑ i, ∑ j, (ENNReal.ofReal |(z i j).re| + ENNReal.ofReal |(z i j).im|) *
        sobO ψ θ μ 𝓕 (d + 1) f := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (sobO_sum_le hψ hθ Finset.univ (fun j _ => hT i j) d).trans (Finset.sum_le_sum fun j _ => ?_)
        refine (sobO_add_le hψ hθ (theta_smul _ (hD _)) (theta_smul _ (hD _)) d).trans ?_
        rw [sobO_smul, sobO_smul, hre, hre, add_mul]
        gcongr <;> exact sobO_heisDer_le d _
    _ = _ := by
        simp_rw [← Finset.sum_mul]
        congr 1
        rw [ENNReal.ofReal_sum_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)).symm

end GlobalTheory.Size

end
