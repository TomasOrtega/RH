import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothOfLimitClassStableUnderDirectionalDerivsStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

namespace GlobalTheory.ThetaDens

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in

/- English proof (translation)
Introduce `w`. Use `GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨l, rfl⟩`. Establish `hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop` using `fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly`. Use `⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩` and prove the remaining obligations.

Establish `h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ)` using `(LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)`. Establish `hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)` using `contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)`. Use `⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun y => F l (w + ι y)` using `(hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently`. Establish `h0 : TendstoLocallyUniformly (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop` using `fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩`.

Establish `h2` using `(h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))`. Establish `e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x)`. Use function extensionality and compare the values at `j x`. Rewrite using `[hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]`. Use `fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x` as an intermediate fact.

Rewrite `this` using `[add_zero]`. Establish `e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y))`. Use function extensionality and compare the values at `y`. Rewrite using `[map_add, add_assoc]`. Rewrite using `[← this, e2]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h2`.
-/
theorem sm_of_tendstoUniformly_words {G R A : Type} [AddCommGroup G] [NormedAddCommGroup R] [NormedSpace ℝ R]
    [FiniteDimensional ℝ R] [Fintype A] (ι : R →+ G) (p : G →+ R) (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (hp : ∀ x, p (ι x) = x)
    (v : A → R) (c : A → R →L[ℝ] ℝ) (hv : ∀ x, ∑ a, c a x • v a = x) (g : List A → ℕ → G → ℂ)
    (hg : ∀ l j, Sm ι (g l j)) (hd : ∀ a l j, g (a :: l) j = hD ι p om (v a) (g l j)) (F : List A → G → ℂ)
    (hF : ∀ l, TendstoUniformly (g l) (F l) Filter.atTop) (l : List A) : Sm ι (F l) := by
  intro w
  refine GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs v c hv (fun φ => ∃ l, φ = fun y => F l (w + ι y)) ?_ _ ⟨l, rfl⟩
  rintro _ ⟨l, rfl⟩
  have hU : ∀ l, TendstoLocallyUniformly (fun j y => g l j (w + ι y)) (fun y => F l (w + ι y)) Filter.atTop :=
    fun l => ((hF l).comp fun y => w + ι y).tendstoLocallyUniformly
  refine ⟨fun j y => g l j (w + ι y), fun j => (hg l j w).differentiable (by simp), hU l, fun a => ?_⟩
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun x : R => (om.flip (v a) (p w + x) : ℝ) :=
    (LinearMap.toContinuousLinearMap (om.flip (v a))).contDiff.comp (contDiff_const.add contDiff_id)
  have hα : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) :=
    contDiff_const.mul (Complex.ofRealCLM.contDiff.comp h1)
  refine ⟨_, hα, _, ⟨a :: l, rfl⟩, ?_⟩
  have hc : Continuous fun y => F l (w + ι y) :=
    (hU l).continuous (Filter.Eventually.of_forall fun j => (hg l j w).continuous).frequently
  have h0 : TendstoLocallyUniformly
      (fun (_ : ℕ) (x : R) => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ))
      (fun x : R => (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ)) Filter.atTop :=
    fun U hU x => ⟨Set.univ, Filter.univ_mem, Filter.Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have h2 := (h0.mul₀ (hU l) hα.continuous hc).add (hU (a :: l))
  have e : (fun j y => fderiv ℝ (fun y => g l j (w + ι y)) y (v a)) = fun j x =>
      (Real.pi * Complex.I : ℂ) * ((om.flip (v a) (p w + x) : ℝ) : ℂ) * g l j (w + ι x) + g (a :: l) j (w + ι x) := by
    funext j x
    rw [hd, hD_eq_fderiv ι p om _ (hg l j), map_add p, hp, LinearMap.flip_apply]
    have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : R => g l j (w + ι y)) (x := 0) x
    rw [add_zero] at this
    have e2 : (fun y : R => g l j (w + ι x + ι y)) = fun y => g l j (w + ι (x + y)) := by
      funext y
      rw [map_add, add_assoc]
    rw [← this, e2]
    ring
  rw [e]
  exact h2

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]`. Rewrite using `[Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp), Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp), Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using `[add_comm]`.
-/
theorem sum_coord_single {τs : Type} [Fintype τs] {m n : ℕ} (x : τs → Fin m → Fin n → ℂ)
    (v : τs × Fin m × Fin n × Bool → τs → Fin m → Fin n → ℂ)
    (hv : ∀ a τ i j, v a τ i j = if τ = a.1 then
      Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1) i j else 0) :
    ∑ a : τs × Fin m × Fin n × Bool,
      (if a.2.2.2 then (x a.1 a.2.1 a.2.2.1).im else (x a.1 a.2.1 a.2.2.1).re) • v a = x := by
  funext τ i j
  simp only [Finset.sum_apply, Pi.smul_apply, hv, Fintype.sum_prod_type, Matrix.single_apply]
  rw [Finset.sum_eq_single τ (fun b _ hb => by simp [hb.symm]) (by simp),
    Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp),
    Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  simp [add_comm]

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.Size in

/- English proof (translation)
Introduce `D ψ hψ θ hθ S T u hu F hF l`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Use `((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_` and prove the remaining obligations. Set `z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ` to `fun a => Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)`. Set `c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ` to `fun a => (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp (ContinuousLinearMap.proj (R := ℝ) (φ := f …`.

Use `sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S) (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j)) (fun l j => theta_sm h (theta_word hψ hθ l (hu j))) (fun a l j => dLine_eq_hD h hψ (isRealDir_li …` and prove the remaining obligations. Use `Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)` and prove the remaining obligations. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Take `⟨τ, i, j, b⟩` from `a`.

Apply the tactic sequence `cases b <;> rfl`. Use `congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [z, *]`.
-/
theorem contDiff_of_tendstoUniformly_words : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  intro D ψ hψ θ hθ S T u hu F hF l
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  refine ((smooth_iff_sm_and_real_lines D θ σ h T S).1 (F l)).2 ?_
  let z : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → Matrix (Fin T.rank) (Fin S.rank) ℂ := fun a =>
    Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1)
  let c : D.what₂.Tau × Fin T.rank × Fin S.rank × Bool → RW T S →L[ℝ] ℝ := fun a =>
    (if a.2.2.2 then Complex.imCLM else Complex.reCLM).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin S.rank => ℂ) a.2.2.1).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin T.rank => Fin S.rank → ℂ) a.2.1).comp
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : D.what₂.Tau => Fin T.rank → Fin S.rank → ℂ) a.1)))
  refine sm_of_tendstoUniformly_words (iotaW σ T S) (piW θ T S) (omO S T) (h.pi_iota T S)
    (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) c (fun x => ?_) (fun l j => wordAct (heisDer ψ θ) l (u j))
    (fun l j => theta_sm h (theta_word hψ hθ l (hu j)))
    (fun a l j => dLine_eq_hD h hψ (isRealDir_lineAt hθ a.1 (z a)) _) F hF l
  refine Eq.trans ?_ (sum_coord_single x (fun a => piW θ T S (lineAt θ a.1 (z a) 1)) fun a τ i j => ?_)
  · refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    obtain ⟨τ, i, j, b⟩ := a
    cases b <;> rfl
  · have := congrFun (congrFun ((GlobalTheory.OrientedHeis.isLineAt_lineAt hθ a.1 (z a)).2.2 1 τ) i) j
    refine Eq.trans this ?_
    split_ifs <;> simp [z, *]

end GlobalTheory.ThetaDens
