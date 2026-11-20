import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnitaryPointsDiscreteFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesKernelSummableWithBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousAutomorphicKernelDiscreteSeriesTestStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.KernelConv

/- English proof (translation)
Take `⟨⟨h1, hmul⟩, hnorm, -⟩` from `hσ`. Establish `hg : uMat g ∈ UJset ε` using `g.2`. Establish `hgi : uMat g⁻¹ ∈ UJset ε` using `(g⁻¹).2`. Establish `hone : uMat g * uMat g⁻¹ = 1` using `by show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1`. Simplify using the standard rewrite rules.

Establish `hback : σ (uMat g) (σ (uMat g⁻¹) w) = w`. Use `congrArg (fun T : H →L[ℂ] H => T w) (hmul _ hg _ hgi)` as an intermediate fact. Simplify using `only [hone, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this`. Conclude with `this.symm`. Set `L : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (σ (uMat g) : H →ₗ[ℂ] H), norm_map' := hnorm _ hg }`.

Establish `key : ⟪w, σ (uMat g⁻¹) w⟫_ℂ = ⟪σ (uMat g) w, w⟫_ℂ`. Rewrite using `[← L.inner_map_map w (σ (uMat g⁻¹) w)]`. Use `show ⟪σ (uMat g) w, σ (uMat g) (σ (uMat g⁻¹) w)⟫_ℂ = _`. Rewrite using `[hback]`. Rewrite using `[key, ← inner_conj_symm]`.

Both sides reduce to the same expression.
-/
theorem coef_inv {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) (w : H) (g : UJ ε) :
    ⟪w, σ (uMat g⁻¹) w⟫_ℂ = star ⟪w, σ (uMat g) w⟫_ℂ := by
  obtain ⟨⟨h1, hmul⟩, hnorm, -⟩ := hσ
  have hg : uMat g ∈ UJset ε := g.2
  have hgi : uMat g⁻¹ ∈ UJset ε := (g⁻¹).2
  have hone : uMat g * uMat g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      (((g⁻¹ : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    simp
  have hback : σ (uMat g) (σ (uMat g⁻¹) w) = w := by
    have := congrArg (fun T : H →L[ℂ] H => T w) (hmul _ hg _ hgi)
    simp only [hone, h1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at this
    exact this.symm
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ (uMat g) : H →ₗ[ℂ] H), norm_map' := hnorm _ hg }
  have key : ⟪w, σ (uMat g⁻¹) w⟫_ℂ = ⟪σ (uMat g) w, w⟫_ℂ := by
    rw [← L.inner_map_map w (σ (uMat g⁻¹) w)]
    show ⟪σ (uMat g) w, σ (uMat g) (σ (uMat g⁻¹) w)⟫_ℂ = _
    rw [hback]
  rw [key, ← inner_conj_symm]
  rfl

/- English proof (translation)
Establish `he : B.e x⁻¹.2 = star (B.e x.2)` using `B.e_adm.2.2.1 x.2`. Establish `hp : ∏ v, ⟪B.w v, B.σ v (uMat (x⁻¹.1 v)) (B.w v)⟫_ℂ = star (∏ v, ⟪B.w v, B.σ v (uMat (x.1 v)) (B.w v)⟫_ℂ)`. Rewrite using `[star_prod]`. Use `Finset.prod_congr rfl (fun v _ => ?_)` and prove the remaining obligations. Use `show ⟪B.w v, B.σ v (uMat (x.1 v)⁻¹) (B.w v)⟫_ℂ = _`.

Conclude with `coef_inv (hd v).2.1.2.2.1 (B.w v) (x.1 v)`. Unfold `phe ph`. Rewrite using `[he, hp]`. Simplify using `only [star_mul', star_star]`. Rewrite using `[show star ((∏ v, d v : ℝ) : ℂ) = ((∏ v, d v : ℝ) : ℂ) from Complex.conj_ofReal _]`.
-/
theorem phe_inv (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (hd : IsDSData B d) (x : B.I.GA) :
    phe B d x⁻¹ = star (phe B d x) := by
  have he : B.e x⁻¹.2 = star (B.e x.2) := B.e_adm.2.2.1 x.2
  have hp : ∏ v, ⟪B.w v, B.σ v (uMat (x⁻¹.1 v)) (B.w v)⟫_ℂ =
      star (∏ v, ⟪B.w v, B.σ v (uMat (x.1 v)) (B.w v)⟫_ℂ) := by
    rw [star_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    show ⟪B.w v, B.σ v (uMat (x.1 v)⁻¹) (B.w v)⟫_ℂ = _
    exact coef_inv (hd v).2.1.2.2.1 (B.w v) (x.1 v)
  unfold phe ph
  rw [he, hp]
  simp only [star_mul', star_star]
  rw [show star ((∏ v, d v : ℝ) : ℂ) = ((∏ v, d v : ℝ) : ℂ) from Complex.conj_ofReal _]

/- English proof (translation)
Unfold `kern`. Conclude with `((Equiv.subtypeEquivRight (fun a => by rw [← hΓ, SetLike.mem_coe]) : Γ ≃ I.GFset).tsum_eq (fun γ : I.GFset => φ (x⁻¹ * γ.1 * y))).symm`.
-/
theorem kern_eq (I : AutInst) (Γ : Subgroup I.GA) (hΓ : (Γ : Set I.GA) = I.GFset) (φ : I.GA → ℂ) (x y : I.GA) :
    kern I φ x y = ∑' γ : Γ, φ (x⁻¹ * γ.1 * y) := by
  unfold kern
  exact ((Equiv.subtypeEquivRight (fun a => by rw [← hΓ, SetLike.mem_coe]) : Γ ≃ I.GFset).tsum_eq
    (fun γ : I.GFset => φ (x⁻¹ * γ.1 * y))).symm

/- English proof (translation)
Establish `hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset` using `rfl`. Establish `hγΓ : γ ∈ GlobalTheory.RatDiscrete.ratSub I` using `hγ`. Rewrite using `[kern_eq I _ hΓ, kern_eq I _ hΓ, kern_eq I _ hΓ]`. Prove the components needed by the constructor for the conclusion. Use `((Equiv.mulLeft (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)).tsum_eq (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ ((γ * x)⁻¹ * δ.1 * y))).symm.trans ?_` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `δ`. Simplify using `[mul_assoc]`. Use `((Equiv.mulRight (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)⁻¹).tsum_eq (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (x⁻¹ * δ.1 * (γ * y)))).symm.trans ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `δ`. Simplify using `[mul_assoc]`.
-/
theorem kern_invariant (I : AutInst) (φ : I.GA → ℂ) (γ : I.GA) (hγ : γ ∈ I.GFset) (x y : I.GA) :
    kern I φ (γ * x) y = kern I φ x y ∧ kern I φ x (γ * y) = kern I φ x y := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  have hγΓ : γ ∈ GlobalTheory.RatDiscrete.ratSub I := hγ
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, kern_eq I _ hΓ]
  constructor
  · refine ((Equiv.mulLeft (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ ((γ * x)⁻¹ * δ.1 * y))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]
  · refine ((Equiv.mulRight (⟨γ, hγΓ⟩ : GlobalTheory.RatDiscrete.ratSub I)⁻¹).tsum_eq
      (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (x⁻¹ * δ.1 * (γ * y)))).symm.trans ?_
    congr 1; funext δ; simp [mul_assoc]

/- English proof (translation)
Establish `hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset` using `rfl`. Rewrite using `[kern_eq I _ hΓ, kern_eq I _ hΓ, tsum_star]`. Use `((Equiv.inv (GlobalTheory.RatDiscrete.ratSub I)).tsum_eq (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (y⁻¹ * δ.1 * x))).symm.trans ?_` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `δ`.

Rewrite using `[← hφ]`. Simplify using `[mul_assoc]`.
-/
theorem kern_symm (I : AutInst) (φ : I.GA → ℂ) (hφ : ∀ x, φ x⁻¹ = star (φ x)) (x y : I.GA) :
    kern I φ y x = star (kern I φ x y) := by
  have hΓ : ((GlobalTheory.RatDiscrete.ratSub I : Subgroup I.GA) : Set I.GA) = I.GFset := rfl
  rw [kern_eq I _ hΓ, kern_eq I _ hΓ, tsum_star]
  refine ((Equiv.inv (GlobalTheory.RatDiscrete.ratSub I)).tsum_eq
    (fun δ : GlobalTheory.RatDiscrete.ratSub I => φ (y⁻¹ * δ.1 * x))).symm.trans ?_
  congr 1; funext δ
  rw [← hφ]
  simp [mul_assoc]

/- English proof (translation)
Unfold `KernelA`. Introduce `B d h hd hn hL hH`. Use `⟨GlobalTheory.T.discreteSeriesKernel_summable_with_bound B d h hd hn hL hH, GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest B d h hd hn hL hH, ?_, ?_⟩` and prove the remaining obligations. Introduce `γ hγ x y`. Conclude with `kern_invariant B.I (phe B d) γ hγ x y`.

Introduce `x y`. Conclude with `kern_symm B.I (phe B d) (phe_inv B d hd) x y`.
-/
theorem kernelA : KernelA := by
  unfold KernelA
  intro B d h hd hn hL hH
  refine ⟨GlobalTheory.T.discreteSeriesKernel_summable_with_bound B d h hd hn hL hH, GlobalTheory.T.continuous_automorphicKernel_discreteSeriesTest B d h hd hn hL hH, ?_, ?_⟩
  · intro γ hγ x y
    exact kern_invariant B.I (phe B d) γ hγ x y
  · intro x y
    exact kern_symm B.I (phe B d) (phe_inv B d hd) x y

end GlobalTheory.KernelConv
