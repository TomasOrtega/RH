import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergyCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergyIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualGeomDegCharts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualEnergyChartsAlt

open StandardDualMassAtPoint DualGeometricDegreeCharts

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

def chartMat (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ :=
  LinearMap.toMatrix' (LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)).symm.toLinearMap

/- English proof (translation)
Use `set A := chartMat hOf b hb hΨ with hAdef`. Set `E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ)` to `fun σ => LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)`. Establish `hAv : ∀ σ v, A σ *ᵥ v = (E σ).symm v` using `fun σ v => LinearMap.toMatrix'_mulVec _ v`. Establish `hAbij : ∀ σ, Function.Bijective (A σ).mulVec` using `fun σ => by`. Establish `: (A σ).mulVec = (E σ).symm` using `funext (hAv σ)`.

Rewrite using `[this]`. Conclude with `(E σ).symm.bijective`. Establish `hΨA : ∀ σ v, Ψ (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ v))) = v := fun σ v => by`. Rewrite using `[hAv]`. Conclude with `(E σ).apply_symm_apply v`.

Establish `huniq : ∀ σ v c, Ψ (segre (ι` using `dualBlocks T) (dualPlanePt b σ v)) = c → v = A σ *ᵥ c := fun σ v c h => (E σ).injective (by show Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) = Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ c)))`. Rewrite using `[h, hΨA])`. Establish `hne : ∀ σ (y : Fin D → ℂ), A σ *ᵥ Fin.cons 1 y ≠ 0` using `fun σ y h0 => by`. Establish `h1 : Fin.cons 1 y = (0 : Fin (D + 1) → ℂ)` using `(hAbij σ).1 (h0.trans (Matrix.mulVec_zero _).symm)`. Simplify using `using congrFun h1 0`.

Establish `hfib : ∀ y : Fin D → ℂ, fibre (dualIdeal b) Ψ y = Set.range fun σ : K →+* ℂ => segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := by`. Introduce `y`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl, hΨz⟩`.

Take `⟨σ, hσ⟩` from `hOn K (D + 1) F T b hb z hz`. Establish `hz'` using `eq_planePt b hb hσ`. Establish `hv : recLin b hb σ z = A σ *ᵥ Fin.cons 1 y` using `huniq σ _ _ (by rw [← hz']; exact hΨz)`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use `show segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) = segre z`.

Rewrite using `[← hv, ← hz']`. Introduce and unpack `⟨σ, rfl⟩`. Conclude with `⟨_, hOf K (D + 1) F T b hb σ _ (hne σ y), rfl, hΨA σ _⟩`. Establish `hsheet : ∀ σ (y : Fin D → ℂ), IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) (fun y' => dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y')) := by`. Introduce `σ y`.

Establish `hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ))`. Rewrite using `[differentiable_pi]`. Introduce `j`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `using differentiable_apply (𝕜 := ℂ) k`. Use `⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, hOf K (D + 1) F T b hb σ _ (hne σ y'), hΨA σ _⟩⟩` and prove the remaining obligations. Use `(differentiable_pi.mpr fun p => ?_) y'` and prove the remaining obligations. Simplify using `only [dualPlanePt, Matrix.mulVec, dotProduct]`. Conclude with `Differentiable.fun_sum fun j _ => (Differentiable.fun_sum fun k _ => (differentiable_pi.mp hc k).const_mul _).const_mul _`.

Establish `hnear : ∀ σ (y : Fin D → ℂ) γ, IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ → ∀ᶠ y' in 𝓝 y, γ y' = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y') := by`. Introduce `σ y γ hγ`. Establish `hγy : γ y = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)`. Use function extensionality and compare the values at `⟨u, t⟩`. Consider the cases of `u`.

Establish `h1` using `congrFun hγ.1 (fun _ => t)`. Simplify `h1` using `only [segre_const]`. Establish `hcont : ContinuousAt γ y` using `(hγ.2.self_of_nhds).1.continuousAt`. Establish `hR : ∀ᶠ y' in 𝓝 y, recLin b hb σ (γ y') ≠ 0`. Establish `hc : ContinuousAt (fun y' => recLin b hb σ (γ y')) y` using `(LinearMap.continuous_of_finiteDimensional (recLin b hb σ)).continuousAt.comp hcont`.

Apply `hc.eventually_ne` to reduce the goal to its premises. Rewrite using `[hγy, recLin_planePt]`. Conclude with `hne σ y`. Use `filter_upwards [hγ.2, hR] with y' hy' hRy'`. Take `⟨-, hmc, hΨy'⟩` from `hy'`.

Take `⟨ρ, hρ⟩` from `hOn K (D + 1) F T b hb _ hmc`. Establish `hρσ : ρ = σ`. Assume the negation of the conclusion as `h`. Apply `hRy'` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Conclude with `hρ σ (Ne.symm h) k`. Substitute `hρσ` using the available equality. Establish `hz'` using `eq_planePt b hb hρ`. Establish `hv : recLin b hb ρ (γ y') = A ρ *ᵥ Fin.cons 1 y'` using `huniq ρ _ _ (by rw [← hz']; exact hΨy')`. Rewrite using `[hz', hv]`.

Establish `hpotF : ∀ σ (y' : Fin D → ℂ), Real.log ((dualLine F b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) = hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y'` using `fun σ y' => by`. Rewrite using `[h_planePt, hermChartPot_eq]`. Establish `hpotS : ∀ σ (y' : Fin D → ℂ), Real.log ((dualLine F.withStdMetric b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) = hermChartPot ((A σ)ᴴ * A σ) y'` using `fun σ y' => by`. Establish `h1` using `h_planePt (F := F.withStdMetric) b hb σ (A σ *ᵥ Fin.cons 1 y')`. Establish `h2` using `hermChartPot_eq (A σ) (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) y'`.

Rewrite `h2` using `[Matrix.mul_one]`. Rewrite using `[h2]`. Conclude with `congrArg Real.log h1`. Use `⟨hAbij, fun k => ?_⟩` and prove the remaining obligations. Establish `hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb) (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) = (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) * maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ) else hermChartPot ((A σ)ᴴ * A σ)) y := by`.

Introduce `σ y`. Establish `hex : ∃ γ, IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩`. Unfold `sheetDensity`. Rewrite using `[dif_pos hex]`. Establish `hev` using `hnear σ y _ hex.choose_spec`.

Use `beta_reduce`. Rewrite using `[hev.self_of_nhds, hpotF, hpotS]`. Use `congr 1`. Apply `maDensity_congr_of_eventuallyEq` to reduce the goal to its premises. Introduce `j`.

Use `filter_upwards [hev] with y' hy'`. Simplify using `only [pot]`. Rewrite using `[hy']`. Use `split_ifs`. Conclude with `hpotF σ y'`.

Conclude with `hpotS σ y'`. Establish `hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ => segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := fun y σ τ h => planePt_inj b hb (hne σ y) h`. Establish `hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) Ψ y, sheetDensity (dualIdeal b) Ψ (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb) (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y w = ∑ …`. Introduce `y`. Rewrite using `[hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]`.

Conclude with `Finset.sum_congr rfl fun σ _ => hdens σ y`. Establish `hN : ∀ σ, ((A σ)ᴴ * A σ).PosDef` using `fun σ => by`. Simplify using `using (Matrix.PosDef.one (n := Fin (D + 1)) (R := ℂ)).conjTranspose_mul_mul_same (hAbij σ).1`. Unfold `ptsIntegralAt`. Simplify using `only [hsum]`.

Rewrite using `[integral_finsetSum _ fun σ _ => hInt D _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1) (hN σ) k]`. Both sides reduce to the same expression.
-/
theorem atProj (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartEnergyIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    (∀ σ, Function.Bijective (chartMat hOf b hb hΨ σ).mulVec) ∧ ∀ k : ℕ,
      ptsIntegralAt (e := D) (dualIdeal b) Ψ
          (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
          (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) =
        ∑ σ : K →+* ℂ, chartMixedEnergy ((chartMat hOf b hb hΨ σ)ᴴ * F.metric σ * chartMat hOf b hb hΨ σ)
          ((chartMat hOf b hb hΨ σ)ᴴ * chartMat hOf b hb hΨ σ) k := by
  set A := chartMat hOf b hb hΨ with hAdef
  let E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ) := fun σ =>
    LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)
  have hAv : ∀ σ v, A σ *ᵥ v = (E σ).symm v := fun σ v => LinearMap.toMatrix'_mulVec _ v
  have hAbij : ∀ σ, Function.Bijective (A σ).mulVec := fun σ => by
    have : (A σ).mulVec = (E σ).symm := funext (hAv σ)
    rw [this]
    exact (E σ).symm.bijective
  have hΨA : ∀ σ v, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ v))) = v := fun σ v => by
    rw [hAv]
    exact (E σ).apply_symm_apply v
  have huniq : ∀ σ v c, Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) = c → v = A σ *ᵥ c :=
    fun σ v c h => (E σ).injective (by
      show Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) =
        Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ c)))
      rw [h, hΨA])
  have hne : ∀ σ (y : Fin D → ℂ), A σ *ᵥ Fin.cons 1 y ≠ 0 := fun σ y h0 => by
    have h1 : Fin.cons 1 y = (0 : Fin (D + 1) → ℂ) := (hAbij σ).1 (h0.trans (Matrix.mulVec_zero _).symm)
    simpa using congrFun h1 0
  have hfib : ∀ y : Fin D → ℂ, fibre (dualIdeal b) Ψ y =
      Set.range fun σ : K →+* ℂ => segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := by
    intro y
    ext w
    constructor
    · rintro ⟨z, hz, rfl, hΨz⟩
      obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
      have hz' := eq_planePt b hb hσ
      have hv : recLin b hb σ z = A σ *ᵥ Fin.cons 1 y := huniq σ _ _ (by rw [← hz']; exact hΨz)
      refine ⟨σ, ?_⟩
      show segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) = segre z
      rw [← hv, ← hz']
    · rintro ⟨σ, rfl⟩
      exact ⟨_, hOf K (D + 1) F T b hb σ _ (hne σ y), rfl, hΨA σ _⟩
  have hsheet : ∀ σ (y : Fin D → ℂ), IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)))
      (fun y' => dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y')) := by
    intro σ y
    have hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ)) := by
      rw [differentiable_pi]
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simpa using differentiable_apply (𝕜 := ℂ) k
    refine ⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, hOf K (D + 1) F T b hb σ _ (hne σ y'), hΨA σ _⟩⟩
    refine (differentiable_pi.mpr fun p => ?_) y'
    simp only [dualPlanePt, Matrix.mulVec, dotProduct]
    exact Differentiable.fun_sum fun j _ =>
      (Differentiable.fun_sum fun k _ => (differentiable_pi.mp hc k).const_mul _).const_mul _

  have hnear : ∀ σ (y : Fin D → ℂ) γ, IsSheet (dualIdeal b) Ψ y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ →
      ∀ᶠ y' in 𝓝 y, γ y' = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y') := by
    intro σ y γ hγ
    have hγy : γ y = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y) := by
      funext ⟨u, t⟩
      cases u
      have h1 := congrFun hγ.1 (fun _ => t)
      simpa only [segre_const] using h1
    have hcont : ContinuousAt γ y := (hγ.2.self_of_nhds).1.continuousAt
    have hR : ∀ᶠ y' in 𝓝 y, recLin b hb σ (γ y') ≠ 0 := by
      have hc : ContinuousAt (fun y' => recLin b hb σ (γ y')) y :=
        (LinearMap.continuous_of_finiteDimensional (recLin b hb σ)).continuousAt.comp hcont
      apply hc.eventually_ne
      rw [hγy, recLin_planePt]
      exact hne σ y
    filter_upwards [hγ.2, hR] with y' hy' hRy'
    obtain ⟨-, hmc, hΨy'⟩ := hy'
    obtain ⟨ρ, hρ⟩ := hOn K (D + 1) F T b hb _ hmc
    have hρσ : ρ = σ := by
      by_contra h
      apply hRy'
      funext k
      exact hρ σ (Ne.symm h) k
    subst hρσ
    have hz' := eq_planePt b hb hρ
    have hv : recLin b hb ρ (γ y') = A ρ *ᵥ Fin.cons 1 y' :=
      huniq ρ _ _ (by rw [← hz']; exact hΨy')
    rw [hz', hv]

  have hpotF : ∀ σ (y' : Fin D → ℂ), Real.log ((dualLine F b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y' := fun σ y' => by
    rw [h_planePt, hermChartPot_eq]
  have hpotS : ∀ σ (y' : Fin D → ℂ),
      Real.log ((dualLine F.withStdMetric b hb).h (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y'))) =
      hermChartPot ((A σ)ᴴ * A σ) y' := fun σ y' => by
    have h1 := h_planePt (F := F.withStdMetric) b hb σ (A σ *ᵥ Fin.cons 1 y')
    have h2 := hermChartPot_eq (A σ) (1 : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) y'
    rw [Matrix.mul_one] at h2
    rw [h2]
    exact congrArg Real.log h1
  refine ⟨hAbij, fun k => ?_⟩
  have hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) =
      (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro σ y
    have hex : ∃ γ, IsSheet (dualIdeal b) Ψ y
        (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩
    unfold sheetDensity
    rw [dif_pos hex]
    have hev := hnear σ y _ hex.choose_spec
    beta_reduce
    rw [hev.self_of_nhds, hpotF, hpotS]
    congr 1
    apply maDensity_congr_of_eventuallyEq
    intro j
    filter_upwards [hev] with y' hy'
    simp only [pot]
    rw [hy']
    split_ifs
    · exact hpotF σ y'
    · exact hpotS σ y'
  have hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ =>
      segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) :=
    fun y σ τ h => planePt_inj b hb (hne σ y) h
  have hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) Ψ y,
      sheetDensity (dualIdeal b) Ψ
        (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
        (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) y w =
      ∑ σ : K →+* ℂ, (hermChartPot ((A σ)ᴴ * F.metric σ * A σ) y - hermChartPot ((A σ)ᴴ * A σ) y) *
        maDensity (fun j : Fin D => if (j : ℕ) < k then hermChartPot ((A σ)ᴴ * F.metric σ * A σ)
          else hermChartPot ((A σ)ᴴ * A σ)) y := by
    intro y
    rw [hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hdens σ y
  have hN : ∀ σ, ((A σ)ᴴ * A σ).PosDef := fun σ => by
    simpa using (Matrix.PosDef.one (n := Fin (D + 1)) (R := ℂ)).conjTranspose_mul_mul_same (hAbij σ).1
  unfold ptsIntegralAt
  simp only [hsum]
  rw [integral_finsetSum _ fun σ _ =>
    hInt D _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1) (hN σ) k]
  rfl

end DualEnergyChartsAlt

open DualEnergyChartsAlt DualGeometricDegreeCharts in

/- English proof (translation)
Introduce `K _ _ i F T _ _ b hb hi`. Take `⟨D, rfl⟩ : ∃ D, i = D + 1` from `⟨i - 1, by omega⟩`. Establish `hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (dualIdeal b) Ψ` using `⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩`. Take `⟨hA, hE⟩` from `atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec`. Use `⟨chartMat DualPtsOfPlane.proof b hb hex.choose_spec, hA, fun k => ?_⟩` and prove the remaining obligations.

Use `show ptsIntegral (e := D) (dualIdeal b) (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb) (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = _`. Unfold `ptsIntegral`. Rewrite using `[dif_pos hex]`. Conclude with `hE k`.
-/
theorem DualEnergyCharts.proof (hInt : ChartEnergyIntegrable.Statement) : DualEnergyCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨chartMat DualPtsOfPlane.proof b hb hex.choose_spec, hA, fun k => ?_⟩
  show ptsIntegral (e := D) (dualIdeal b)
      (pot fun j : Fin D => if (j : ℕ) < k then dualLine F b hb else dualLine F.withStdMetric b hb)
      (fun z => Real.log ((dualLine F b hb).h z) - Real.log ((dualLine F.withStdMetric b hb).h z)) = _
  unfold ptsIntegral
  rw [dif_pos hex]
  exact hE k

end

end GroundTheory.Heights₂.Heights
