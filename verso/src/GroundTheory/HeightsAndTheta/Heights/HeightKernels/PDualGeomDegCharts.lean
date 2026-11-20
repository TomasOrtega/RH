import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualGeomDegCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartDensityIntegrable
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOfPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualPtsOnPlane
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStdMassAt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter Topology Matrix NumberField
open scoped ComplexOrder

noncomputable section

namespace DualGeometricDegreeCharts

open StandardDualMassAtPoint

variable {K : Type} [Field K] [NumberField K] {T : Type} [Fintype T] [DecidableEq T]
  {D : ℕ} {F : HermLattice K (D + 1)}

def planeLin (b : Module.Basis T ℤ (dualLattice F)) (σ : K →+* ℂ) :
    (Fin (D + 1) → ℂ) →ₗ[ℂ] (((k : Unit) → dualBlocks T k) → ℂ) where
  toFun v := segre (ι := dualBlocks T) (dualPlanePt b σ v)
  map_add' v v' := by
    funext s
    simp [segre, dualPlanePt, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext s
    simp [segre, dualPlanePt, Finset.mul_sum, mul_left_comm]

def recLin (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) :
    ((Σ _ : Unit, T) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ) :=
  (LinearMap.pi fun j => LinearMap.proj (σ, j)) ∘ₗ (dualRecover b hb).toLinearMap ∘ₗ
    (LinearMap.pi fun t => LinearMap.proj ⟨(), t⟩)

omit [Fintype T] [DecidableEq T] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem recLin_apply (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ)
    (z : (Σ _ : Unit, T) → ℂ) (j : Fin (D + 1)) :
    recLin b hb σ z j = dualRecover b hb (fun t => z ⟨(), t⟩) (σ, j) := rfl

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Use function extensionality and compare the values at `j`. Rewrite using `[recLin_apply, recover_planePt]`. Simplify using the standard rewrite rules.
-/
theorem recLin_planePt (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin (D + 1) → ℂ) :
    recLin b hb σ (dualPlanePt b σ v) = v := by
  funext j
  rw [recLin_apply, recover_planePt]
  simp

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Establish `hW : dualRecover b hb (fun t => z ⟨(), t⟩) = dualRecover b hb (fun t => dualPlanePt b σ (recLin b hb σ z) ⟨(), t⟩)`. Rewrite using `[recover_planePt]`. Use function extensionality and compare the values at `⟨τ, j⟩`. Distinguish the cases in `hτ : τ = σ`. Substitute `hτ` using the available equality.

Rewrite using `[if_pos rfl]`. Both sides reduce to the same expression. Rewrite using `[if_neg hτ]`. Conclude with `hσ τ hτ j`. Establish `h1` using `(dualRecover b hb).injective hW`.

Use function extensionality and compare the values at `⟨u, t⟩`. Consider the cases of `u`. Conclude with `congrFun h1 t`.
-/
theorem eq_planePt (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {z : (Σ _ : Unit, T) → ℂ}
    {σ : K →+* ℂ} (hσ : ∀ τ : K →+* ℂ, τ ≠ σ → ∀ j, dualRecover b hb (fun t => z ⟨(), t⟩) (τ, j) = 0) :
    z = dualPlanePt b σ (recLin b hb σ z) := by
  have hW : dualRecover b hb (fun t => z ⟨(), t⟩) =
      dualRecover b hb (fun t => dualPlanePt b σ (recLin b hb σ z) ⟨(), t⟩) := by
    rw [recover_planePt]
    funext ⟨τ, j⟩
    by_cases hτ : τ = σ
    · subst hτ
      rw [if_pos rfl]
      rfl
    · rw [if_neg hτ]
      exact hσ τ hτ j
  have h1 := (dualRecover b hb).injective hW
  funext ⟨u, t⟩
  cases u
  exact congrFun h1 t

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Use `show Real.sqrt (dualNormSq b hb _) = _`. Use `congr 1`. Rewrite using `[dualNormSq, Finset.sum_eq_single σ]`. Rewrite using `[recover_planePt]`. Simplify using the standard rewrite rules.

Introduce `τ _ hτ`. Rewrite using `[recover_planePt]`. Simplify using `only [hτ, if_false]`. Use `show (star (0 : Fin (D + 1) → ℂ) ⬝ᵥ (F.metric τ *ᵥ (0 : Fin (D + 1) → ℂ))).re = 0`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
theorem h_planePt (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) (σ : K →+* ℂ) (v : Fin (D + 1) → ℂ) :
    (dualLine F b hb).h (dualPlanePt b σ v) = Real.sqrt (star v ⬝ᵥ (F.metric σ *ᵥ v)).re := by
  show Real.sqrt (dualNormSq b hb _) = _
  congr 1
  rw [dualNormSq, Finset.sum_eq_single σ]
  · rw [recover_planePt]
    simp
  · intro τ _ hτ
    rw [recover_planePt]
    simp only [hτ, if_false]
    show (star (0 : Fin (D + 1) → ℂ) ⬝ᵥ (F.metric τ *ᵥ (0 : Fin (D + 1) → ℂ))).re = 0
    simp
  · simp

/- English proof (translation)
Unfold `hermChartPot`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`.
-/
theorem hermChartPot_eq (A h : Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ) (y : Fin D → ℂ) :
    hermChartPot (Aᴴ * h * A) y =
      Real.log (Real.sqrt (star (A *ᵥ Fin.cons 1 y) ⬝ᵥ (h *ᵥ (A *ᵥ Fin.cons 1 y))).re) := by
  unfold hermChartPot
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]

omit [Fintype T] [DecidableEq T] in

/- English proof (translation)
Establish `h1` using `congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ => dualRecover b hb (fun t => w fun _ => t)) h`. Simplify using `only [segre_const, recover_planePt] at h1`. Take `⟨j, hj⟩` from `Function.ne_iff.mp hv`. Establish `h2` using `congrFun h1 (σ, j)`. Assume the negation of the conclusion as `hne`.

Conclude with `hj (by simpa [hne] using h2)`.
-/
theorem planePt_inj (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) {σ τ : K →+* ℂ}
    {v u : Fin (D + 1) → ℂ} (hv : v ≠ 0)
    (h : segre (ι := dualBlocks T) (dualPlanePt b σ v) = segre (ι := dualBlocks T) (dualPlanePt b τ u)) :
    σ = τ := by
  have h1 := congrArg (fun w : ((k : Unit) → dualBlocks T k) → ℂ =>
    dualRecover b hb (fun t => w fun _ => t)) h
  simp only [segre_const, recover_planePt] at h1
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have h2 := congrFun h1 (σ, j)
  by_contra hne
  exact hj (by simpa [hne] using h2)

/- English proof (translation)
Introduce `z hz h0`. Take `⟨σ, hσ⟩` from `hOn K (D + 1) F T b hb z hz`. Establish `hz'` using `eq_planePt b hb hσ`. Establish `hp : dualProj b hb (segre z) = recLin b hb σ z`. Use function extensionality and compare the values at `j`.

Simplify using `only [dualProj_apply, segre_const]`. Conclude with `Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)`. Rewrite `h0` using `[hp]`. Take `⟨t, ht⟩` from `hz.1 ()`. Apply `ht` to reduce the goal to its premises.

Rewrite using `[hz', h0]`. Simplify using `[dualPlanePt]`.
-/
theorem dualProj_good (hOn : DualPtsOnPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b))) :
    IsGoodProj (dualIdeal b) (dualProj b hb) := by
  intro z hz h0
  obtain ⟨σ, hσ⟩ := hOn K (D + 1) F T b hb z hz
  have hz' := eq_planePt b hb hσ
  have hp : dualProj b hb (segre z) = recLin b hb σ z := by
    funext j
    simp only [dualProj_apply, segre_const]
    exact Finset.sum_eq_single σ (fun τ _ hτ => hσ τ hτ j) (by simp)
  rw [hp] at h0
  obtain ⟨t, ht⟩ := hz.1 ()
  apply ht
  rw [hz', h0]
  simp [dualPlanePt]

/- English proof (translation)
Establish `hinj : Function.Injective (Ψ ∘ₗ planeLin b σ)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`. Assume the negation of the conclusion as `h0`. Conclude with `hΨ _ (hOf K (D + 1) F T b hb σ v h0) hv`.

Conclude with `⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩`.
-/
theorem restr_bijective (hOf : DualPtsOfPlane.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    {Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)} (hΨ : IsGoodProj (dualIdeal b) Ψ)
    (σ : K →+* ℂ) : Function.Bijective (Ψ ∘ₗ planeLin b σ) := by
  have hinj : Function.Injective (Ψ ∘ₗ planeLin b σ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra h0
    exact hΨ _ (hOf K (D + 1) F T b hb σ v h0) hv
  exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/- English proof (translation)
Set `E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ)` to `fun σ => LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)`. Set `A : (K →+* ℂ) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ` to `fun σ => LinearMap.toMatrix' (E σ).symm.toLinearMap`. Establish `hAv : ∀ σ v, A σ *ᵥ v = (E σ).symm v` using `fun σ v => LinearMap.toMatrix'_mulVec _ v`. Establish `hAbij : ∀ σ, Function.Bijective (A σ).mulVec` using `fun σ => by`. Establish `: (A σ).mulVec = (E σ).symm` using `funext (hAv σ)`.

Rewrite using `[this]`. Conclude with `(E σ).symm.bijective`. Establish `hΨA : ∀ σ v, Ψ (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ v))) = v := fun σ v => by`. Rewrite using `[hAv]`. Conclude with `(E σ).apply_symm_apply v`.

Establish `huniq : ∀ σ v c, Ψ (segre (ι` using `dualBlocks T) (dualPlanePt b σ v)) = c → v = A σ *ᵥ c := fun σ v c h => (E σ).injective (by show Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ v)) = Ψ (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ c)))`. Rewrite using `[h, hΨA])`. Establish `hne : ∀ σ (y : Fin D → ℂ), A σ *ᵥ Fin.cons 1 y ≠ 0` using `fun σ y h0 => by`. Establish `h1 : Fin.cons 1 y = (0 : Fin (D + 1) → ℂ)` using `(hAbij σ).1 (h0.trans (Matrix.mulVec_zero _).symm)`. Simplify using `using congrFun h1 0`.

Establish `hfib : ∀ y : Fin D → ℂ, fibre (dualIdeal b) Ψ y = Set.range fun σ : K →+* ℂ => segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := by`. Introduce `y`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl, hΨz⟩`.

Take `⟨σ, hσ⟩` from `hOn K (D + 1) F T b hb z hz`. Establish `hz'` using `eq_planePt b hb hσ`. Establish `hv : recLin b hb σ z = A σ *ᵥ Fin.cons 1 y` using `huniq σ _ _ (by rw [← hz']; exact hΨz)`. Use `⟨σ, ?_⟩` and prove the remaining obligations. Use `show segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) = segre z`.

Rewrite using `[← hv, ← hz']`. Introduce and unpack `⟨σ, rfl⟩`. Conclude with `⟨_, hOf K (D + 1) F T b hb σ _ (hne σ y), rfl, hΨA σ _⟩`. Establish `hsheet : ∀ σ (y : Fin D → ℂ), IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) (fun y' => dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y')) := by`. Introduce `σ y`.

Establish `hc : Differentiable ℂ (fun y' : Fin D → ℂ => (Fin.cons 1 y' : Fin (D + 1) → ℂ))`. Rewrite using `[differentiable_pi]`. Introduce `j`. Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using the standard rewrite rules.

Simplify using `using differentiable_apply (𝕜 := ℂ) k`. Use `⟨rfl, Filter.Eventually.of_forall fun y' => ⟨?_, hOf K (D + 1) F T b hb σ _ (hne σ y'), hΨA σ _⟩⟩` and prove the remaining obligations. Use `(differentiable_pi.mpr fun p => ?_) y'` and prove the remaining obligations. Simplify using `only [dualPlanePt, Matrix.mulVec, dotProduct]`. Conclude with `Differentiable.fun_sum fun j _ => (Differentiable.fun_sum fun k _ => (differentiable_pi.mp hc k).const_mul _).const_mul _`.

Establish `hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) = maDensity (fun _ : Fin D => hermChartPot ((A σ)ᴴ * F.metric σ * A σ)) y := by`. Introduce `σ y`. Establish `hex : ∃ γ, IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩`. Unfold `sheetDensity`. Rewrite using `[dif_pos hex, one_mul]`.

Apply `maDensity_congr_of_eventuallyEq` to reduce the goal to its premises. Introduce `j`. Use `set γ := hex.choose with hγdef`. Establish `hγ : IsSheet (dualIdeal b) Ψ y (segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := hex.choose_spec`. Establish `hγy : γ y = dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)`.

Use function extensionality and compare the values at `⟨u, t⟩`. Consider the cases of `u`. Establish `h1` using `congrFun hγ.1 (fun _ => t)`. Simplify `h1` using `only [segre_const]`. Establish `hcont : ContinuousAt γ y` using `(hγ.2.self_of_nhds).1.continuousAt`.

Establish `hR : ∀ᶠ y' in 𝓝 y, recLin b hb σ (γ y') ≠ 0`. Establish `hc : ContinuousAt (fun y' => recLin b hb σ (γ y')) y` using `(LinearMap.continuous_of_finiteDimensional (recLin b hb σ)).continuousAt.comp hcont`. Apply `hc.eventually_ne` to reduce the goal to its premises. Rewrite using `[hγy, recLin_planePt]`. Conclude with `hne σ y`.

Use `filter_upwards [hγ.2, hR] with y' hy' hRy'`. Take `⟨-, hmc, hΨy'⟩` from `hy'`. Take `⟨ρ, hρ⟩` from `hOn K (D + 1) F T b hb _ hmc`. Establish `hρσ : ρ = σ`. Assume the negation of the conclusion as `h`.

Apply `hRy'` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Conclude with `hρ σ (Ne.symm h) k`. Substitute `hρσ` using the available equality. Establish `hz'` using `eq_planePt b hb hρ`.

Establish `hv : recLin b hb ρ (γ y') = A ρ *ᵥ Fin.cons 1 y'` using `huniq ρ _ _ (by rw [← hz']; exact hΨy')`. Use `show Real.log ((dualLine F b hb).h (γ y')) = hermChartPot ((A ρ)ᴴ * F.metric ρ * A ρ) y'`. Rewrite using `[hz', h_planePt, hv, hermChartPot_eq]`. Establish `hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ => segre (ι` using `dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) := fun y σ τ h => planePt_inj b hb (hne σ y) h`. Use `⟨A, hAbij, ?_⟩` and prove the remaining obligations.

Establish `hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) Ψ y, sheetDensity (dualIdeal b) Ψ (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) y w = ∑ σ : K →+* ℂ, maDensity (fun _ : Fin D => hermChartPot ((A σ)ᴴ * F.metric σ * A σ)) y`. Introduce `y`. Rewrite using `[hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]`. Conclude with `Finset.sum_congr rfl fun σ _ => hdens σ y`. Unfold `ptsIntegralAt`.

Simplify using `only [hsum]`. Rewrite using `[integral_finsetSum _ fun σ _ => hInt D _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1)]`. Both sides reduce to the same expression.
-/
theorem atProj (hOn : DualPtsOnPlane.Statement) (hOf : DualPtsOfPlane.Statement)
    (hInt : ChartDensityIntegrable.Statement) (b : Module.Basis T ℤ (dualLattice F))
    (hb : Function.Bijective (Matrix.mulVecLin (dualEmbMatrix b)))
    (Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ)) (hΨ : IsGoodProj (dualIdeal b) Ψ) :
    ∃ A : (K →+* ℂ) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ, (∀ σ, Function.Bijective (A σ).mulVec) ∧
      ptsIntegralAt (e := D) (dualIdeal b) Ψ (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) =
        ∑ σ : K →+* ℂ, chartMass ((A σ)ᴴ * F.metric σ * A σ) := by
  let E : (K →+* ℂ) → (Fin (D + 1) → ℂ) ≃ₗ[ℂ] (Fin (D + 1) → ℂ) := fun σ =>
    LinearEquiv.ofBijective _ (restr_bijective hOf b hb hΨ σ)
  let A : (K →+* ℂ) → Matrix (Fin (D + 1)) (Fin (D + 1)) ℂ := fun σ =>
    LinearMap.toMatrix' (E σ).symm.toLinearMap
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
  have hdens : ∀ σ (y : Fin D → ℂ), sheetDensity (dualIdeal b) Ψ
      (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) y
      (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) =
      maDensity (fun _ : Fin D => hermChartPot ((A σ)ᴴ * F.metric σ * A σ)) y := by
    intro σ y
    have hex : ∃ γ, IsSheet (dualIdeal b) Ψ y
        (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := ⟨_, hsheet σ y⟩
    unfold sheetDensity
    rw [dif_pos hex, one_mul]
    apply maDensity_congr_of_eventuallyEq
    intro j
    set γ := hex.choose with hγdef
    have hγ : IsSheet (dualIdeal b) Ψ y
        (segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y))) γ := hex.choose_spec
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
    show Real.log ((dualLine F b hb).h (γ y')) = hermChartPot ((A ρ)ᴴ * F.metric ρ * A ρ) y'
    rw [hz', h_planePt, hv, hermChartPot_eq]
  have hinj : ∀ y : Fin D → ℂ, Function.Injective fun σ : K →+* ℂ =>
      segre (ι := dualBlocks T) (dualPlanePt b σ (A σ *ᵥ Fin.cons 1 y)) :=
    fun y σ τ h => planePt_inj b hb (hne σ y) h
  refine ⟨A, hAbij, ?_⟩
  have hsum : ∀ y : Fin D → ℂ, ∑ᶠ w ∈ fibre (dualIdeal b) Ψ y,
      sheetDensity (dualIdeal b) Ψ (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) y w =
      ∑ σ : K →+* ℂ, maDensity (fun _ : Fin D => hermChartPot ((A σ)ᴴ * F.metric σ * A σ)) y := by
    intro y
    rw [hfib y, finsum_mem_range (hinj y), finsum_eq_sum_of_fintype]
    exact Finset.sum_congr rfl fun σ _ => hdens σ y
  unfold ptsIntegralAt
  simp only [hsum]
  rw [integral_finsetSum _ fun σ _ =>
    hInt D _ ((F.posDef σ).conjTranspose_mul_mul_same (hAbij σ).1)]
  rfl

end DualGeometricDegreeCharts

open DualGeometricDegreeCharts in

/- English proof (translation)
Introduce `K _ _ i F T _ _ b hb hi`. Take `⟨D, rfl⟩ : ∃ D, i = D + 1` from `⟨i - 1, by omega⟩`. Establish `hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (dualIdeal b) Ψ` using `⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩`. Take `⟨A, hA, hE⟩` from `atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec`. Use `⟨A, hA, ?_⟩` and prove the remaining obligations.

Use `show ptsIntegral (e := D) (dualIdeal b) (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = _`. Unfold `ptsIntegral`. Rewrite using `[dif_pos hex]`. Conclude with `hE`.
-/
theorem DualGeomDegCharts.proof (hInt : ChartDensityIntegrable.Statement) : DualGeomDegCharts.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨D, rfl⟩ : ∃ D, i = D + 1 := ⟨i - 1, by omega⟩
  have hex : ∃ Ψ : (((k : Unit) → dualBlocks T k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ),
      IsGoodProj (dualIdeal b) Ψ := ⟨_, dualProj_good DualPtsOnPlane.proof b hb⟩
  obtain ⟨A, hA, hE⟩ := atProj DualPtsOnPlane.proof DualPtsOfPlane.proof hInt b hb hex.choose hex.choose_spec
  refine ⟨A, hA, ?_⟩
  show ptsIntegral (e := D) (dualIdeal b) (fun _ z => Real.log ((dualLine F b hb).h z)) (fun _ => 1) = _
  unfold ptsIntegral
  rw [dif_pos hex]
  exact hE

end

end GroundTheory.Heights₂.Heights
