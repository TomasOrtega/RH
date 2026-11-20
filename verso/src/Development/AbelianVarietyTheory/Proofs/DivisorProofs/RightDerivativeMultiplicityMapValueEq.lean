import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsUnitaryRepStableConjSkewAdjointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtSobolevContinuousOrbitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.MultDer

/- English proof (translation)
Introduce `k Xs _`. Simplify using `only [map_zero]`. Conclude with `contDiff_const`.
-/
theorem smoothVec_zero {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (L : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : SmoothVec L π 0 := by
  intro k Xs _
  simp only [map_zero]
  exact contDiff_const

/- English proof (translation)
Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hx`. Consider the case `zero => exact smoothVec_zero _ _`. Consider the case `add x y _ _ hx hy`. Introduce `k Xs h`.

Simplify using `only [map_add]`. Conclude with `(hx k Xs h).add (hy k Xs h)`. Consider the case `smul c x _ hx`. Introduce `k Xs h`. Simplify using `only [map_smul]`.

Conclude with `(hx k Xs h).const_smul c`.
-/
theorem smoothVec_of_mem {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {w : M.H τ} (hw : w ∈ M.sm τ) : SmoothVec (lieAt V τ) (M.rep τ) w := by
  induction hw using Submodule.span_induction with
  | mem x hx => exact hx
  | zero => exact smoothVec_zero _ _
  | add x y _ _ hx hy =>
    intro k Xs h
    simp only [map_add]
    exact (hx k Xs h).add (hy k Xs h)
  | smul c x _ hx =>
    intro k Xs h
    simp only [map_smul]
    exact (hx k Xs h).const_smul c

/- English proof (translation)
Introduce `D θ V S M J χ T _ hT v τ`. Establish `hs` using `smoothVec_of_mem M τ (v τ).2`. Use `⟨hs, fun X hX => ?_⟩` and prove the remaining obligations. Establish `hH` using `GlobalTheory.SmoothAutCheck.gramAt_herm V τ`. Establish `hU` using `GlobalTheory.SmoothAutCheck.gramAt_unit V τ`.

Establish `hπ` using `(GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1`. Take `⟨h1, -, h3⟩` from `GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hπ _ hs`. Use `⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Take `⟨ℓ, hℓ, hℓT⟩` from `hT.cont τ v x`.

Establish `hd` using `GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX`. Rewrite using `[← hℓT]`. Establish `e : (fun t : ℝ => T v (x * oneP θ V τ X t)) = fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ))`. Use function extensionality and compare the values at `t`. Establish `hg` using `GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t`.

Set `w : M.sm τ` to `⟨_, Submodule.subset_span (h1 _ hg)⟩`. Establish `h4` using `congrFun (hT.equiv τ _ hg v w rfl) x`. Conclude with `((hℓT w).trans h4).symm`. Use `show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _`. Rewrite using `[e]`.

Conclude with `hd.deriv`.
-/
theorem rder_eq : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M), IsInfFam θ → IsMultMap θ M J χ T → ∀ (v : M.Vec) (τ : D.what₂.Tau), SmoothVec (lieAt V τ) (M.rep τ) (v τ : M.H τ) ∧ ∀ X ∈ lieAt V τ, ∃ u : M.sm τ, (u : M.H τ) = dRep (M.rep τ) X (v τ : M.H τ) ∧ Rder θ V τ X (T v) = T (Function.update v τ u) := by
  intro D θ V S M J χ T _ hT v τ
  have hs := smoothVec_of_mem M τ (v τ).2
  refine ⟨hs, fun X hX => ?_⟩
  have hH := GlobalTheory.SmoothAutCheck.gramAt_herm V τ
  have hU := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have hπ := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.smoothVectors_unitaryRep_stable_conj_skewAdjoint _ _ _ _ hH hU hπ _ hs
  refine ⟨⟨_, Submodule.subset_span (h3 X hX).1⟩, rfl, ?_⟩
  funext x
  obtain ⟨ℓ, hℓ, hℓT⟩ := hT.cont τ v x
  have hd := GlobalTheory.T.hasDerivAt_sobolevContinuous_orbit _ _ _ _ hH hU hπ _ hs ℓ hℓ X hX
  rw [← hℓT]
  have e : (fun t : ℝ => T v (x * oneP θ V τ X t)) =
      fun t : ℝ => ℓ (M.rep τ (NormedSpace.exp (t • X)) (v τ : M.H τ)) := by
    funext t
    have hg := GlobalTheory.SmoothAutCheck.exp_mem_UH hU hX t
    let w : M.sm τ := ⟨_, Submodule.subset_span (h1 _ hg)⟩
    have h4 := congrFun (hT.equiv τ _ hg v w rfl) x
    exact ((hℓT w).trans h4).symm
  show deriv (fun t : ℝ => T v (x * oneP θ V τ X t)) 0 = _
  rw [e]
  exact hd.deriv

end GlobalTheory.HolRead.MultDer
