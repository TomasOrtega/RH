import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

open MeasureTheory NumberField Matrix Finset in

/- English proof (translation)
Take `⟨W, hW⟩` from `Submodule.exists_isCompl V`. Set `P` to `Submodule.linearProjOfIsCompl V W hW`. Set `b` to `Module.finBasis ℂ V`. Set `g : X → ℂ` to `fun x => (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det`. Establish `hg : Continuous g`.

Use `Continuous.matrix_det ?_` and prove the remaining obligations. Use `continuous_matrix fun i k => ?_` and prove the remaining obligations. Establish `hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i` using `(((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional`. Conclude with `hL.comp (hf.matrix_mulVec continuous_const)`. Establish `hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V}`.

Simplify using `only [Set.setOf_forall]`. Use `isClosed_biInter fun y _ => ?_` and prove the remaining obligations. Conclude with `V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)`. Establish `heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) = fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0`. Use function extensionality and compare the values at `x`.

Unfold `_root_.GlobalTheory.FlagMeas.detOn`. Distinguish the cases in `h : ∀ y ∈ V, (toLin' (f x)) y ∈ V`. Establish `h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V}` using `fun y hy => by`. Simplify `h y hy` using `[Matrix.toLin'_apply]`. Rewrite using `[dif_pos h, if_pos h', ← LinearMap.det_toMatrix b]`.

Use `congr 2`. Use extensionality with `i k`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.of_apply]`. Use `congr 2`. Establish `hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ)`.

Simplify using `[LinearMap.restrict_apply, Matrix.toLin'_apply]`. Rewrite using `[hm]`. Conclude with `(Submodule.projectionOnto_apply_left hW _).symm`. Establish `h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V}` using `fun hx => h fun y hy => by`. Simplify `hx y hy` using `[Matrix.toLin'_apply]`.

Rewrite using `[dif_neg h, if_neg h']`. Rewrite using `[heq]`. Conclude with `Measurable.ite hS.measurableSet hg.norm.measurable measurable_const`.
-/
theorem _root_.GlobalTheory.FlagMeas.measurable_detOn_comp {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] {n : ℕ}
    (f : X → Matrix (Fin n) (Fin n) ℂ) (hf : Continuous f) (V : Submodule ℂ (Fin n → ℂ)) :
    Measurable fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl V
  let P := Submodule.linearProjOfIsCompl V W hW
  let b := Module.finBasis ℂ V
  let g : X → ℂ := fun x =>
    (Matrix.of fun i k => b.repr (P (f x *ᵥ (b k : Fin n → ℂ))) i).det
  have hg : Continuous g := by
    refine Continuous.matrix_det ?_
    refine continuous_matrix fun i k => ?_
    have hL : Continuous fun v : Fin n → ℂ => b.repr (P v) i :=
      (((Finsupp.lapply i).comp b.repr.toLinearMap).comp P).continuous_of_finiteDimensional
    exact hL.comp (hf.matrix_mulVec continuous_const)
  have hS : IsClosed {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := by
    simp only [Set.setOf_forall]
    refine isClosed_biInter fun y _ => ?_
    exact V.closed_of_finiteDimensional.preimage (hf.matrix_mulVec continuous_const)
  have heq : (fun x => _root_.GlobalTheory.FlagMeas.detOn (f x) V) =
      fun x => if x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} then ‖g x‖ else 0 := by
    funext x
    unfold _root_.GlobalTheory.FlagMeas.detOn
    by_cases h : ∀ y ∈ V, (toLin' (f x)) y ∈ V
    · have h' : x ∈ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun y hy => by
        simpa [Matrix.toLin'_apply] using h y hy
      rw [dif_pos h, if_pos h', ← LinearMap.det_toMatrix b]
      congr 2
      ext i k
      rw [LinearMap.toMatrix_apply, Matrix.of_apply]
      congr 2
      have hm : f x *ᵥ (b k : Fin n → ℂ) = ((toLin' (f x)).restrict h (b k) : Fin n → ℂ) := by
        simp [LinearMap.restrict_apply, Matrix.toLin'_apply]
      rw [hm]
      exact (Submodule.projectionOnto_apply_left hW _).symm
    · have h' : x ∉ {x | ∀ y ∈ V, f x *ᵥ y ∈ V} := fun hx => h fun y hy => by
        simpa [Matrix.toLin'_apply] using hx y hy
      rw [dif_neg h, if_neg h']
  rw [heq]
  exact Measurable.ite hS.measurableSet hg.norm.measurable measurable_const

open MeasureTheory NumberField Matrix Finset in

/- English proof (translation)
Establish `hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g`. Unfold `_root_.Formalism.MainNotions.S.uMat`. Conclude with `Units.continuous_val.comp continuous_subtype_val`. Unfold `_root_.GlobalTheory.FlagMeas.locSize`. Conclude with `((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _`.
-/
theorem _root_.GlobalTheory.FlagMeas.measurable_locSize_uMat (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ)
    (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (i : Fin a) :
    Measurable fun g : _root_.Formalism.REAL.UJ ε => _root_.GlobalTheory.FlagMeas.locSize j W (_root_.Formalism.MainNotions.S.uMat g) i := by
  have hc : Continuous fun g : _root_.Formalism.REAL.UJ ε => _root_.Formalism.MainNotions.S.uMat g := by
    unfold _root_.Formalism.MainNotions.S.uMat
    exact Units.continuous_val.comp continuous_subtype_val
  unfold _root_.GlobalTheory.FlagMeas.locSize
  exact ((_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _).div
    (_root_.GlobalTheory.FlagMeas.measurable_detOn_comp _ hc _)).pow_const _

end GlobalTheory.FlagMeas
