import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

/- English proof (translation)
Use `haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))`. Conclude with `(Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace`.
-/
theorem measPolish_UJ (n : ℕ) (ε : Fin n → Bool) : PolishSpace (Formalism.REAL.UJ ε) := by
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℂ) := inferInstanceAs (PolishSpace (Fin n → Fin n → ℂ))
  exact (Formalism.REAL.isClosedEmbeddingMatrix n ε).1.polishSpace

variable {D : D7}

/- English proof (translation)
Use `continuous_pi fun τ => ?_` and prove the remaining obligations. Use `show Continuous fun x : X.B.I.Ginf => C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ`. Use `(continuous_const.matrix_mul ?_).matrix_mul continuous_const` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply _)`.
-/
theorem measCont_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Continuous (trX X C) := by
  refine continuous_pi fun τ => ?_
  show Continuous fun x : X.B.I.Ginf => C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ
  refine (continuous_const.matrix_mul ?_).matrix_mul continuous_const
  exact (Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply _)

/- English proof (translation)
Introduce `x y h`. Use function extensionality and compare the values at `v`. Take `⟨τ, rfl⟩ : ∃ τ, vOf X τ = v` from `⟨X.pl v, by simp [vOf]⟩`. Establish `h2 : C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ = C.Qi τ * Formalism.MainNotions.S.uMat (y (vOf X τ)) * C.Q τ` using `congrFun h τ`. Take `⟨-, h1, -⟩` from `C.isT τ`.

Establish `h3` using `congrArg (fun M => C.Q τ * M * C.Qi τ) h2`. Simplify using `only [Matrix.mul_assoc, h1, Matrix.mul_one] at h3`. Simplify using `only [← Matrix.mul_assoc, h1, Matrix.one_mul] at h3`. Conclude with `Subtype.ext (Units.ext h3)`.
-/
theorem measInj_trX (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) : Function.Injective (trX X C) := by
  intro x y h
  funext v
  obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, by simp [vOf]⟩
  have h2 : C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ =
      C.Qi τ * Formalism.MainNotions.S.uMat (y (vOf X τ)) * C.Q τ := congrFun h τ
  obtain ⟨-, h1, -⟩ := C.isT τ
  have h3 := congrArg (fun M => C.Q τ * M * C.Qi τ) h2
  simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at h3
  simp only [← Matrix.mul_assoc, h1, Matrix.one_mul] at h3
  exact Subtype.ext (Units.ext h3)

/- English proof (translation)
The claim follows from `(GlobalTheory.RealPlaces.existsUnique_place D _).unique (GlobalTheory.RealPlaces.existsUnique_place D _).exists.choose_spec rfl`.
-/
theorem measTauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique
    (GlobalTheory.RealPlaces.existsUnique_place D _).exists.choose_spec rfl

/- English proof (translation)
Introduce `M N h`. Distinguish the cases in `hw : Direct D w`. Simplify `h` using `[cjw, hw]`. Simplify using `only [cjw, hw, if_false] at h`. Use function extensionality and compare the values at `i j`.

Simplify using `using congrArg star (congrFun (congrFun h i) j)`.
-/
theorem measInj_cjw (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N h
  by_cases hw : Direct D w
  · simpa [cjw, hw] using h
  · simp only [cjw, hw, if_false] at h
    funext i j
    simpa using congrArg star (congrFun (congrFun h i) j)

/- English proof (translation)
Use `continuous_pi fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : Direct D w`. Simplify using `only [Gm, cjw, hw, if_true]`. Conclude with `continuous_apply _`. Simplify using `only [Gm, cjw, hw, if_false]`.

Conclude with `continuous_pi fun i => continuous_pi fun j => continuous_star.comp ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply _)))`.
-/
theorem measCont_Gm (D : D7) : Continuous (Gm D) := by
  refine continuous_pi fun w => ?_
  by_cases hw : Direct D w
  · simp only [Gm, cjw, hw, if_true]
    exact continuous_apply _
  · simp only [Gm, cjw, hw, if_false]
    exact continuous_pi fun i => continuous_pi fun j =>
      continuous_star.comp ((continuous_apply j).comp ((continuous_apply i).comp (continuous_apply _)))

/- English proof (translation)
Introduce `y z h`. Use function extensionality and compare the values at `τ`. Use `congrFun h (InfinitePlace.mk (embS D τ))` as an intermediate fact. Simplify using `only [Gm, measTauOf_mk] at this`. Conclude with `measInj_cjw D _ this`.
-/
theorem measInj_Gm (D : D7) : Function.Injective (Gm D) := by
  intro y z h
  funext τ
  have := congrFun h (InfinitePlace.mk (embS D τ))
  simp only [Gm, measTauOf_mk] at this
  exact measInj_cjw D _ this

/- English proof (translation)
Introduce `D X θ C S hS`. Use `haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => measPolish_UJ _ _`. Rewrite using `[Set.image_image]`. Conclude with `hS.image_of_continuousOn_injOn ((measCont_Gm D).comp (measCont_trX X C)).continuousOn ((measInj_Gm D).comp (measInj_trX X C)).injOn`.
-/
theorem measurableSet_Gm_trX_image : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (S : Set X.B.I.Ginf),
    MeasurableSet S → MeasurableSet (Gm D '' (trX X C '' S)) := by
  intro D X θ C S hS
  haveI : ∀ v, PolishSpace (Formalism.REAL.UJ (X.B.I.ε v)) := fun v => measPolish_UJ _ _
  rw [Set.image_image]
  exact hS.image_of_continuousOn_injOn ((measCont_Gm D).comp (measCont_trX X C)).continuousOn
    ((measInj_Gm D).comp (measInj_trX X C)).injOn

end GlobalTheory.CovDom
