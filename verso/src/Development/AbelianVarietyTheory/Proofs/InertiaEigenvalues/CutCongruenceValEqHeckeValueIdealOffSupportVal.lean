import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect

noncomputable section

namespace GlobalTheory.Pass.CutEq

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

/- English proof (translation)
Introduce `D i Xs π`. Establish `h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π`. Unfold `ccAt GlobalTheory.Cut.ccOff Ideal.map`. Use `congr 1`. Use extensionality with `a`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`. Use `⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩` and prove the remaining obligations. Use `congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩` as an intermediate fact. Conclude with `this`.

Introduce and unpack `⟨f, hf, h0, rfl⟩`. Use `⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩` and prove the remaining obligations. Establish `hy` using `y.2`. Simplify using `only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy`. Conclude with `h0 y.1 hy.2 hy.1`.

Unfold `vccCut GlobalTheory.Cut.vccOff`. Rewrite using `[h]`.
-/
theorem main : ∀ (D : D7) (i : D.nd.Loc) (Xs : Set (D.nd.X i)) (π : D.nd.X i),
    PairedCharacterCondition.CongruenceModules.vccCut i Xs π = GlobalTheory.Cut.vccOff i Xs π := by
  intro D i Xs π
  have h : ccAt (D.nd.T i) (cutLocus i Xs) π = GlobalTheory.Cut.ccOff i Xs π := by
    unfold ccAt GlobalTheory.Cut.ccOff Ideal.map
    congr 1
    ext a
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f.1, f.2, fun x hx hZ => ?_, rfl⟩
      have := congrFun (RingHom.mem_ker.1 hf) ⟨x, by simp [cutLocus, hx, hZ]⟩
      exact this
    · rintro ⟨f, hf, h0, rfl⟩
      refine ⟨⟨f, hf⟩, RingHom.mem_ker.2 (funext fun y => ?_), rfl⟩
      have hy := y.2
      simp only [cutLocus, Finset.mem_filter, Finset.mem_univ, true_and, not_or, not_not] at hy
      exact h0 y.1 hy.2 hy.1
  unfold vccCut GlobalTheory.Cut.vccOff
  rw [h]

end GlobalTheory.Pass.CutEq
