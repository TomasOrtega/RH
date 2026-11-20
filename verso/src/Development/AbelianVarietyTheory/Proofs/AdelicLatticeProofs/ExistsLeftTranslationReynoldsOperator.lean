import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyCompletelyReducibleStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducibleStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ReynoldsLtr

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [evC, ltr]`. Consider the case `add p q hp hq`. Simplify using `only [evC, map_add] at hp hq ⊢`. Rewrite using `[hp, hq]`.

Consider the case `mul_X p i hp`. Simplify using `only [evC, map_mul] at hp ⊢`. Rewrite using `[hp]`. Simplify using `[ltr, Matrix.mul_apply]`.
-/
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h g hg`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Establish `h1` using `evC_ltr g (Matrix.of fun i j => x (i, j)) f`.

Rewrite `h1` using `[h g hg]`. Simplify `h1` using `[evC]`. Introduce `h g hg y`. Rewrite using `[← evC_ltr, h g hg]`.
-/
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have h1 := evC_ltr g (Matrix.of fun i j => x (i, j)) f
    rw [h g hg] at h1
    simpa [evC] using h1
  · intro h g hg y
    rw [← evC_ltr, h g hg]

/- English proof (translation)
Introduce `ι _ _ Γ hΓ hss`. Take `⟨Rey, h1, h2, -, -, h5, h6⟩` from `GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ) ((fun g => (ltr g).toLinearMap) '' Γ) (by`. Introduce `U hU`. Take `⟨U', hU', hc⟩` from `GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hΓ hss U (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)`. Use `⟨U', ?_, hc⟩` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, rfl⟩ f hf`. Conclude with `hU' g hg f hf)`. Use `⟨Rey, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f`. Rewrite using `[isInv_iff]`.

Introduce `g hg`. Conclude with `h1 f _ ⟨g, hg, rfl⟩`. Introduce `f hf`. Rewrite `hf` using `[isInv_iff]`. Apply `h2` to reduce the goal to its premises.

Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `hf g hg`. Introduce `a f ha`. Rewrite `ha` using `[isInv_iff]`. Use `h5 (LinearMap.mulLeft ℂ a) ?_ f` and prove the remaining obligations.

Introduce and unpack `_ ⟨g, hg, rfl⟩ v`. Simplify using `only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ha g hg]`. Introduce `U hU`. Apply `h6` to reduce the goal to its premises. Introduce and unpack `_ ⟨g, hg, rfl⟩ f hf`.

Conclude with `hU g hg f hf`.
-/
theorem exists_isReynolds : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, h1, h2, -, -, h5, h6⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hΓ hss U
        (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ f hf
      exact hU' g hg f hf)
  refine ⟨Rey, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [isInv_iff]
    intro g hg
    exact h1 f _ ⟨g, hg, rfl⟩
  · intro f hf
    rw [isInv_iff] at hf
    apply h2
    rintro _ ⟨g, hg, rfl⟩
    exact hf g hg
  · intro a f ha
    rw [isInv_iff] at ha
    refine h5 (LinearMap.mulLeft ℂ a) ?_ f
    rintro _ ⟨g, hg, rfl⟩ v
    simp only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ha g hg]
  · intro U hU
    apply h6
    rintro _ ⟨g, hg, rfl⟩ f hf
    exact hU g hg f hf

end GlobalTheory.ClassFin.ReynoldsLtr
