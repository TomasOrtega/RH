import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate

/- English proof (translation)
Introduce `R _ T _ A hA f hf t`. Establish `key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨a, -, b, hb, rfl⟩` from `hg`. Conclude with `A.smul_mem hb (a t)`. Consider the case `zero => exact A.zero_mem`. Consider the case `add x y _ _ hx hy => exact A.add_mem hx hy`. Consider the case `smul r x _ hx => exact A.smul_mem hx r`.

Conclude with `key _ (hA.comul f hf)`.
-/
theorem translate_mem_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)),
    IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, -, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

end GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate
