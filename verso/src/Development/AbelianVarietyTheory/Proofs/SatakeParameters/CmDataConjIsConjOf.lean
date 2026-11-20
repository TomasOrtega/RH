import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalToGlobal.Divisibility.TuplesLemmas
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc`. Use `⟨fun h0 => ?_, fun e => star_star e, fun e he => (hc.fixed e).1 he⟩` and prove the remaining obligations. Establish `hs : Function.Surjective (algebraMap F E)` using `fun e => (hc.fixed e).1 (AlgHom.congr_fun h0 e)`. Establish `h1 : Module.finrank F E = 1` using `(LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap F E) ⟨(algebraMap F E).injective, hs⟩)).symm.trans (Module.finrank_self F)`. Use `hc.deg2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem cmData_sig_isConjOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] (hc : CMData F E), IsConjOf hc.sig := by
  intro F E _ _ _ _ _ _ hc
  refine ⟨fun h0 => ?_, fun e => star_star e, fun e he => (hc.fixed e).1 he⟩
  have hs : Function.Surjective (algebraMap F E) := fun e => (hc.fixed e).1 (AlgHom.congr_fun h0 e)
  have h1 : Module.finrank F E = 1 :=
    (LinearEquiv.finrank_eq (LinearEquiv.ofBijective (Algebra.linearMap F E)
      ⟨(algebraMap F E).injective, hs⟩)).symm.trans (Module.finrank_self F)
  have := hc.deg2
  omega

end GlobalTheory
