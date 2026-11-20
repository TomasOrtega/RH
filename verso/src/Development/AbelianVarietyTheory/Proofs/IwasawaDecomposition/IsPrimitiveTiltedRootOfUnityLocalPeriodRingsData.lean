import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

/- English proof (translation)
Introduce `l _ C`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `C.ε_root 0`. Rewrite `h` using `[C.ζ_zero, map_one]`. Conclude with `Subtype.ext h`.

Introduce `h1`. Establish `h` using `C.ε_root 1`. Establish `h2 : rootT C.ε 1 = 1` using `h1`. Rewrite `h` using `[h2]`. Apply `C.ζ_one` to reduce the goal to its premises.

Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises. Rewrite using `[map_one, ← h]`. Both sides reduce to the same expression.
-/
theorem core_isEps : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l, IsEps C.ε := by
  intro l _ C
  refine ⟨?_, ?_⟩
  · have h := C.ε_root 0
    rw [C.ζ_zero, map_one] at h
    exact Subtype.ext h
  · intro h1
    have h := C.ε_root 1
    have h2 : rootT C.ε 1 = 1 := h1
    rw [h2] at h
    apply C.ζ_one
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [map_one, ← h]
    rfl

end GlobalTheory.MemLoc
