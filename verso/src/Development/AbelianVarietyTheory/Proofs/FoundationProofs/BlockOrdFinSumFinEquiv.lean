import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InstSecondCountable
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.HolDS Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.HolDS

/- English proof (translation)
Use `⟨fun i => by simp, fun j => by simp, ?_⟩` and prove the remaining obligations. Introduce and unpack `(a | a) (b | b) hab`. Establish `: a < b` using `hab`. Conclude with `(Fin.strictMono_castAdd q) this`. Conclude with `hab.elim`.

Conclude with `hab.elim`. Establish `: a < b` using `hab`. Conclude with `(Fin.strictMono_natAdd p) this`.
-/
theorem blockOrd_finSumFinEquiv (p q : ℕ) :
    GlobalTheory.RealPar.BlockOrd (p := p) (q := q) finSumFinEquiv (fun i => (finSumFinEquiv.symm i).isLeft) := by
  refine ⟨fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) hab
  · have : a < b := hab
    exact (Fin.strictMono_castAdd q) this
  · exact hab.elim
  · exact hab.elim
  · have : a < b := hab
    exact (Fin.strictMono_natAdd p) this

end GlobalTheory.HolDS
