import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes.MirClosed

/- English proof (translation)
Introduce `k _ _ _ _ n`. Use `haveI : T2Space k := GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField (k := k)`. Establish `e : (Mir k n : Set (GL (Fin (n + 1)) k)) = ⋂ j : Fin (n + 1), {g : GL (Fin (n + 1)) k | (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = eLast k n j}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]`.

Rewrite using `[mem_Mir_iff k g]`. Conclude with `funext_iff`. Rewrite using `[e]`. Establish `hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)` using `Units.continuous_val`. Use `isClosed_iInter fun j => ?_` and prove the remaining obligations.

Conclude with `isClosed_eq ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval)) continuous_const`.
-/
theorem isClosed_mirabolic :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ),
      IsClosed (Mir k n : Set (GL (Fin (n + 1)) k)) := by
  intro k _ _ _ _ n
  haveI : T2Space k := GlobalTheory.LGrp.t2Space_of_nonarchimedeanLocalField (k := k)
  have e : (Mir k n : Set (GL (Fin (n + 1)) k)) =
      ⋂ j : Fin (n + 1), {g : GL (Fin (n + 1)) k |
        (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = eLast k n j} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_setOf_eq]
    rw [mem_Mir_iff k g]
    exact funext_iff
  rw [e]
  have hval : Continuous fun g : GL (Fin (n + 1)) k => (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    Units.continuous_val
  refine isClosed_iInter fun j => ?_
  exact isClosed_eq ((continuous_apply j).comp ((continuous_apply (Fin.last n)).comp hval))
    continuous_const

end GlobalTheory.CompanionTheory.BZRes.MirClosed
