import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.SecDerSt
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.DenseCell
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.WeightFactorDilation

noncomputable section

open MeasureTheory Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.SD

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.AbsSt.DF

variable {n : ℕ}

def TK (n : ℕ) : Set (M2 n) := {M | Mᴴ * M = 1 ∧ InG M}

/- English proof (translation)
Establish `hsub : TK n ⊆ Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1`. Introduce `M hM i _ j _`. Establish `hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ`. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Conclude with `hM.1`.

Simplify using `using entry_norm_bound_of_unitary hU i j`. Use `(isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub` and prove the remaining obligations. Establish `hc1 : IsClosed {M : M2 n | Mᴴ * M = 1}` using `isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const`. Establish `hc2 : IsClosed {M : M2 n | Mᴴ * JJ n * M = JJ n}` using `isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id) continuous_const`. Conclude with `hc1.inter hc2`.
-/
theorem isCompact_TK : IsCompact (TK n) := by
  have hsub : TK n ⊆ Set.pi univ fun _ => Set.pi univ fun _ => Metric.closedBall (0 : ℂ) 1 := by
    intro M hM i _ j _
    have hU : M ∈ Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
      rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
      exact hM.1
    simpa using entry_norm_bound_of_unitary hU i j
  refine (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
    isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset ?_ hsub
  have hc1 : IsClosed {M : M2 n | Mᴴ * M = 1} :=
    isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) continuous_const
  have hc2 : IsClosed {M : M2 n | Mᴴ * JJ n * M = JJ n} :=
    isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
      continuous_id) continuous_const
  exact hc1.inter hc2

def toGR (M : TK n) : GR n :=
  ⟨⟨M.1, M.1ᴴ, mul_eq_one_comm.mp M.2.1, M.2.1⟩, M.2.2⟩

/- English proof (translation)
Use `Continuous.subtype_mk ?_ _` and prove the remaining obligations. Rewrite using `[Units.continuous_iff]`. Conclude with `⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩`.
-/
theorem continuous_toGR : Continuous (toGR (n := n)) := by
  refine Continuous.subtype_mk ?_ _
  rw [Units.continuous_iff]
  exact ⟨continuous_subtype_val, continuous_subtype_val.matrix_conjTranspose⟩

/- English proof (translation)
Establish `hset : (KR n : Set (GR n)) = Set.range (toGR (n` using `n)) := by`. Use extensionality with `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk`. Use `⟨⟨mR k, hk.2, hk.1⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Introduce and unpack `⟨M, rfl⟩`. Conclude with `⟨M.2.2, M.2.1⟩`.

Use `haveI : CompactSpace (TK n) := isCompact_iff_compactSpace.mp isCompact_TK`. Rewrite using `[hset]`. Conclude with `isCompact_range continuous_toGR`.
-/
theorem isCompact_KR : IsCompact ((KR n : Set (GR n))) := by
  have hset : (KR n : Set (GR n)) = Set.range (toGR (n := n)) := by
    ext k
    constructor
    · intro hk
      refine ⟨⟨mR k, hk.2, hk.1⟩, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
    · rintro ⟨M, rfl⟩
      exact ⟨M.2.2, M.2.1⟩
  haveI : CompactSpace (TK n) := isCompact_iff_compactSpace.mp isCompact_TK
  rw [hset]
  exact isCompact_range continuous_toGR

instance compactSpace_KR : CompactSpace (KR n) := isCompact_iff_compactSpace.mp isCompact_KR

end PositivityTheory.Rg.Sw.AbsSt.SD
