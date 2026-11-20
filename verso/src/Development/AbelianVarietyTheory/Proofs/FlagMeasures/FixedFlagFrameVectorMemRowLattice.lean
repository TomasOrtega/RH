import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
open scoped Classical ENNReal Pointwise
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.RowFrame

/- English proof (translation)
Establish `hI0 : ddS D ≠ 0`. Unfold `ddS`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]`. Rewrite using `[Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`.

Conclude with `FaithfulSMul.algebraMap_injective _ _`. Establish `hI1 : ddS D ≤ 1` using `FractionalIdeal.coeIdeal_le_one`. Establish `hJ0 : ddS D ^ n ≠ 0` using `pow_ne_zero _ hI0`. Establish `hJ1 : ddS D ^ n ≤ 1` using `pow_le_one' hI1 n`. Rewrite using `[zpow_neg, zpow_natCast]`.

Establish `h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹`. Combine the equalities or inequalities in the displayed calculation. Conclude with `h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)`.
-/
theorem one_mem_ddS_zpow (D : D7) (n : ℕ) :
    (1 : D.host.E) ∈ (ddS D ^ (-(n : ℤ)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  have hI0 : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    rw [Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hI1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hJ0 : ddS D ^ n ≠ 0 := pow_ne_zero _ hI0
  have hJ1 : ddS D ^ n ≤ 1 := pow_le_one' hI1 n
  rw [zpow_neg, zpow_natCast]
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ (ddS D ^ n)⁻¹ := by
    calc (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = ddS D ^ n * (ddS D ^ n)⁻¹ :=
          (mul_inv_cancel₀ hJ0).symm
      _ ≤ 1 * (ddS D ^ n)⁻¹ := by gcongr
      _ = (ddS D ^ n)⁻¹ := one_mul _
  exact h1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)

/- English proof (translation)
Introduce and unpack `⟨-, ⟨-, -, hlift, -⟩, hX⟩ a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Establish `e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z` using `by simp [frame, FlagG.fvec]`. Rewrite using `[e]`. Conclude with `hlift.1`.

Establish `e : frame (lf D F0) i.castSucc = F0.e i` using `by simp [frame, FlagG.fvec]`. Rewrite using `[e]`. Establish `hmem : F0.e i ∈ XS D F0`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `⟨i, 1, ?_, (one_smul _ _).symm⟩` and prove the remaining obligations.

Establish `hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ)`. Rewrite using `[Nat.cast_sub i.isLt.le]`. Rewrite using `[hk]`. Conclude with `one_mem_ddS_zpow D _`. Rewrite `hmem` using `[← hX]`.

Conclude with `hmem.1`.
-/
theorem frame_mem (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D) :
    IsRowLat D F0 Λ → ∀ a, frame (lf D F0) a ∈ Λ := by
  rintro ⟨-, ⟨-, -, hlift, -⟩, hX⟩ a
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have e : frame (lf D F0) (Fin.last D.R.rS) = (lf D F0).fl.z := by simp [frame, FlagG.fvec]
    rw [e]
    exact hlift.1
  · have e : frame (lf D F0) i.castSucc = F0.e i := by simp [frame, FlagG.fvec]
    rw [e]
    have hmem : F0.e i ∈ XS D F0 := by
      apply Submodule.subset_span
      refine ⟨i, 1, ?_, (one_smul _ _).symm⟩
      have hk : (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) = -(((D.R.rS - (i : ℕ) : ℕ)) : ℤ) := by
        rw [Nat.cast_sub i.isLt.le]
      rw [hk]
      exact one_mem_ddS_zpow D _
    rw [← hX] at hmem
    exact hmem.1

end GlobalTheory.Unfold.RowFrame
