import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.PieceGood
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PsiMulVec

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

/- English proof (translation)
Set `_ : Field (Fe hA he)` to `(Fe_isField hA he hne hf).toField`. Establish `hFd : Module.finrank k (Fe hA he) = Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))`. Rewrite using `[← map_Th_Fe hA he, ← (Submodule.equivMapOfInjective (Th e) Th_inj _).finrank_eq, Subalgebra.finrank_toSubmodule]`. Establish `hD : Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) = Module.finrank k (Module.End (Fe hA he) (Wd e))`. Unfold `cenSub`.

Rewrite using `[← range_Psi hA he hid, LinearMap.finrank_range_of_inj (Psi_inj hA he)]`. Establish `h1` using `GroundTheory.Brauer.finrank_mul_finrank_end k (Fe hA he) (Wd e)`. Establish `h2` using `Module.finrank_mul_finrank k (Fe hA he) (Wd e)`. Establish `hr : e.rank = Module.finrank k (Wd e)` using `rfl`. Establish `hd0 : 0 < Module.finrank k (Fe hA he)` using `Module.finrank_pos`.

Rewrite using `[← hFd, hD, hr]`. Use `set d := Module.finrank k (Fe hA he)`. Use `set m := Module.finrank (Fe hA he) (Wd e)`. Rewrite `h1`, the goal using `[← h2]`. Use `⟨hd0, dvd_mul_right _ _, ?_⟩` and prove the remaining obligations.

Rewrite using `[Nat.mul_div_cancel_left m hd0]`. Apply `Nat.eq_of_mul_eq_mul_left hd0` to reduce the goal to its premises. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pi_ratio {A : Subalgebra k (Matrix (Fin N) (Fin N) k)} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {e : Matrix (Fin N) (Fin N) k} (he : e ∈ A) (hid : IsIdempotentElem e) (hne : e ≠ 0)
    (hf : ∀ a ∈ A, e * a = 0 ∨ ∃ b ∈ A, e * a * b = e) :
    0 < Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∧
      Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) ∣ e.rank ∧
      Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
        (e.rank / Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))) ^ 2 *
          Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
  classical
  let _ : Field (Fe hA he) := (Fe_isField hA he hne hf).toField
  have hFd : Module.finrank k (Fe hA he) = Module.finrank k (A.toSubmodule.map (LinearMap.mulLeft k e)) := by
    rw [← map_Th_Fe hA he, ← (Submodule.equivMapOfInjective (Th e) Th_inj _).finrank_eq,
      Subalgebra.finrank_toSubmodule]
  have hD : Module.finrank k ((cenSub A).map (LinearMap.mulLeft k e)) =
      Module.finrank k (Module.End (Fe hA he) (Wd e)) := by
    unfold cenSub
    rw [← range_Psi hA he hid, LinearMap.finrank_range_of_inj (Psi_inj hA he)]
  have h1 := GroundTheory.Brauer.finrank_mul_finrank_end k (Fe hA he) (Wd e)
  have h2 := Module.finrank_mul_finrank k (Fe hA he) (Wd e)
  have hr : e.rank = Module.finrank k (Wd e) := rfl
  have hd0 : 0 < Module.finrank k (Fe hA he) := Module.finrank_pos
  rw [← hFd, hD, hr]
  set d := Module.finrank k (Fe hA he)
  set m := Module.finrank (Fe hA he) (Wd e)
  rw [← h2] at h1 ⊢
  refine ⟨hd0, dvd_mul_right _ _, ?_⟩
  rw [Nat.mul_div_cancel_left m hd0]
  apply Nat.eq_of_mul_eq_mul_left hd0
  rw [h1]; ring

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
