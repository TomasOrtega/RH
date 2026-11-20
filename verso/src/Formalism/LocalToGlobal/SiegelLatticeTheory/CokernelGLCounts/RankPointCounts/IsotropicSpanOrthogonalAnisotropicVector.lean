import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBetaID
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FStarBwdNA

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.Pf.ScalarFramePf

namespace Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : Formalism.BasicNotions.D7}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hsw' (x y : (VS D).V) : (VS D).hT y x = star ((VS D).hT x y) := ((VS D).herm.eq x y).symm

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fvec_cs {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (i : Fin D.R.rS) : F.fvec i.castSucc = F.e i := by
  simp [FlagG.fvec]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem fvec_last {T : D.host.E} (F : FlagG (VS D) D.R.rS T) : F.fvec (Fin.last D.R.rS) = F.z := by
  simp [FlagG.fvec]

/- English proof (translation)
Proceed by induction. Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Proceed by induction. Treat this case separately.

Treat this case separately.
-/
theorem hff {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (a b : Fin (D.R.rS + 1)) :
    (VS D).hT (F.fvec a) (F.fvec b) = if a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS then -T else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => rw [fvec_last, F.z_norm, if_pos ⟨rfl, rfl⟩]
    | cast j =>
      rw [fvec_last, fvec_cs, if_neg (fun h => Fin.castSucc_ne_last j h.2), hsw', F.z_orth, star_zero]
  | cast i =>
    rw [if_neg (fun h => Fin.castSucc_ne_last i h.1)]
    induction b using Fin.lastCases with
    | last => rw [fvec_cs, fvec_last, F.z_orth]
    | cast j => rw [fvec_cs, fvec_cs, F.e_iso]

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem iso_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x y : (VS D).V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    (VS D).hT x y = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hy
  simp [map_sum, LinearMap.sum_apply, F.e_iso]

/- English proof (translation)
Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules.
-/
theorem isotropicSpan_orthogonal_anisotropicVector {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT x F.z = 0 := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx
  simp [map_sum, LinearMap.sum_apply, F.z_orth]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem z_orth_X {T : D.host.E} (F : FlagG (VS D) D.R.rS T) {x : (VS D).V} (hx : x ∈ F.X) :
    (VS D).hT F.z x = 0 := by
  rw [hsw', isotropicSpan_orthogonal_anisotropicVector F hx, star_zero]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Proceed by induction. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem Xplus_eq {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    F.Xplus = Submodule.span D.host.E (Set.range F.fvec) := by
  apply le_antisymm
  · apply sup_le
    · rw [FlagG.X, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨i.castSucc, fvec_cs F i⟩
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨Fin.last _, fvec_last F⟩
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    induction a using Fin.lastCases with
    | last => rw [fvec_last]; exact Submodule.mem_sup_right (Submodule.subset_span rfl)
    | cast i => rw [fvec_cs]; exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

end Formalism.L2.SG.Pf.FrameGlobalPatching.FStar.SpanOmPf
