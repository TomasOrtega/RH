import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSupportHermitianDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryConjSplitSupportedFiniteAdelicPoiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIffStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FunObj.StdVertex

set_option maxHeartbeats 6000000 in

/- English proof (translation)
Introduce `D V Λ hsig hpos hΛ S hS`. Take `⟨fr0, hfr0⟩` from `GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace D V hsig hpos`. Take `⟨x, hxx⟩` from `GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice D V fr0 Λ hfr0 hΛ`. Establish `hx : x ∈ GfC V` using `hxx.1`. Establish `hxL` using `hxx.2`.

Take `⟨γ, h, k, hr⟩` from `GlobalTheory.T.idempotent_support_hermitian_decomposition D V fr0 S hS x hx`. Establish `hγ` using `hr.1`. Establish `hh` using `hr.2.1`. Establish `hsupp` using `hr.2.2.1`. Establish `hkL` using `hr.2.2.2.2.1`.

Establish `hxe` using `hr.2.2.2.2.2`. Take `⟨u, hur⟩` from `GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint D V S γ h hγ hh hsupp`. Establish `hu : u ∈ GfC V` using `hur.1`. Establish `hue` using `hur.2.2`. Use `⟨γ * fr0, ⟨u, hu⟩, ?_, hur.2.1, ?_⟩` and prove the remaining obligations.

Establish `e1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ * fr0).1 = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1`. Simplify using `only [Formalism.UG.cT, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]`. Rewrite using `[e1, Units.val_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 1 := by rw [hγ, hfr0]`. Introduce `v`. Establish `hγγ : γ.1.map (eToEAf D) * (γ⁻¹).1.map (eToEAf D) = 1`. Rewrite using `[← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hKK : (Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1 = 1`.

Rewrite using `[← Units.val_mul, mul_inv_cancel, Units.val_one]`. Establish `h1 : ∀ w, w ∈ Formalism.L2.Herm.hatL (F` using `D.host.F) (colLat fr0) ↔ ((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) := fun w => by`. Rewrite using `[hkL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]`. Establish `key : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v)) = (Formalism.IndefR.Lev.finE V u).1 *ᵥ v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxe, hue]`.

Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hKK, Matrix.mul_one]`. Establish `s1` using `GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff D γ fr0 v`.

Establish `s2` using `h1 ((γ⁻¹).1.map (eToEAf D) *ᵥ v)`. Establish `s3` using `hxL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v))`. Rewrite `s3` using `[key]`. Conclude with `s1.trans (s2.trans s3)`.
-/
theorem exists_std_vertex : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), V.SigOK →
    (∀ τ, V.sig τ = (V.rank, 0)) → IsSelfDualC V Λ → ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) →
    ∃ (fr : GL (Fin V.rank) D.host.E) (u : GfC V),
      Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 ∧
      (∃ (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P ∧ SuppAt e V u.1 ∧ ∀ w ∈ P, Off S w) ∧
      ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
        (Formalism.IndefR.Lev.finE V u.1).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V Λ hsig hpos hΛ S hS
  obtain ⟨fr0, hfr0⟩ := GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace D V hsig hpos
  obtain ⟨x, hxx⟩ := GlobalTheory.T.exists_finiteAdelicUnitary_moves_selfDualLattice D V fr0 Λ hfr0 hΛ
  have hx : x ∈ GfC V := hxx.1
  have hxL := hxx.2
  obtain ⟨γ, h, k, hr⟩ := GlobalTheory.T.idempotent_support_hermitian_decomposition D V fr0 S hS x hx
  have hγ := hr.1
  have hh := hr.2.1
  have hsupp := hr.2.2.1
  have hkL := hr.2.2.2.2.1
  have hxe := hr.2.2.2.2.2
  obtain ⟨u, hur⟩ := GlobalTheory.T.rationalUnitary_conj_splitSupported_finiteAdelicPoint D V S γ h hγ hh hsupp
  have hu : u ∈ GfC V := hur.1
  have hue := hur.2.2
  refine ⟨γ * fr0, ⟨u, hu⟩, ?_, hur.2.1, ?_⟩
  · have e1 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (γ * fr0).1 =
        Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 := by
      simp only [Formalism.UG.cT, Units.val_mul, Matrix.map_mul, Matrix.transpose_mul]
    rw [e1, Units.val_mul]
    calc _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr0.1 *
          (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γ.1 * V.gram * γ.1) * fr0.1 := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hγ, hfr0]
  · intro v
    have hγγ : γ.1.map (eToEAf D) * (γ⁻¹).1.map (eToEAf D) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have hKK : (Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1 = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h1 : ∀ w, w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) ↔
        ((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr0) := fun w => by
      rw [hkL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ w), Matrix.mulVec_mulVec, hKK, Matrix.one_mulVec]
    have key : (Formalism.IndefR.Lev.finE V x).1 *ᵥ (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v)) =
        (Formalism.IndefR.Lev.finE V u).1 *ᵥ v := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hxe, hue]
      congr 1
      calc _ = γ.1.map (eToEAf D) * (Formalism.IndefR.Lev.finE V h).1 *
            ((Formalism.IndefR.Lev.finE V k).1 * ((Formalism.IndefR.Lev.finE V k)⁻¹).1) * (γ⁻¹).1.map (eToEAf D) := by
              simp only [Matrix.mul_assoc]
        _ = _ := by rw [hKK, Matrix.mul_one]
    have s1 := GlobalTheory.T.mem_completedLattice_columnLattice_mul_iff D γ fr0 v
    have s2 := h1 ((γ⁻¹).1.map (eToEAf D) *ᵥ v)
    have s3 := hxL (((Formalism.IndefR.Lev.finE V k)⁻¹).1 *ᵥ ((γ⁻¹).1.map (eToEAf D) *ᵥ v))
    rw [key] at s3
    exact s1.trans (s2.trans s3)

end GlobalTheory.FunObj.StdVertex
