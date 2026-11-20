import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealPlaceBlockWeightLastEntryConsecutiveLevelsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealisingPolynomialBlockwiseHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ModelPartitionSizeExtensionFirstLastRowsStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.DelA

/- English proof (translation)
Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.

Simplify using the standard rewrite rules. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem blk_iff_posJ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (j : ℕ)
    (x : Var (X.Pj j)) (b : Σ v : X.Pl, Fin (X.G.P.n' v)) :
    ((⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)) ↔ blkJ X j x = b := by
  cases j
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl
  · simp only [blkJ, idxJ]
    change _ = pos.symm (pos b) ↔ _
    rw [Equiv.symm_apply_apply]
    exact Iff.rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem oddDeg_of_realises : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (j : ℕ) (hN : RankTie X D j) (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ (Q : MvPolynomial (GL3Theta.FrV D (D.R.N j)) ℂ), Q ∈ WtPol ℂ ν → ∀ (Gc : XR (X.Pj j) ℂ) (G : (X.Pj j).Xsp), Realises X D pos j (rkS X D hN) (wT X D pos j) Q Gc → MvPolynomial.map (algebraMap X.G.Kf Kc) G = MvPolynomial.map ι Gc → OddDeg X j G := by
  intro p _ X D pos Kc _ _ ι j hN ν hν Q hQ Gc G hR hmap m hm b hb
  have hs : G.support = Gc.support := by
    rw [← MvPolynomial.support_map_of_injective G (algebraMap X.G.Kf Kc).injective, hmap,
      MvPolynomial.support_map_of_injective Gc ι.injective]
  rw [hs] at hm
  have hh := GlobalTheory.T.realising_polynomial_blockwise_homogeneous X D pos j (rkS X D hN) (wT X D pos j) ν Q Gc hQ hR m hm (pos b)
  obtain ⟨he, -⟩ := GlobalTheory.T.realPlaceBlockWeightLastEntry_consecutive_levels X D pos j (pos b)
  obtain ⟨-, hsz, -, -, -⟩ := GlobalTheory.T.modelPartition_size_extension_firstLast_rows X D pos j hN ν hν
  have hodd : IsOddPos (pos.symm (pos b)).2 := by rw [Equiv.symm_apply_apply]; exact hb
  rw [if_pos hodd] at he hh
  rw [he, ← hsz] at hh
  have hl : ((∑ x ∈ Finset.univ.filter (fun x => blkJ X j x = b), m x : ℕ) : ℤ) =
      ∑ x : Var (X.Pj j), if (⟨x.1, x.2.1⟩ : Σ v : Fin (X.Pj j).nV, Fin ((X.Pj j).n' v)) = (GlobalTheory.TwV.DelA.posJ X D pos j).symm (pos b)
        then (m x : ℤ) else 0 := by
    rw [Nat.cast_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [blk_iff_posJ]
  have h1 : szT X D pos j (pos b) = szMu X j b.1 b.2 := by unfold szT; rw [Equiv.symm_apply_apply]
  have h2 : cT1 X D pos j (pos b) = cMu X j b.1 b.2 := by unfold cT1; rw [Equiv.symm_apply_apply]
  rw [hl, hh, h1, h2, hN.1]
  ring

end GlobalTheory.TwV.DelA
