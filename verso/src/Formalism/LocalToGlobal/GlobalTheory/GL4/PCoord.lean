import Formalism.LocalToGlobal.GlobalTheory.GL4.PCoordH

noncomputable section

open NumberField

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree Cc

section CoordRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramFac_X (D : D7) (i : ℕ) (hi : i ≤ D.R.m) : GramFac (D.sp.X i) :=
  gramFac_of_definite _ (host_star D) (D.sp.X_sig i) (D.sp.X_def i hi)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gramFac_X' (D : D7) : GramFac D.sp.X' :=
  gramFac_of_isomEmb _ _ D.sp.iX' D.sp.iX'_isom (gramFac_X D D.R.m le_rfl)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem coordCount_rec (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (S : HSpace D.host.E) (q n : ℕ)
    (hn : 1 ≤ n) (hr : S.rank = n) (hF : GramFac S) :
    CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n) := by
  have h1 := one_le_radius_sq D u C₀ hC n hn
  have hl := Real.log_nonneg h1
  refine coordCount_of S q _ _ (by unfold msRho; linarith) hF ?_
  rw [hr, Formalism.MainNotions.flipTwoThree.b_finrank_host]
  have hpos : 0 < msRho D u C₀ n ^ (2 * D.R.f * n * n) := pow_pos (by unfold msRho; linarith) _
  rw [← Real.log_le_iff_le_exp hpos, Real.log_pow]
  unfold msRho coordinateLogBound
  push_cast
  have hn' : (0 : ℝ) ≤ n := by positivity
  have hf : (0 : ℝ) ≤ D.R.f := by positivity
  have hp : 0 ≤ (D.R.f : ℝ) * n * Real.log (radiusSq D u C₀ n) := mul_nonneg (mul_nonneg hf hn') hl
  nlinarith [hp]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Replace the relevant objects with their definitions. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem coordCount_record (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) :
    (∀ i ≤ D.R.m, CoordCount (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (msRho D u C₀ (D.R.N i)) (coordinateLogBound D u C₀ (D.R.N i))) ∧
    CoordCount D.sp.X' 1 (msRho D u C₀ (D.R.N D.R.m - 1)) (coordinateLogBound D u C₀ (D.R.N D.R.m - 1)) := by
  refine ⟨fun i hi ↦ coordCount_rec D u C₀ hC _ _ _ ?_ (D.sp.X_rank i hi) (gramFac_X D i hi), ?_⟩
  · have := D.R.k_ge
    unfold Ranks.N
    omega
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    refine coordCount_rec D u C₀ hC _ _ _ ?_ (by rw [D.sp.X'_rank, hN]) (gramFac_X' D)
    rw [hN]
    unfold Ranks.rankX' Ranks.r
    have := D.R.k_ge
    omega

end CoordRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
