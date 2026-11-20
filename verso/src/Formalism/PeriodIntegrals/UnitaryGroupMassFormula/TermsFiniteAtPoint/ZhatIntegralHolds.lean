import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ZhatRed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components.
-/
theorem carrierRow_holds : CarrierRow := by
  intro D u u' F0 Λ hΛ F' hPD
  obtain ⟨hgen, ⟨hlat, hunim, _, _⟩, _⟩ := hΛ
  obtain ⟨hlift, _, hconv, hX⟩ := hPD
  have heq : lf D F'.fl = F' := by
    obtain ⟨fl, zt⟩ := F'
    obtain ⟨_, hzt⟩ := hlift
    simp only [lf] at hzt ⊢
    rw [hzt]
  refine ⟨?_, heq⟩
  rw [IsRowLat, heq]
  exact ⟨hgen, ⟨hlat, hunim, hlift, hconv⟩, hX⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem one_le_ddS_zpow (D : D7) (k : ℕ) :
    (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ ddS D ^ (-(k : ℤ)) := by
  have h1 : ddS D ≤ 1 := FractionalIdeal.coeIdeal_le_one
  have hk : ddS D ^ k ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc ddS D ^ k * ddS D ≤ 1 * 1 := mul_le_mul' ih h1
        _ = 1 := one_mul 1
  have hne : ddS D ^ k ≠ 0 := pow_ne_zero _ (PI.SRW.ddS_ne D)
  rw [zpow_neg, zpow_natCast]
  have := FractionalIdeal.inv_anti_mono hne one_ne_zero hk
  simpa using this

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem e_mem_of_XS (D : D7) {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (VS D) D.R.rS T) (hX : XLam Λ F = XS D F.fl) (a : Fin D.R.rS) : F.fl.e a ∈ Λ := by
  have hmem : F.fl.e a ∈ XS D F.fl := by
    refine Submodule.subset_span ⟨a, 1, ?_, by simp⟩
    have h := one_le_ddS_zpow D (D.R.rS - a)
    have e : (-((D.R.rS : ℤ) - (a : ℕ))) = -((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
      have : (a : ℕ) ≤ D.R.rS := a.2.le
      push_cast [this]; ring
    rw [e]
    exact h (FractionalIdeal.one_mem_one _)
  rw [← hX] at hmem
  exact hmem.1

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.
-/
theorem frame_mem (D : D7) {T : D.host.E} (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F : LFlag (VS D) D.R.rS T) (hX : XLam Λ F = XS D F.fl) (hz : F.fl.z ∈ Λ) (a : Fin (D.R.rS + 1)) :
    frame F a ∈ Λ := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simpa [frame, FlagG.fvec] using hz
  · simpa [frame, FlagG.fvec] using e_mem_of_XS D Λ F hX i

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem hT_int (D : D7) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ)
    {x y : (VS D).V} (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = (VS D).hT x y := by
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU]; exact hy
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hy' x) hx
  obtain ⟨o, ho⟩ := (Submodule.mem_one).1 this
  exact ⟨o, by simpa using ho⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem zhatIntegral_holds : ZhatIntegral := by
  intro D u u' F0 Λ hΛ F' hPD a b
  obtain ⟨_, ⟨_, hU, hlift0, _⟩, hX0⟩ := hΛ
  obtain ⟨hlift, _, _, hX⟩ := hPD
  exact hT_int D Λ hU (frame_mem D Λ (lf D F0) hX0 hlift0.1 a) (frame_mem D Λ F' hX hlift.1 b)

end PI.TermsAtPtFiniteW
