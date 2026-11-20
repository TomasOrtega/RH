import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanishAll
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSplit
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PChartSecMul
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubringOfInvMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (cechHc quotPart mIdealOver)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem twistVanishAll_closed : Kleiman.TwistVanishAll.Statement.{0, 0} :=
  Kleiman.TwistVanishAll.proof Kleiman.Extension.full Kleiman.SerreVanish.full Kleiman.TwistSplit.proof

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem lineBundle_twist_vanish {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (Q : Kleiman.LineBundle F x) :
    ∃ c₀ : ℤ, ∀ (i : ℕ) (c : ℤ), 1 ≤ i → c₀ ≤ c →
      Subsingleton ((Q.twist (Kleiman.twistSys F x c)).H i) := by
  obtain ⟨c₀, hc₀⟩ := twistVanishAll_closed F Ω N x Q (Kleiman.twistBundle F x 1) N x
    Kleiman.mem_secs_twistBundle_one Kleiman.span_range_eq_twistMod_one
  refine ⟨c₀, fun i c hi hc => ?_⟩
  have h := hc₀ i 0 c hi hc
  have e : Q.twist ((Kleiman.twistBundle F x 1).pow 0) = Q.toSubSystem :=
    Kleiman.SubSystem.twist_twistSys_zero _
  rwa [e] at h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem RayVanish.proof (hMC : ModelCechTwist.Statement) : RayVanish.Statement := by
  intro F _ K _ _ ι _ _ Ω _ _ y k₀ hM β
  have : Nonempty (ι k₀) := let ⟨i, _⟩ := hM.1 k₀; ⟨i⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card (ι k₀) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : ι k₀ ≃ Fin (N + 1) := (Fintype.equivFin _).trans (finCongr hN)
  obtain ⟨Q, hQ⟩ := BundleOfDeg.full F K ι Ω y k₀ N e hM β
  obtain ⟨c₀, hc₀⟩ := lineBundle_twist_vanish Q
  rw [Filter.eventually_atTop]
  refine ⟨c₀.toNat, fun c hc i hi => ?_⟩
  obtain ⟨φ⟩ := hMC F K ι Ω y k₀ N e hM β Q hQ 1 1 0 c i
  have hdeg : (1 : ℕ) • IndefiniteRowSideFullHecke.Kleiman2.stepL k₀ β 1 0 + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ =
      β + (c : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀ := by
    simp [IndefiniteRowSideFullHecke.Kleiman2.stepL]
  have hsys : (Kleiman.twistMul Q.toSubSystem 1 0).pow 1 = Q.toSubSystem := by
    change (Kleiman.twistSys _ _ 0).twist (Kleiman.twistMul Q.toSubSystem 1 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.twistMul]
    change ((Kleiman.twistSys _ _ 0).twist Q.toSubSystem).twist (Kleiman.twistSys _ _ 0) = _
    rw [Kleiman.twistSys_zero_twist, Kleiman.SubSystem.twist_twistSys_zero]
  rw [hdeg, hsys] at φ
  have := hc₀ i c hi (by omega)
  exact φ.symm.toEquiv.subsingleton

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RayVanish.proof_of_ties (hLoc : CellLocEval.Statement) (hRef : ModelCechRefine.Statement) :
    RayVanish.Statement :=
  RayVanish.proof (ModelCechTwist.proof (ChartSecMul.proof BundleOfDeg.full) BaseRealises.proof hLoc hRef)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
