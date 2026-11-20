import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.NonEllFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwConjOfIsTest

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace GlobalTheory.CompanionTheory.RatDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem thetaA_ratGL (g : GL (Fin n) E) : thetaA E n (ratGL E n g) = ratGL E n (thetaE E n g) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [thetaR_val, ← map_inv]
  exact conjAd_algebraMap _

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ratCent_le (d : GL (Fin n) E) : ratCent d ≤ adCent d := by
  rintro _ ⟨g, hg, rfl⟩
  have h : twConj (thetaE E n) g d = d := hg
  change twConj (thetaA E n) (ratGL E n g) (ratGL E n d) = ratGL E n d
  rw [twConj, thetaA_ratGL, ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ h

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem discrete_ratIn (d : GL (Fin n) E) : DiscreteTopology (ratIn d) := by
  haveI := GlobalTheory.CompanionTheory.KerTwFin.discreteTopology_range (E := E) (n := n)
  have hmem : ∀ x : ratIn d, (x.1.1 : GA E n) ∈ (ratGL E n).range := fun x => by
    obtain ⟨g, -, hg⟩ := (Subgroup.mem_subgroupOf.1 x.2)
    exact ⟨g, hg⟩
  refine DiscreteTopology.of_continuous_injective
    (f := fun x : ratIn d => (⟨x.1.1, hmem x⟩ : (ratGL E n).range)) ?_ ?_
  · exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  · intro x y h
    have h' : (x.1.1 : GA E n) = y.1.1 := congrArg (fun z : (ratGL E n).range => (z : GA E n)) h
    exact Subtype.ext (Subtype.ext h')

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem isClosed_adCent (d : GL (Fin n) E) : IsClosed (adCent d : Set (GA E n)) := by
  have hc : Continuous fun g : GA E n => twConj (thetaA E n) g (ratGL E n d) := by
    unfold twConj
    exact (continuous_inv.mul continuous_const).mul GlobalTheory.CompanionTheory.KerTwFin.continuous_thetaA
  exact isClosed_eq hc continuous_const

/- English proof (translation)
Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem measurable_sdot {m : ℕ} (e : Fin m → SignType) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => sdot e p.2 := by
  unfold sdot
  exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_snd).const_mul _

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem measurable_gam (m : ℕ) :
    Measurable fun p : ((Fin m → SignType) → ℝ) × (Fin m → ℝ) => gam p.1 p.2 := by
  classical
  unfold gam gamOn
  refine Finset.measurable_sum _ fun s _ => ?_
  refine Measurable.const_mul (Finset.measurable_prod _ fun e _ => ?_) _
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_lt ((measurable_pi_apply e).comp measurable_fst) (measurable_sdot e)

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem ratDisc : PositivityTheory.Rg.BcB.D4.RatDisc :=
  ⟨fun _ _ _ _ _ d => ⟨ratCent_le d, discrete_ratIn d, isClosed_adCent d⟩, measurable_gam⟩

end GlobalTheory.CompanionTheory.RatDisc

end
