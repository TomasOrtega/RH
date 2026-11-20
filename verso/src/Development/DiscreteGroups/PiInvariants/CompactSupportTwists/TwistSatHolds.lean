import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CTZeroCut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem absC_loc (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n)) :
    (((Model.absC E u).loc w x : ℂˣ) : ℂ) = Complex.exp (u * (-(n * Real.log (Ideal.absNorm w.asIdeal : ℕ)) : ℝ)) := by
  change Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem absC_unrAt (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E u).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [absC_loc u w x 0 (by rw [hx]; simp)]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem absC_val (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((Model.absC E u).val w : ℂˣ) : ℂ) = ((qV E w : ℕ) : ℂ) ^ (-u) := by
  have hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ)) :=
    unif_spec w
  have h := absC_loc u w (atFin w (unif w)) 1 hu
  change (((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _
  rw [h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]
  have e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]; rfl
  rw [e]
  congr 1
  push_cast
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem twistSat_holds : TwistSat := by
  intro E _ _ _ m σ u
  refine ⟨σ.twist (Model.absC E (-u)), Filter.Eventually.of_forall fun w B hB => ?_⟩
  refine ⟨B.map (· * (Model.absC E (-u)).val w),
    GlobalTheory.SphGal.hasSatGL_twist E m σ _ w B (absC_unrAt (-u) w) hB, ?_⟩
  rw [Multiset.map_map]
  unfold sclQ
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul, absC_val, neg_neg]

end DiscreteGroups.T1.G

end
