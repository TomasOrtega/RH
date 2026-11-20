import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.PoincareLaw

variable {D : D7}

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ratW_inj (A T : HSp D) : Function.Injective (ratW T A) :=
  fun _ _ h => Matrix.map_injective GlobalTheory.MixModel.incA_injective h

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem ratW_sub (A T : HSp D) (γ γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) :
    ratW T A (γ - γ₀) = ratW T A γ - ratW T A γ₀ := by
  ext i j
  simp [ratW, map_sub]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Supply the required witnesses or components.
-/
theorem finite_ratW_mem (A T : HSp D) (K : Set (WO A T)) (hK : IsCompact K) :
    {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ K}.Finite := by
  obtain ⟨hg, hlc, hsc, ht2, hdisc, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  have hcl : IsClosed (ratL T A : Set (WA T A)) := AddSubgroup.isClosed_of_discrete
  have hS : IsCompact ((Subtype.val : ratL T A → WA T A) ⁻¹' K) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hfin := (hS.finite_of_discrete.image Subtype.val).preimage (ratW_inj A T).injOn
  refine hfin.subset fun γ hγ => ?_
  exact ⟨⟨ratW T A γ, γ, rfl⟩, hγ, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem symplOH_neg_left (A T : HSp D) (y z : WO A T) : symplOH A T (-y) z = -symplOH A T y z := by
  have hadd := (GlobalTheory.OrientedFormLaws.symplOH_laws D A T).1
  have h0 : symplOH A T 0 z = 0 := by
    have := hadd 0 0 z
    rw [add_zero] at this
    exact left_eq_add.1 this
  have := hadd y (-y) z
  rw [add_neg_cancel, h0] at this
  exact (eq_neg_of_add_eq_zero_right this.symm)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem poincare_law : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A T : HSp D) (h : WO A T → ℂ), Continuous h → HasCompactSupport h → (∀ u, {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | h (ratW T A γ + u) ≠ 0}.Finite) ∧ Continuous (fun u => ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u)) ∧ ∀ (γ₀ : Matrix (Fin T.rank) (Fin A.rank) D.host.E) (u : WO A T), (∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) (ratW T A γ₀ + u)) * h (ratW T A γ + (ratW T A γ₀ + u))) = ψ (-(symplOH A T (ratW T A γ₀) u)) * ∑' γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) := by
  intro D ψ hψ A T h hc hs
  obtain ⟨hg, hlc, -, -, -, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T A
  haveI : IsTopologicalAddGroup (WO A T) := hg
  haveI : LocallyCompactSpace (WO A T) := hlc
  haveI : ContinuousSub (WO A T) := @IsTopologicalAddGroup.to_continuousSub _ _ _ hg
  have laws := GlobalTheory.OrientedFormLaws.symplOH_laws D A T

  have vanish : ∀ (U : Set (WO A T)) (u : WO A T), u ∈ U → ∀ γ,
      γ ∉ {γ : Matrix (Fin T.rank) (Fin A.rank) D.host.E | ratW T A γ ∈ (fun p : WO A T × WO A T => p.1 - p.2) '' (tsupport h ×ˢ U)} →
      h (ratW T A γ + u) = 0 := by
    intro U u hu γ hγ
    by_contra hne
    exact hγ ⟨(ratW T A γ + u, u), ⟨subset_tsupport h hne, hu⟩, add_sub_cancel_right _ _⟩
  refine ⟨fun u => ?_, ?_, fun γ₀ u => ?_⟩
  · refine (finite_ratW_mem A T _ ((hs.isCompact.prod (isCompact_singleton (x := u))).image continuous_sub)).subset fun γ hγ => ?_
    by_contra hn
    exact hγ (vanish {u} u rfl γ hn)
  · refine continuous_iff_continuousAt.2 fun u₀ => ?_
    obtain ⟨U, hU, hUn⟩ := exists_compact_mem_nhds u₀
    have hF := finite_ratW_mem A T _ ((hs.isCompact.prod hU).image continuous_sub)
    have hcont : Continuous fun u => ∑ γ ∈ hF.toFinset, ψ (symplOH A T (ratW T A γ) u) * h (ratW T A γ + u) :=
      continuous_finset_sum _ fun γ _ =>
        (hψ.1.1.comp (laws.2.2.2.2.1.comp (continuous_const.prodMk continuous_id))).mul
          (hc.comp (continuous_add_left (ratW T A γ)))
    refine hcont.continuousAt.congr (Filter.eventually_of_mem hUn fun u hu => ?_)
    refine (tsum_eq_sum fun γ hγ => ?_).symm
    rw [vanish U u hu γ (fun h' => hγ (hF.mem_toFinset.2 h')), mul_zero]
  · rw [← (Equiv.subRight γ₀).tsum_eq, ← tsum_mul_left]
    congr 1
    funext γ
    simp only [Equiv.subRight_apply]
    rw [ratW_sub]
    have e1 : ratW T A γ - ratW T A γ₀ + (ratW T A γ₀ + u) = ratW T A γ + u := by abel
    have e2 : symplOH A T (ratW T A γ - ratW T A γ₀) (ratW T A γ₀ + u) =
        symplOH A T (ratW T A γ) (ratW T A γ₀) + symplOH A T (ratW T A γ) u +
          -(symplOH A T (ratW T A γ₀) u) := by
      rw [sub_eq_add_neg, laws.1, laws.2.1, laws.2.1, symplOH_neg_left, symplOH_neg_left, laws.2.2.1]
      ring
    obtain ⟨c, hc'⟩ := laws.2.2.2.2.2.1 (ratW T A γ) ⟨γ, rfl⟩ (ratW T A γ₀) ⟨γ₀, rfl⟩
    rw [e1, e2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, hc', hψ.1.2.2.1 c]
    ring

end GlobalTheory.PoincareLaw
