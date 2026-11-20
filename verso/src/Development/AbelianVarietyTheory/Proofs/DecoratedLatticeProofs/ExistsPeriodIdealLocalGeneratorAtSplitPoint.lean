import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField

noncomputable section

namespace GlobalTheory.FinPl.LocGen

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem half_diff_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h, Ideal.bot_mul] at h1
  exact differentIdeal_ne_bot h1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem AA_ne_zero (D : D7) : D.host.AA ≠ 0 := by
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (half_diff_ne_bot D)
  have hc0 : ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    rw [Host.ccE, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
    exact D.host.ccK_ne_bot
  exact mul_ne_zero hc0 (inv_ne_zero hb0)

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem pr_incA_int (q : SplitPt D k) (x : 𝓞 D.host.E) : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (q.pr (incA D (x : D.host.E))) := (x.2).map ((q.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (q.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Proceed by induction. Treat this case separately.

Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_gen : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k), ∃ a₀ ∈ (D.host.AA : Set D.host.E), q.pr (incA D a₀) ≠ 0 ∧
      ∀ a ∈ (D.host.AA : Set D.host.E), q.pr (incA D a) / q.pr (incA D a₀) ∈ 𝒪[k] := by
  intro D k _ _ _ _ q
  classical
  set π : D.host.E →+* k := q.pr.comp (incA D) with hπ
  have hinj : Function.Injective π := π.injective
  have hfg : ((D.host.AA : Submodule (𝓞 D.host.E) D.host.E)).FG :=
    FractionalIdeal.fg_unit (Units.mk0 D.host.AA (AA_ne_zero D))
  obtain ⟨s, hs⟩ := hfg
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs]; simp
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun x => valuation k (π x)) hsne
  have hjmem : j ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := hs ▸ Submodule.subset_span hj
  have hj0 : π j ≠ 0 := by
    intro h0
    apply AA_ne_zero D
    rw [← FractionalIdeal.coeToSubmodule_eq_bot, ← hs, Submodule.span_eq_bot]
    intro i hi
    have h1 := hmax i hi
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at h1
    exact hinj (h1.trans π.map_zero.symm)
  refine ⟨j, hjmem, hj0, ?_⟩
  intro a ha
  have ha' : a ∈ Submodule.span (𝓞 D.host.E) (s : Set D.host.E) := hs.symm ▸ ha
  change π a / π j ∈ 𝒪[k]
  clear ha
  induction ha' using Submodule.span_induction with
  | mem x hx =>
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ (hmax x hx) zero_le'
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, add_div]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [Algebra.smul_def, map_mul, mul_div_assoc]
    exact mul_mem (pr_incA_int q r) hx

end GlobalTheory.FinPl.LocGen
