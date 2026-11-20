import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.CharLat

/- English proof (translation)
Introduce a local definition for the expression. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Apply the first step, then apply the next step to every resulting obligation. Both sides reduce to the same expression.

Both sides reduce to the same expression. Establish an intermediate fact. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem nonempty_equiv_of_free {O K : Type} [CommRing O] [IsDomain O] [Field K] [Module O K]
    (φ : O →+* K) (hsm : ∀ (o : O) (x : K), o • x = φ o * x)
    (hfr : ∀ z : K, ∃ a d : O, d ≠ 0 ∧ z * φ d = φ a)
    (T : Submodule O K) [Module.Free O T] (hT : T ≠ ⊥) :
    Nonempty (O ≃ₗ[O] T) := by
  let b := Module.Free.chooseBasis O T
  haveI hsub : Subsingleton (Module.Free.ChooseBasisIndex O T) := by
    constructor
    intro i j
    by_contra hij
    have hi : ((b i : T) : K) ≠ 0 := fun h0 => b.ne_zero i (Subtype.ext h0)
    obtain ⟨a, d, hd0, hd⟩ := hfr (((b j : T) : K) / ((b i : T) : K))
    have hrel : d • b j + (-a) • b i = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm, ZeroMemClass.coe_zero,
        map_neg, ← hd]
      field_simp
      ring
    have hinj : Function.Injective ![j, i] := by
      intro x y hxy
      fin_cases x <;> fin_cases y
      · rfl
      · exact absurd (hxy : j = i).symm hij
      · exact absurd (hxy : i = j) hij
      · rfl
    have hli : LinearIndependent O ![b j, b i] := by
      have := b.linearIndependent.comp ![j, i] hinj
      convert this using 1
      ext k
      fin_cases k <;> rfl
    have h2 := LinearIndependent.pair_iff.1 hli d (-a) hrel
    exact hd0 h2.1
  haveI hne : Nonempty (Module.Free.ChooseBasisIndex O T) := by
    by_contra h
    rw [not_nonempty_iff] at h
    apply hT
    rw [eq_bot_iff]
    intro x hx
    have h0 : (⟨x, hx⟩ : T) = 0 := b.repr.injective (Subsingleton.elim _ _)
    simpa using congrArg Subtype.val h0
  haveI : Unique (Module.Free.ChooseBasisIndex O T) := uniqueOfSubsingleton (Classical.arbitrary _)
  exact ⟨(LinearEquiv.funUnique (Module.Free.ChooseBasisIndex O T) O O).symm.trans b.equivFun.symm⟩

end GlobalTheory.CharLat

namespace GlobalTheory.CharLat

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem exists_equiv_charLattice : ∀ {l : ℕ} [Fact l.Prime] (LL : FinExt l) {G : Type} [Group G] [TopologicalSpace G]
    (θ : G →* (↥(OL LL))ˣ) (Lc : Lattice (O := ↥(OL LL)) (charRep (tableLineDegreeTwo.charL (LL := ↥LL.1) θ))),
    ∃ e : ↥(OL LL) ≃ₗ[↥(OL LL)] ↥Lc.T, ∀ g a, e (Formalism.GaloisCohomology.scalRep (↥(OL LL)) θ g a) = latRep Lc g (e a) := by
  intro l _ LL G _ _ θ Lc
  haveI := LL.2
  haveI hF : IsFractionRing (↥(OL LL)) (↥LL.1) :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[l]) (K := ℚ_[l]) (L := ↥LL.1)
  haveI := Lc.free
  have hT : Lc.T ≠ ⊥ := by
    intro h
    have hs := Lc.span
    rw [h, Submodule.bot_coe, Submodule.span_zero_singleton] at hs
    exact bot_ne_top hs
  have hsm : ∀ (o : ↥(OL LL)) (x : ↥LL.1), o • x = algebraMap (↥(OL LL)) (↥LL.1) o * x :=
    fun o x => rfl
  have hfr : ∀ z : ↥LL.1, ∃ a d : ↥(OL LL), d ≠ 0 ∧ z * algebraMap (↥(OL LL)) (↥LL.1) d =
      algebraMap (↥(OL LL)) (↥LL.1) a := by
    intro z
    obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors (↥(OL LL))) z
    exact ⟨a, d, nonZeroDivisors.coe_ne_zero d, hd⟩
  obtain ⟨e⟩ := nonempty_equiv_of_free (algebraMap (↥(OL LL)) (↥LL.1)) hsm hfr Lc.T hT
  refine ⟨e, fun g a => ?_⟩
  rw [Formalism.GaloisCohomology.scalRep_apply, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_smul, hsm]
  rfl

end GlobalTheory.CharLat
