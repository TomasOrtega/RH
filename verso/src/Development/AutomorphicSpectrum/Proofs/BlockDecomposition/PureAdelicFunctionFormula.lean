import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules.
-/
theorem rv_zero_apply (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    rv v 0 s = if s ≠ 0 ∧ s ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold rv
  rw [tsum_eq_single 0]
  · have h : (s ∈ v.adicCompletionIntegers F) ↔ Valued.v s ≤ 1 :=
      HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v
    simp [h]
  · intro i hi
    simp [hi]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem rv_zero_of_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v} (h0 : s ≠ 0)
    (hs : s ∈ v.adicCompletionIntegers F) : rv v 0 s = 1 := by
  rw [rv_zero_apply, if_pos ⟨h0, hs⟩]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem rv_zero_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v}
    (hs : s ∉ v.adicCompletionIntegers F) : rv v 0 s = 0 := by
  rw [rv_zero_apply, if_neg fun h => hs h.2]

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem pure_rv_zero_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (a : AF F).2 v ≠ 0 := fun v =>
    IdeleGroup.finite_ne_zero a v
  unfold PositivityTheory.Rg.Base1.pure
  split_ifs with h
  · rw [finprod_eq_one_of_forall_eq_one (fun v : {v // v ∉ S} => rv_zero_of_mem v.1 (hne v.1) (h v.1 v.2)),
      mul_one]
  · push_neg at h
    obtain ⟨v, hvS, hv⟩ := h
    have hfin : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 0 ((a : AF F).2 v.1)).Finite := by
      have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
      refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn hco) ?_
      intro w hw
      by_contra hmem
      exact hw (rv_zero_of_mem w.1 (hne w.1) (not_not.1 hmem))
    rw [finprod_eq_zero _ (⟨v, hvS⟩ : {v // v ∉ S}) (rv_zero_of_not_mem v hv) hfin, mul_zero,
      ENNReal.ofReal_zero]

end GlobalTheory.CompanionTheory.BasePsi

end
