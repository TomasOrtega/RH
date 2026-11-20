import Mathlib
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalCharacterQuantumDet

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace GlobalTheory.CompanionTheory.RgCz

/- English proof (translation)
Substitute using the available equality. Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem exists_fin_map_eq {a : ℕ} (m : Multiset ℂ) (hm : Multiset.card m = a) :
    ∃ χ : Fin a → ℂ, Multiset.map χ Finset.univ.val = m := by
  subst hm
  induction m using Quotient.inductionOn with
  | h l =>
    refine ⟨fun i => l.get (Fin.cast (by simp) i), ?_⟩
    rw [Fin.univ_val_map]
    refine congrArg _ ?_
    apply List.ext_get
    · simp
    · intro n h1 h2
      simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem charInt_at {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (hr : (CG.mk π).IsRegAlg) (τ : E →+* ℂ) :
    ∃ l : Fin a → ℤ, Function.Injective l ∧
      PositivityTheory.Rg.Cz.HasChar (cx τ (lieOp π)) fun k => (l k : ℂ) := by
  obtain ⟨hnd, hint⟩ := hr τ
  obtain ⟨χ, hχ⟩ := exists_fin_map_eq ((CG.mk π).infChar τ) (CG.card_infChar (CG.mk π) τ)
  have hinf : π.HasInfChar τ (Multiset.map χ Finset.univ.val) := by
    rw [hχ]
    exact GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) τ
  have hcap := (GlobalTheory.capelli_cuspSub E a π τ χ hinf).2
  rw [← hχ] at hnd hint
  have hχinj : Function.Injective χ := by
    have h := Multiset.inj_on_of_nodup_map hnd
    intro s t hst
    exact h s (by simp) t (by simp) hst
  have hn : ∀ s, ∃ n : ℤ, χ s = (n : ℂ) + ((a : ℂ) - 1) / 2 := fun s =>
    hint _ (Multiset.mem_map_of_mem χ (by simp))
  choose l hl using hn
  refine ⟨l, fun s t hst => hχinj (by rw [hl, hl, hst]), fun u => ?_⟩
  have h := hcap (u - ((a : ℂ) - 1) / 2)
  rw [sub_add_cancel] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hl k]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem charInt : PositivityTheory.Rg.Cz.CharInt := by
  intro E _ _ _ a π hr
  choose l hl using charInt_at π hr
  exact ⟨l, fun τ => (hl τ).1, fun τ => (hl τ).2⟩

end GlobalTheory.CompanionTheory.RgCz

end
