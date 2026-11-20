import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem ptOf_std_entries_intAtA : ∀ {B : Base} (n : ℕ) (g : GA B n) (p : DecoF B.fields.E n ∅ ∅ ∅), PtOf g p → p.deco.1.N = stdLat B.fields.E n → ∀ (P : HeightOneSpectrum (𝓞 B.host.E)) (r s : Fin n), IntAtA (F := B.host.F) P ((g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) ∧ IntAtA (F := B.host.F) P (((g⁻¹ : GA B n) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) r s) := by
  intro B n g p hp hN P r s
  have hlat := hp.lat
  rw [hN] at hlat
  have hint : ∀ x : Fin n → AfE B.host.F B.host.E, x ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) ↔ ∀ i, x i ∈ Formalism.L2.Herm.intAf B.host.F B.host.E := by
    intro x
    exact mem_latS_std x
  have hone : ∀ a : AfE B.host.F B.host.E, a ∈ Formalism.L2.Herm.intAf B.host.F B.host.E → IntAtA (F := B.host.F) P a := by
    intro a ha
    refine ⟨1, ?_, ?_⟩
    · exact P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top
    · simpa using ha
  have he : ∀ j : Fin n, (Pi.single j 1 : Fin n → AfE B.host.F B.host.E) ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
    intro j
    rw [hint]
    intro i
    by_cases h : i = j
    · subst h; simp [one_mem]
    · simp [Pi.single_apply, h, zero_mem]
  constructor
  · apply hone
    have hx : (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) *ᵥ Pi.single s 1 ∈ Formalism.L2.Herm.hatL (Formalism.L2.Col.stdLat B.host.E n) := by
      rw [hlat]
      rw [Matrix.mulVec_mulVec]
      have h1 : ((g⁻¹ : GL (Fin n) (AfE B.host.F B.host.E)) : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) * (g : Matrix (Fin n) (Fin n) (AfE B.host.F B.host.E)) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [h1, Matrix.one_mulVec]
      exact he s
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this
  · apply hone
    have hx := (hlat (Pi.single s 1)).1 (he s)
    have := (hint _).1 hx r
    simpa [Matrix.mulVec_single] using this

end GlobalTheory
