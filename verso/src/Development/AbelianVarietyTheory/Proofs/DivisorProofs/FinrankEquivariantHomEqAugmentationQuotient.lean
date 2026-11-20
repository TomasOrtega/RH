import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem mSub_qAct_top {k O C : Type*} {H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : C →+* k) : mSub (qAct σ G hG) χ ⊤ = (mSub σ χ ⊤).map G.mkQ := by
  unfold mSub
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, x, -, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    refine ⟨σ (algebraMap C O c) y - χ c • y, ⟨c, y, trivial, rfl⟩, ?_⟩
    rw [map_sub, map_smul]
    rfl
  · rintro ⟨w, ⟨c, y, -, rfl⟩, rfl⟩
    refine ⟨c, G.mkQ y, trivial, ?_⟩
    rw [map_sub, map_smul, qAct_mk]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem quotFacts {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C]
    [Algebra C O] (σ : O →+* Module.End k H) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G)
    (χ : Idx → C →+* k) :
    (jSub σ χ ⊤ ≤ G → jSub (qAct σ G hG) χ ⊤ = ⊥) ∧
      ∀ i, finrank k ((H ⧸ G) ⧸ mSub (qAct σ G hG) (χ i) ⊤) = finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) := by
  refine ⟨fun hJ => ?_, fun i => ?_⟩
  · unfold jSub
    rw [Submodule.span_eq_bot]
    rintro z ⟨r, lam, c, x, -, hc, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective G x
    have hmem : (∑ l, lam l • σ (algebraMap C O (c l)) y) ∈ G :=
      hJ (Submodule.subset_span ⟨r, lam, c, y, trivial, hc, rfl⟩)
    have : (∑ l, lam l • qAct σ G hG (algebraMap C O (c l)) (Submodule.Quotient.mk y)) =
        G.mkQ (∑ l, lam l • σ (algebraMap C O (c l)) y) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul]
      rfl
    rw [this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · rw [mSub_qAct_top]
    exact LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotientSup G (mSub σ (χ i) ⊤))

end GlobalTheory.HTRho
