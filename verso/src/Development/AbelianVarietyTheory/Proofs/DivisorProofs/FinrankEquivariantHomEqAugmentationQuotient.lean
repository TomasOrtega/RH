import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

namespace GlobalTheory.HTRho

/- English proof (translation)
Unfold `mSub`. Rewrite using `[Submodule.map_span]`. Use `congr 1`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨c, x, -, rfl⟩`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective G x`. Use `⟨σ (algebraMap C O c) y - χ c • y, ⟨c, y, trivial, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul]`. Both sides reduce to the same expression.

Introduce and unpack `⟨w, ⟨c, y, -, rfl⟩, rfl⟩`. Use `⟨c, G.mkQ y, trivial, ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, qAct_mk]`.
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
Use `⟨fun hJ => ?_, fun i => ?_⟩` and prove the remaining obligations. Unfold `jSub`. Rewrite using `[Submodule.span_eq_bot]`. Introduce and unpack `z ⟨r, lam, c, x, -, hc, rfl⟩`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective G x`.

Establish `hmem : (∑ l, lam l • σ (algebraMap C O (c l)) y) ∈ G` using `hJ (Submodule.subset_span ⟨r, lam, c, y, trivial, hc, rfl⟩)`. Establish `: (∑ l, lam l • qAct σ G hG (algebraMap C O (c l)) (Submodule.Quotient.mk y)) = G.mkQ (∑ l, lam l • σ (algebraMap C O (c l)) y)`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`.

Both sides reduce to the same expression. Rewrite using `[this, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hmem`. Rewrite using `[mSub_qAct_top]`. Conclude with `LinearEquiv.finrank_eq (Submodule.quotientQuotientEquivQuotientSup G (mSub σ (χ i) ⊤))`.
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
