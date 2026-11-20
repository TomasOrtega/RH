import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `l _ a _ O _ _ π Ep hE hπ`. Take `⟨hmon, -, hdvd, -⟩` from `hE`. Take `⟨h0, hsurj, hker⟩` from `hπ`. Use `haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP`. Establish `H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)})` using `{ mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn) monic := hmon }`.

Establish `hK : RingHom.ker (Polynomial.aeval (R` using `Wq l a) π) = Ideal.span {Ep} := by`. Use extensionality with `f`. Rewrite using `[RingHom.mem_ker, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Conclude with `hker f`.

Introduce and unpack `⟨g, rfl⟩`. Simplify using `[h0]`. Set `e1` to `Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π) (fun x => hsurj x)`. Set `e2` to `Ideal.quotientEquivAlgOfEq (Wq l a) hK`. Set `e` to `(e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv`.

Use `⟨e, fun f => ?_⟩` and prove the remaining obligations. Establish `h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f`. Apply `e1.injective` to reduce the goal to its premises. Simplify using `only [AlgEquiv.apply_symm_apply, e1]`. Both sides reduce to the same expression.

Simplify using `only [e, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]`. Simplify using `[e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]`.
-/
theorem bkStr_quotient_equiv : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (O : Type) [CommRing O] [Algebra (Wq l a) O] (π : O) (Ep : Polynomial (Wq l a)), (Ep.Monic ∧ 0 < Ep.natDegree ∧ (∀ i < Ep.natDegree, (l : Wq l a) ∣ Ep.coeff i) ∧ (∃ w : (Wq l a)ˣ, Ep.coeff 0 = (l : Wq l a) * w)) → (Polynomial.aeval π Ep = 0 ∧ (∀ x : O, ∃ f : Polynomial (Wq l a), Polynomial.aeval π f = x) ∧ ∀ f : Polynomial (Wq l a), Polynomial.aeval π f = 0 → Ep ∣ f) → ∃ str : O ≃+* ((Wq l a)⟦X⟧ ⧸ Ideal.span {(Ep : (Wq l a)⟦X⟧)}), ∀ f : Polynomial (Wq l a), str (Polynomial.aeval π f) = Ideal.Quotient.mk _ (f : (Wq l a)⟦X⟧) := by
  intro l _ a _ O _ _ π Ep hE hπ
  obtain ⟨hmon, -, hdvd, -⟩ := hE
  obtain ⟨h0, hsurj, hker⟩ := hπ
  haveI : IsAdicComplete (Ideal.span {(l : Wq l a)}) (Wq l a) := WittVector.isAdicCompleteIdealSpanP
  have H : Ep.IsDistinguishedAt (Ideal.span {(l : Wq l a)}) :=
    { mem := fun hn => Ideal.mem_span_singleton.2 (hdvd _ hn)
      monic := hmon }
  have hK : RingHom.ker (Polynomial.aeval (R := Wq l a) π) = Ideal.span {Ep} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    constructor
    · exact hker f
    · rintro ⟨g, rfl⟩
      simp [h0]
  let e1 := Ideal.quotientKerAlgEquivOfSurjective (f := Polynomial.aeval (R := Wq l a) π)
    (fun x => hsurj x)
  let e2 := Ideal.quotientEquivAlgOfEq (Wq l a) hK
  let e := (e1.symm.trans (e2.trans H.algEquivQuotient)).toRingEquiv
  refine ⟨e, fun f => ?_⟩
  have h1 : e1.symm (Polynomial.aeval π f) = Ideal.Quotient.mk _ f := by
    apply e1.injective
    simp only [AlgEquiv.apply_symm_apply, e1]
    rfl
  simp only [e, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.trans_apply, h1]
  simp [e2, Polynomial.IsDistinguishedAt.algEquivQuotient_apply]

end GlobalTheory
