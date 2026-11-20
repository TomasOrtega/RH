import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

namespace GlobalTheory

open Cardinal

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem cardinalMk_padic_eq_continuum (l : ℕ) [Fact l.Prime] : #ℚ_[l] = 𝔠 := by
  apply le_antisymm
  · have hd := Padic.denseRange_ratCast l
    have h : ∀ x : ℚ_[l], ∃ u : ℕ → ℚ,
        Filter.Tendsto (fun n => (u n : ℚ_[l])) Filter.atTop (nhds x) := by
      intro x
      obtain ⟨v, hv, hx⟩ := mem_closure_iff_seq_limit.1 (hd x)
      choose u hu using hv
      exact ⟨u, by simpa only [hu] using hx⟩
    choose u hu using h
    have hi : Function.Injective u := fun x y hxy =>
      tendsto_nhds_unique (hu x) (hxy ▸ hu y)
    refine (Cardinal.mk_le_of_injective hi).trans ?_
    simp
  · exact continuum_le_cardinal_of_nontriviallyNormedField ℚ_[l]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cardinalMk_padicAlgCl_eq_continuum (l : ℕ) [Fact l.Prime] : #(PadicAlgCl l) = 𝔠 := by
  apply le_antisymm
  · exact (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[l] (PadicAlgCl l)).trans
      (max_le (cardinalMk_padic_eq_continuum l).le Cardinal.aleph0_le_continuum)
  · rw [← cardinalMk_padic_eq_continuum l]
    exact Cardinal.mk_le_of_injective (algebraMap ℚ_[l] (PadicAlgCl l)).injective

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nonempty_padicAlgCl_ringEquiv_complex (l : ℕ) [Fact l.Prime] :
    Nonempty (PadicAlgCl l ≃+* ℂ) :=
  IsAlgClosed.ringEquiv_of_equiv_of_charZero
    (by rw [cardinalMk_padicAlgCl_eq_continuum]; exact Cardinal.aleph0_lt_continuum)
    (Cardinal.eq.mp (by rw [cardinalMk_padicAlgCl_eq_continuum, Cardinal.mk_complex]))

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [Countable K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, ∀ x, e (a x) = b x := by
  obtain ⟨e₀⟩ := nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨σ, hσ⟩ := GaloisDescent.exists_complex_ringEquiv_comp_eq (e₀.toRingHom.comp a) b
  exact ⟨e₀.trans σ, fun x => hσ x⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_padicAlgCl_ringEquiv_complex_comp_eq (l : ℕ) [Fact l.Prime]
    (K : Type) [Field K] [NumberField K] (a : K →+* PadicAlgCl l) (b : K →+* ℂ) :
    ∃ e : PadicAlgCl l ≃+* ℂ, (e : PadicAlgCl l →+* ℂ).comp a = b := by
  haveI : Countable K := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨e, he⟩ := exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable l K a b
  exact ⟨e, RingHom.ext he⟩

end GlobalTheory
