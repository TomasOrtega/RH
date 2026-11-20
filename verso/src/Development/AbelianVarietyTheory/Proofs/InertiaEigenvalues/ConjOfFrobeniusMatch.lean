import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.TripleLocal GlobalTheory.TypeLeaf

noncomputable section

namespace GlobalTheory.TripleLocal

open GlobalTheory.RowTie (WDTie)

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem frobConj_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conj_of_frobMatch : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), FrobDense D → ∀ (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : D.naut.CG a) (s : ℝ) (r r' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)),
    IsAttachedAway D T ι π s r → Continuous (fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep r' →
    FrobMatch D π ι.toRingHom r' (s + (1 - (a : ℝ)) / 2) → ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  intro D T hD l _ ι a π s r r' h hc' hss' hm
  have hall := (hm.and (D.naut.locG_unr_ae π)).and (frobConj_natCast_notMem D.host.E l)
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 hall))
      (h.cont.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨⟨h1, hu⟩, hl⟩ := not_not.1 hw
    have e1 := (h.frob hl hu).2 B σ hB hσ
    have e2 := h1 B σ hB hσ
    have e : ((r σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((r' σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
      Polynomial.map_injective ι.toRingHom ι.injective (e1.trans e2.symm)
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' h.ss hss' htr

end GlobalTheory.TripleLocal

end
