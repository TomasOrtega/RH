import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.MRatSpanRec

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Cmp

open Formalism.MainNotions.G Formalism.BasicNotions Formalism.MainNotions.G.LatticeSystems

variable {p : ℕ} (G : GAtP p) {LL : Type} [Field LL] (e : LL →+* G.Kf)

def RatX (ξ : G.P.Xsp) : Prop := ∃ Q : MvPolynomial _ LL, MvPolynomial.map e Q = ξ

def RatActG : Prop := ∀ (i : G.comp) (γ : (G.lev i).Γ) (ξ : G.P.Xsp), RatX G e ξ →
  RatX G e (((G.lev i).χ γ : G.O) • (G.lev i).actX γ ξ)

def HRat : Prop := ∀ L : G.P.Tup, G.P.IsLatTup L →
  G.P.HtupW L ≤ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW L ∧ RatX G e ξ}

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Substitute using the available equality. Supply the required witnesses or components. Supply the required witnesses or components.

A detailed English derivation is pending.
-/
theorem delta_rat (hA : RatActG G e) (i : G.comp) (L0 : G.P.Tup) (ξ : G.P.Xsp) (hξ : RatX G e ξ) :
    RatFn G e (delta G i L0 ξ) := by
  intro i' L
  simp only [delta]
  split_ifs with h h'
  · subst h'
    exact hA i' _ ξ hξ
  · exact ⟨0, map_zero _⟩
  · exact ⟨0, map_zero _⟩

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem mRatSpan_of (h1 : G.TrivStab) (h2 : G.FinClasses) (hE : EquivSys G G.P.HtupW) (hA : RatActG G e)
    (hH : HRat G e) : MRatSpan G.P G.comp e G.M := by
  classical
  unfold MRatSpan
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  · intro F hF
    obtain ⟨reps, hR⟩ := jd_reps G h2
    rw [jd_decomp G h1 reps hR G.P.HtupW F hF]
    refine Submodule.sum_mem _ (fun r hr => ?_)
    have hL := hR.1 r hr
    have hmem : F r.1 r.2 ∈ G.P.HtupW r.2 := ((jd_fmem G _ F).1 hF r.1).1 r.2 hL
    suffices key : ∀ ξ ∈ Submodule.span G.O {ξ | ξ ∈ G.P.HtupW r.2 ∧ RatX G e ξ},
        delta G r.1 r.2 ξ ∈ Submodule.span G.O
          (cmpF G.P G.comp e G.M '' intLL G.P G.comp e G.M) from key _ (hH r.2 hL hmem)
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem ξ hξ =>
      obtain ⟨hξW, hξR⟩ := hξ
      have hD := jd_mem G h1 _ hE r.1 r.2 hL ξ hξW
      exact Submodule.subset_span
        ⟨⟨delta G r.1 r.2 ξ, ⟨Submodule.subset_span hD, delta_rat G e hA r.1 r.2 ξ hξR⟩⟩, hD, rfl⟩
    | zero =>
      have h0 : delta G r.1 r.2 0 = 0 := by
        have h3 := jd_smul G r.1 r.2 0 0
        rwa [zero_smul, zero_smul] at h3
      rw [h0]
      exact Submodule.zero_mem _
    | add ξ η _ _ hξ hη =>
      rw [jd_add]
      exact Submodule.add_mem _ hξ hη
    | smul a ξ _ hξ =>
      rw [jd_smul]
      exact Submodule.smul_mem _ a hξ

end Formalism.L2.G.Cmp
