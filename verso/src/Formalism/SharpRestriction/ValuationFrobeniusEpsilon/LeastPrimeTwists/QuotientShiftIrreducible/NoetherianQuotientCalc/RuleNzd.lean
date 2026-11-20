import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

/- English proof (translation)
Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Treat this case separately. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem chi_of_subsingleton (ts : List (Deg k × R)) : ∀ (F : GMod B R k), Subsingleton F.M →
    ∀ m, chi ts F m = 0 := by
  induction ts with
  | nil =>
    intro F hF m
    have : Subsingleton (F.gr m) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    simp only [chi]
    rw [Module.length_eq_zero]
    rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hF m
    simp only [chi]
    have h1 : Subsingleton (F.quot s).M :=
      ⟨fun a b => by
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
        obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
        rw [Subsingleton.elim x y]⟩
    have h2 : Subsingleton (F.ann s d).M :=
      ⟨fun a b => Subtype.ext (Subsingleton.elim (α := F.M) _ _)⟩
    rw [ih _ h1, ih _ h2, sub_zero]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem chi_nzd (ts : List (Deg k × R)) (F : GMod B R k) (d : Deg k) (s : R)
    (h : ∀ x : F.M, s • x = 0 → x = 0) (m : Deg k) :
    chi ((d, s) :: ts) F m = chi ts (F.quot s) m := by
  have h2 : Subsingleton (F.ann s d).M :=
    ⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩
  simp only [chi]
  rw [chi_of_subsingleton ts _ h2, sub_zero]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem ruleNzd : RuleNzd := fun _ _ ts F d s h m => chi_nzd ts F d s h m

end Formalism.MainNotions.V.Pf.V2.Calc
