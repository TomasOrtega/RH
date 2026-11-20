import Development.AutomorphicArithmetic.ThetaCorrespondence.CrystallineComparison.LocalComparisonFromAlternative

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UpperTheory.Lit.Cmp.locTied_of6 : ∀ (l : ℕ) [inst : Fact (Nat.Prime l)] (P : Formalism.BasicNotions.LocPrime l) (AI : Formalism.BasicNotions.LocAinf l P),
    Nonempty (Formalism.BasicNotions.LocTied6 l P AI) → Nonempty (Formalism.BasicNotions.LocTied l P AI) :=
  Formalism.BasicNotions.CmpTie.local_comparison_from_alternative
