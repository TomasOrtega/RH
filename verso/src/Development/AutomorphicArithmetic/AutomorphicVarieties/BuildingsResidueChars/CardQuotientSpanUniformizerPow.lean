import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem card_step {O : Type} [CommRing O] [IsDomain O] (π : O) (h0 : π ≠ 0) (n : ℕ) :
    Nat.card (O ⧸ Ideal.span {π ^ (n + 1)}) =
      Nat.card (O ⧸ Ideal.span {π ^ n}) * Nat.card (O ⧸ Ideal.span {π}) := by
  have hrange : (AddMonoidHom.mulLeft (π ^ n)).range = (Ideal.span {π ^ n}).toAddSubgroup := by
    ext r
    simp [Ideal.mem_span_singleton', mul_comm]
  have hcomap : (Ideal.span {π ^ (n + 1)}).toAddSubgroup.comap (AddMonoidHom.mulLeft (π ^ n)) =
      (Ideal.span {π}).toAddSubgroup := by
    ext r
    simp only [AddSubgroup.mem_comap, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
    show π ^ (n + 1) ∣ π ^ n * r ↔ π ∣ r
    rw [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero n h0)]
  have hle : (Ideal.span {π ^ (n + 1)}).toAddSubgroup ≤ (Ideal.span {π ^ n}).toAddSubgroup := by
    intro r hr
    simp only [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at hr ⊢
    exact (pow_dvd_pow π (Nat.le_succ n)).trans hr
  show (Ideal.span {π ^ (n + 1)}).toAddSubgroup.index =
    (Ideal.span {π ^ n}).toAddSubgroup.index * (Ideal.span {π}).toAddSubgroup.index
  rw [← AddSubgroup.relIndex_mul_index hle, ← hcomap, AddSubgroup.index_comap, hrange, mul_comm]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Proceed by induction.

Treat this case separately. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Treat this case separately. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.card_quotient_span_uniformizer_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → ∀ π : O, Irreducible π → ∀ n : ℕ, Nat.card (O ⧸ Ideal.span {π ^ n}) = Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro O K _ _ _ _ _ Δ τ hL π hπ n
  have hres : Nat.card (IsLocalRing.ResidueField O) = Nat.card (O ⧸ Ideal.span {π}) := by
    rw [← hπ.maximalIdeal_eq]
    rfl
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.span_singleton_one]
    show (⊤ : Ideal O).toAddSubgroup.index = 1
    simp
  | succ k ih =>
    rw [card_step π hπ.ne_zero k, ih, hres, pow_succ]
