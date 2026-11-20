import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupProductEqZeroOfVanishingOnCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Substitute using the available equality. Substitute using the available equality. Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression.
-/
private theorem ht_cast_cast' {q : ℕ} {E : Spc} {n i n' i' n'' i'' : ℤ} (x : Ht q E n i) (a : n = n') (b : i = i')
    (c : n' = n'') (d : i' = i'') : (x.cast a b).cast c d = x.cast (a.trans c) (b.trans d) := by
  subst a; subst b; subst c; subst d; rfl

/- English proof (translation)
Substitute using the available equality. Substitute using the available equality. Both sides reduce to the same expression.
-/
private theorem cup_cast_left' {q : ℕ} {E : Spc} {n m i j n' i' : ℤ} (x : Ht q E n i) (b : Ht q E m j) (hn : n = n')
    (hi : i = i') : cup q (x.cast hn hi) b = (cup q x b).cast (congrArg (· + m) hn) (congrArg (· + j) hi) := by
  subst hn; subst hi; rfl

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem cup_self_eq (q : ℕ) [NeZero q] {U V B : Spc} (g₁ : U ⟶ B) (g₂ : V ⟶ B) (ξ h : Ht q B 2 1)
    (hc : Cover2 (ZMod q) g₁ g₂) (h₁ : pull _ g₁ _ _ ξ = 0) (h₂ : pull _ g₂ _ _ ξ = pull _ g₂ _ _ h) :
    cup q ξ ξ = cup q h ξ := by
  have inj := (GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties (ZMod q) (tw q 1)).1
  have hz : cup q ξ (ξ - h) = 0 :=
    GlobalTheory.T.cupProduct_eq_zero_of_vanishing_on_cover (ZMod q) (twPair q 1 1) inj inj g₁ g₂ hc _ ξ (ξ - h) h₁ (by
      rw [map_sub]
      exact sub_eq_zero.mpr h₂)
  rw [map_sub, sub_eq_zero] at hz
  rw [hz, GlobalTheory.T.tateTwistCupProduct_graded_comm q B ξ h]
  norm_num
  rw [Int.negOnePow_even 4 ⟨2, rfl⟩, one_smul]
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Treat this case separately. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem UpperTheory.cpow_succ_eq_cup_of_two_cover :
    ∀ (q : ℕ) [NeZero q] {U V B : Spc} (g₁ : U ⟶ B) (g₂ : V ⟶ B) (ξ h : Ht q B 2 1), Inv q B → Cover2 (ZMod q) g₁ g₂ →
        pull _ g₁ _ _ ξ = 0 → pull _ g₂ _ _ ξ = pull _ g₂ _ _ h →
        ∀ j : ℕ, cpow q ξ (j + 1) = (cup q (cpow q h j) ξ).cast (by push_cast; ring) (by push_cast; ring) := by
  intro q _ U V B g₁ g₂ ξ h _ hc h₁ h₂ j
  induction j with
  | zero =>
    rw [cpow_succ]
    rfl
  | succ j ih =>
    rw [cpow_succ q ξ (j + 1), ih, cup_cast_left', ht_cast_cast', GlobalTheory.T.tateTwistCupProduct_assoc,
      ht_cast_cast', cup_self_eq q g₁ g₂ ξ h hc h₁ h₂]
    rw [cpow_succ q h j, cup_cast_left', ht_cast_cast', GlobalTheory.T.tateTwistCupProduct_assoc, ht_cast_cast']
