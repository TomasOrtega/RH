import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Evaluate the decidable proposition.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.HF.frobG_spec :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
      (∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ↔ H.galE σ = H.frobG p) ∧
      (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p ∧ (((H.frobG p).1.1 : ℤˣ) : ℤ) = H.psAt p ∧
      (H.frobG p ∉ φ.Psi ↔ H.Inert p) ∧ (H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1) ∧
      ∃ v : (ZMod (2 ^ (φ.e + 2)))ˣ, (v : ZMod (2 ^ (φ.e + 2))) = (p : ZMod _) ∧ φ.hH (H.frobG p).2 = hcl φ.e v := by
  intro φ H p hpr hnd
  have hp : Nat.Coprime p H.condN := (Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd
  have hodd : p % 2 = 1 := H.odd_of_coprime hp
  set u := ZMod.unitOfCoprime p hp with hu
  have hval : (u : ZMod H.condN).val ≡ p [MOD H.condN] := H.val_unitOfCoprime hp
  have hF : H.frobG p = H.art u := H.frobG_of_coprime hp
  have hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p := by
    rw [hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]
    exact jacobi_congr (hval.of_dvd H.d_dvd_condN)
  have hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1 := by
    rw [← hjac]
    rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]
  have hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1 := by
    rw [Frame.mem_Psi_iff, ← hjac]
    constructor
    · intro h
      rw [h]
      rfl
    · intro h
      exact Units.ext h
  refine ⟨?_, hjac, ?_, ?_, hpsi, ?_⟩
  · intro P _ _ σ
    rw [hF]
    exact H.frob_iff p hp P σ
  · rw [hF, H.psAt_of_coprime hp]
  · rw [hpsi]
    unfold UpperTheory.HF.Formalism.HC.HostRaw.Inert
    constructor
    · intro h
      refine ⟨hpr.out, ?_⟩
      rcases hne with h1 | h1
      · exact absurd h1 h
      · exact h1
    · rintro ⟨-, h⟩
      rw [h]
      decide
  · have hc2 : Nat.Coprime p (2 ^ (φ.e + 2)) :=
      Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp
    refine ⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩
    rw [hF]
    apply H.art_h
    rw [ZMod.coe_unitOfCoprime]
    exact ((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm
