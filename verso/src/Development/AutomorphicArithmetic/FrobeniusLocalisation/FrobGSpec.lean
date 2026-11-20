import Development.AutomorphicArithmetic.FrobeniusLocalisation.SizeDefs

open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

/- English proof (translation)
Introduce `φ H p hpr hnd`. Establish `hp : Nat.Coprime p H.condN` using `(Nat.Prime.coprime_iff_not_dvd hpr.out).2 hnd`. Establish `hodd : p % 2 = 1` using `H.odd_of_coprime hp`. Use `set u := ZMod.unitOfCoprime p hp with hu`. Establish `hval : (u : ZMod H.condN).val ≡ p [MOD H.condN]` using `H.val_unitOfCoprime hp`.

Establish `hF : H.frobG p = H.art u` using `H.frobG_of_coprime hp`. Establish `hjac : (((H.frobG p).1.2 : ℤˣ) : ℤ) = jacobiSym (-(H.d : ℤ)) p`. Rewrite using `[hF, H.der.art_ch u, jacobi_neg_recip H.d_mod_four hodd]`. Conclude with `jacobi_congr (hval.of_dvd H.d_dvd_condN)`. Establish `hne : jacobiSym (-(H.d : ℤ)) p = 1 ∨ jacobiSym (-(H.d : ℤ)) p = -1`.

Rewrite using `[← hjac]`. Apply the tactic sequence `rcases Int.units_eq_one_or ((H.frobG p).1.2) with h | h <;> simp [h]`. Establish `hpsi : H.frobG p ∈ φ.Psi ↔ jacobiSym (-(H.d : ℤ)) p = 1`. Rewrite using `[Frame.mem_Psi_iff, ← hjac]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Rewrite using `[h]`. Both sides reduce to the same expression. Introduce `h`. Conclude with `Units.ext h`.

Use `⟨?_, hjac, ?_, ?_, hpsi, ?_⟩` and prove the remaining obligations. Introduce `P _ _ σ`. Rewrite using `[hF]`. Conclude with `H.frob_iff p hp P σ`. Rewrite using `[hF, H.psAt_of_coprime hp]`.

Rewrite using `[hpsi]`. Unfold `UpperTheory.HF.Formalism.HC.HostRaw.Inert`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨hpr.out, ?_⟩` and prove the remaining obligations.

Break down `hne with h1 | h1` into its components or cases. Conclude with `absurd h1 h`. Conclude with `h1`. Introduce and unpack `⟨-, h⟩`. Rewrite using `[h]`.

Evaluate the decidable proposition. Establish `hc2 : Nat.Coprime p (2 ^ (φ.e + 2))` using `Nat.Coprime.coprime_dvd_right H.tower_dvd_condN hp`. Use `⟨ZMod.unitOfCoprime p hc2, by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[hF]`. Apply `H.art_h` to reduce the goal to its premises.

Rewrite using `[ZMod.coe_unitOfCoprime]`. Conclude with `((ZMod.natCast_eq_natCast_iff _ _ _).2 (hval.of_dvd H.tower_dvd_condN)).symm`.
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
