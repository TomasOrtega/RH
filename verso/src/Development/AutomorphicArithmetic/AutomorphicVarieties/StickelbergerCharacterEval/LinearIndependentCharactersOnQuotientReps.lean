import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Replace the chosen expression with an arbitrary variable. Separate the alternatives or extract the components of the hypothesis.

Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem UpperTheory.V.B5.linearIndependent_characters_on_quotientReps :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ), c * c = 1 → LinearIndependent Ω (fun χ : Ch Ω c ε => fun i : Qc c => ((χ.1 (rep i) : Ωˣ) : Ω)) := by
  intro Ω _ Γ _ c ε h2
  classical
  have hw : LinearIndependent Ω (fun χ : Ch Ω c ε => fun g : Γ => ((χ.1 g : Ωˣ) : Ω)) := by
    have := (linearIndependent_monoidHom Γ Ω).comp
      (fun χ : Ch Ω c ε => (Units.coeHom Ω).comp χ.1) (by
        intro χ ψ h
        apply Subtype.ext
        ext g
        exact congrArg (fun f : Γ →* Ω => f g) h)
    exact this
  rw [linearIndependent_iff'] at hw ⊢
  intro s a hs
  apply hw s a
  funext g
  have hg := (mk_eq_mk h2 (rep (Qc.mk c g)) g).mp (mk_rep _)
  have hi := congrFun hs (Qc.mk c g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
  generalize rep (Qc.mk c g) = r at hg hi
  rcases hg with rfl | rfl
  · exact hi
  · calc ∑ χ ∈ s, a χ * ((χ.1 (c * r) : Ωˣ) : Ω)
        = ∑ χ ∈ s, (ε : Ω) * (a χ * ((χ.1 r : Ωˣ) : Ω)) :=
          Finset.sum_congr rfl (fun χ _ => by rw [map_mul, Units.val_mul, χ.2]; ring)
      _ = (ε : Ω) * ∑ χ ∈ s, a χ * ((χ.1 r : Ωˣ) : Ω) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hi, mul_zero]
