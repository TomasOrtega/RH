import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem UpperTheory.GL.rec_surj :
    ∀ {φ : Frame} (H : HostAx φ), Function.Surjective (recH H.toHostRaw) ∧ Function.Injective (dirChar (recH H.toHostRaw)) := by
  intro φ H
  have hs : Function.Surjective (recH H.toHostRaw) :=
    (toE_bij φ).1.2.comp H.der.art_surj
  refine ⟨hs, ?_⟩
  intro ψ₁ ψ₂ h
  ext x
  obtain ⟨u, hu⟩ := hs (Multiplicative.ofAdd x)
  have h2 := congrArg (fun χ : DirichletCharacter ℂ H.toHostRaw.condN => χ (u : ZMod H.toHostRaw.condN)) h
  simp only [dirChar_unit, hu, toAdd_ofAdd] at h2
  exact h2
