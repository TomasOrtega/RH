import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost NumberField Ideal

/- English proof (translation)
Introduce `φ H`. Establish `hs : Function.Surjective (recH H.toHostRaw)` using `(toE_bij φ).1.2.comp H.der.art_surj`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Introduce `ψ₁ ψ₂ h`. Use extensionality with `x`.

Take `⟨u, hu⟩` from `hs (Multiplicative.ofAdd x)`. Establish `h2` using `congrArg (fun χ : DirichletCharacter ℂ H.toHostRaw.condN => χ (u : ZMod H.toHostRaw.condN)) h`. Simplify using `only [dirChar_unit, hu, toAdd_ofAdd] at h2`. Conclude with `h2`.
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
