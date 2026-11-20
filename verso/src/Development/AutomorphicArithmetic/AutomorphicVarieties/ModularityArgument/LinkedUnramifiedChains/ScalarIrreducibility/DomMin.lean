import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.V.J.domMin :
    ∀ (A : Type) [CommRing A] (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q) → ∀ P ∈ minimalPrimes A, P ≤ q → ∀ a ∈ P, ∃ s ∉ P, s * a = 0 := by
  intro A _ q _ hD P hP hPq a ha
  have hK : (RingHom.ker (algebraMap A (Localization.AtPrime q))).IsPrime := RingHom.ker_isPrime _
  have hle : RingHom.ker (algebraMap A (Localization.AtPrime q)) ≤ P := by
    intro x hx
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) x).1 hx
    have h0 : (m : A) * x ∈ P := by rw [hm]; exact P.zero_mem
    exact (hP.1.1.mem_or_mem h0).resolve_left (fun h => m.2 (hPq h))
  have hge : P ≤ RingHom.ker (algebraMap A (Localization.AtPrime q)) := hP.2 ⟨hK, bot_le⟩ hle
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl (Localization.AtPrime q) a).1 (hge ha)
  exact ⟨m, fun h => m.2 (hPq h), hm⟩
