import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.exists_injective_places_above_l_of_tower :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), ∃ pl : T.ι → HeightOneSpectrum (𝓞 T.F), Function.Injective pl ∧ ∀ v, IsPlaceOver (T.pl v) (pl v) ∧ ((l : ℕ) : 𝓞 T.F) ∈ (pl v).asIdeal := by
  intro Ω _ _ _ l _ c D T
  haveI := T.nF
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨_, hex, hne, _⟩ := UpperTheory.V.Kum.placeDict T.F Ω
  have hpl : ∀ v, ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w :=
    fun v => hex _ (hne _ l (Fact.out : l.Prime).ne_zero (T.ovl v))
  choose pl hpl using hpl
  refine ⟨pl, ?_, fun v => ⟨hpl v, ?_⟩⟩
  · intro v w hvw
    have h1 := hpl v
    have h2 := hpl w
    rw [hvw] at h1
    obtain ⟨σ, hσ⟩ := exists_smul_eq_of_isPlaceOver h1 h2
    obtain ⟨u, _, huniq⟩ := T.cover (T.pl w) (T.ovl w)
    have hv : v = u := by
      apply huniq v
      refine ⟨σ, fun x => ?_⟩
      rw [← hσ]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    have hw : w = u := by
      apply huniq w
      exact ⟨1, fun x => Iff.rfl⟩
    rw [hv, hw]
  · apply (hpl v (l : 𝓞 T.F)).1
    simpa using T.ovl v
