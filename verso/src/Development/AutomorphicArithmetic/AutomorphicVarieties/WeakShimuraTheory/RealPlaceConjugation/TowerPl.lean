import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical Pointwise

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T`. Use `haveI := T.nF`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Use `haveI : Algebra.IsAlgebraic T.F Ω := Algebra.IsAlgebraic.tower_top (K := ℚ) T.F`.

Use `haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩`. Take `⟨_, hex, hne, _⟩` from `UpperTheory.V.Kum.placeDict T.F Ω`. Establish `hpl : ∀ v, ∃ w : HeightOneSpectrum (𝓞 T.F), IsPlaceOver (T.pl v) w` using `fun v => hex _ (hne _ l (Fact.out : l.Prime).ne_zero (T.ovl v))`. Use `choose pl hpl using hpl`. Use `⟨pl, ?_, fun v => ⟨hpl v, ?_⟩⟩` and prove the remaining obligations.

Introduce `v w hvw`. Establish `h1` using `hpl v`. Establish `h2` using `hpl w`. Rewrite `h1` using `[hvw]`. Take `⟨σ, hσ⟩` from `exists_smul_eq_of_isPlaceOver h1 h2`.

Take `⟨u, _, huniq⟩` from `T.cover (T.pl w) (T.ovl w)`. Establish `hv : v = u`. Apply `huniq v` to reduce the goal to its premises. Use `⟨σ, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← hσ]`.

Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff`. Establish `hw : w = u`. Apply `huniq w` to reduce the goal to its premises. Conclude with `⟨1, fun x => Iff.rfl⟩`. Rewrite using `[hv, hw]`.

Apply `(hpl v (l : 𝓞 T.F)).1` to reduce the goal to its premises. Simplify using `using T.ovl v`.
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
