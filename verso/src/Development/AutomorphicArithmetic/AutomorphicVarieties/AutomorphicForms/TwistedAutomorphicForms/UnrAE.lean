import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev
import Mathlib.RingTheory.DedekindDomain.Different

open NumberField IsDedekindDomain

/- English proof (translation)
Unfold `UpperTheory.V.Af.Tw.UnrAE`. Introduce `F L _ _ _ _ _`. Use `letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))`. Use `haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance`. Establish `hD0 : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥` using `differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 L)`.

Establish `hfin` using `Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 F) (𝓞 L)) hD0`. Rewrite using `[Filter.eventually_cofinite]`. Use `(hfin.image (HeightOneSpectrum.under (𝓞 F))).subset ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_setOf_eq] at hv`.

Unfold `UpperTheory.V.Af.Tw.Unr at hv`. Use `push_neg at hv`. Take `⟨w, rfl, he⟩` from `hv`. Use `⟨w, ?_, rfl⟩` and prove the remaining obligations. Establish `hle : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤ w.asIdeal` using `Ideal.map_comap_le`.

Establish `h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤ w.asIdeal ^ 2`. Assume the negation of the conclusion as `h`. Conclude with `he (Ideal.ramificationIdx'_spec (by rwa [pow_one]) h)`. Use `haveI := (HeightOneSpectrum.under (𝓞 F) w).isMaximal`. Establish `hdvd` using `pow_sub_one_dvd_differentIdeal (A := 𝓞 F) (P := w.asIdeal) (e := 2) (hp := (HeightOneSpectrum.under (𝓞 F) w).ne_bot) (hP := Ideal.dvd_iff_le.mpr h2)`.

Simplify using `using hdvd`.
-/
theorem UpperTheory.V.Af.Tw.unrAE :
    UpperTheory.V.Af.Tw.UnrAE := by
  unfold UpperTheory.V.Af.Tw.UnrAE
  intro F L _ _ _ _ _
  letI := FractionRing.liftAlgebra (𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  have hD0 : differentIdeal (𝓞 F) (𝓞 L) ≠ ⊥ := differentIdeal_ne_bot (A := 𝓞 F) (B := 𝓞 L)
  have hfin := Ideal.finite_factors (R := 𝓞 L) (I := differentIdeal (𝓞 F) (𝓞 L)) hD0
  rw [Filter.eventually_cofinite]
  refine (hfin.image (HeightOneSpectrum.under (𝓞 F))).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq] at hv
  unfold UpperTheory.V.Af.Tw.Unr at hv
  push_neg at hv
  obtain ⟨w, rfl, he⟩ := hv
  refine ⟨w, ?_, rfl⟩
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal := Ideal.map_comap_le
  have h2 : Ideal.map (algebraMap (𝓞 F) (𝓞 L)) (HeightOneSpectrum.under (𝓞 F) w).asIdeal ≤
      w.asIdeal ^ 2 := by
    by_contra h
    exact he (Ideal.ramificationIdx'_spec (by rwa [pow_one]) h)
  haveI := (HeightOneSpectrum.under (𝓞 F) w).isMaximal
  have hdvd := pow_sub_one_dvd_differentIdeal (A := 𝓞 F) (P := w.asIdeal) (e := 2)
    (hp := (HeightOneSpectrum.under (𝓞 F) w).ne_bot) (hP := Ideal.dvd_iff_le.mpr h2)
  simpa using hdvd
