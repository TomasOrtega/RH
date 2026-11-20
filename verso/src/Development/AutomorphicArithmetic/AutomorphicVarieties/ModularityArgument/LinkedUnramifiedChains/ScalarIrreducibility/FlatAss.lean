import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.RedDefs

/- English proof (translation)
Establish `h1 : ∑ _i : Fin 1, a • r = 0`. Rewrite using `[Fin.sum_univ_one]`. Conclude with `h`. Take `⟨l, c, y, hy, hc⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a) (x := fun _ : Fin 1 => r) h1`. Establish `hr : r = ∑ j, c 0 j • y j` using `hy 0`.

Rewrite using `[hr]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Use `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))` and prove the remaining obligations. Establish `h2` using `hc j`.

Rewrite `h2` using `[Fin.sum_univ_one]`. Rewrite using `[mul_comm]`. Conclude with `h2`.
-/
private theorem flatAss_ann {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) (r : R) (h : a • r = 0) :
    r ∈ P.map (algebraMap A R) := by
  have h1 : ∑ _i : Fin 1, a • r = 0 := by
    rw [Fin.sum_univ_one]
    exact h
  obtain ⟨l, c, y, hy, hc⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (f := fun _ : Fin 1 => a)
      (x := fun _ : Fin 1 => r) h1
  have hr : r = ∑ j, c 0 j • y j := hy 0
  rw [hr]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem _).2 ?_))
  have h2 := hc j
  rw [Fin.sum_univ_one] at h2
  rw [mul_comm]
  exact h2

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `r hr`. Establish `h0 : r * algebraMap A R a = 0` using `congrArg Subtype.val (Module.mem_annihilator.1 hr ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)`. Use `flatAss_ann P a hmem r ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`.

Conclude with `h0`. Use `Ideal.map_le_iff_le_comap.2 fun b hb => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, Module.mem_annihilator]`. Introduce and unpack `⟨n, hn⟩`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hn`.

Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap A R b * (c * algebraMap A R a) = 0`. Rewrite using `[mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]`.
-/
private theorem flatAss_annih {A R : Type} [CommRing A] [CommRing R] [Algebra A R] [Module.Flat A R]
    (P : Ideal A) (a : A) (hmem : ∀ b, b ∈ P ↔ b * a = 0) :
    Module.annihilator R (Ideal.span {algebraMap A R a} : Ideal R) = P.map (algebraMap A R) := by
  apply le_antisymm
  · intro r hr
    have h0 : r * algebraMap A R a = 0 :=
      congrArg Subtype.val (Module.mem_annihilator.1 hr
        ⟨algebraMap A R a, Ideal.mem_span_singleton_self _⟩)
    refine flatAss_ann P a hmem r ?_
    rw [Algebra.smul_def, mul_comm]
    exact h0
  · refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
    rw [Ideal.mem_comap, Module.mem_annihilator]
    rintro ⟨n, hn⟩
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hn
    apply Subtype.ext
    change algebraMap A R b * (c * algebraMap A R a) = 0
    rw [mul_left_comm, ← map_mul, (hmem b).1 hb, map_zero, mul_zero]

/- English proof (translation)
Use `haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat`. Take `⟨hPp, a, hPa⟩` from `isAssociatedPrime_iff.1 hP`. Establish `hmem : ∀ b, b ∈ P ↔ b * a = 0` using `fun b => by`. Rewrite using `[hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]`. Establish `hmapQ : P.map (algebraMap A R) ≤ Q` using `Ideal.map_le_iff_le_comap.2 hPQ`.

Use `haveI := hQ`. Take `⟨Q', hQ'min, hQ'Q⟩` from `Ideal.exists_minimalPrimes_le hmapQ`. Establish `hQ'ass : Q' ∈ associatedPrimes R R`. Establish `h1` using `hQ'min`. Rewrite `h1` using `[← flatAss_annih P a hmem]`.

Conclude with `associatedPrimes.subset_of_injective (Submodule.injective_subtype _) (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)`. Establish `hQ'm` using `hmin Q' hQ'ass hQ'Q`. Use `haveI hQ'p : Q'.IsPrime := hQ'min.1.1`. Use `⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩` and prove the remaining obligations. Use `haveI := hp.1`.

Establish `hPc : P ≤ Q'.comap (algebraMap A R)` using `Ideal.map_le_iff_le_comap.1 hQ'min.1.2`. Use `haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩`. Take `⟨Q'', hle, hQ''p, hlies⟩` from `Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)`. Establish `hge` using `hQ'm.2 ⟨hQ''p, bot_le⟩ hle`. Establish `heq : Q'' = Q'` using `le_antisymm hle hge`.

Rewrite using `[hlies.over, heq]`. Conclude with `hPc`.
-/
private theorem flatAss_alg {A R : Type} [CommRing A] [CommRing R] [IsNoetherianRing A]
    [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (Q : Ideal R) (hQ : Q.IsPrime)
    (hmin : ∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R)
    (P : Ideal A) (hP : P ∈ associatedPrimes A A) (hPQ : P ≤ Q.comap (algebraMap A R)) :
    P ∈ minimalPrimes A := by
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  obtain ⟨hPp, a, hPa⟩ := isAssociatedPrime_iff.1 hP
  have hmem : ∀ b, b ∈ P ↔ b * a = 0 := fun b => by
    rw [hPa, Submodule.mem_colon_singleton, Submodule.mem_bot, smul_eq_mul]
  have hmapQ : P.map (algebraMap A R) ≤ Q := Ideal.map_le_iff_le_comap.2 hPQ
  haveI := hQ
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hmapQ
  have hQ'ass : Q' ∈ associatedPrimes R R := by
    have h1 := hQ'min
    rw [← flatAss_annih P a hmem] at h1
    exact associatedPrimes.subset_of_injective (Submodule.injective_subtype _)
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R _ h1)
  have hQ'm := hmin Q' hQ'ass hQ'Q
  haveI hQ'p : Q'.IsPrime := hQ'min.1.1
  refine ⟨⟨hPp, bot_le⟩, fun p hp hpP => ?_⟩
  haveI := hp.1
  have hPc : P ≤ Q'.comap (algebraMap A R) := Ideal.map_le_iff_le_comap.1 hQ'min.1.2
  haveI : Q'.LiesOver (Q'.comap (algebraMap A R)) := ⟨rfl⟩
  obtain ⟨Q'', hle, hQ''p, hlies⟩ := Ideal.exists_ideal_le_liesOver_of_le Q' (hpP.trans hPc)
  have hge := hQ'm.2 ⟨hQ''p, bot_le⟩ hle
  have heq : Q'' = Q' := le_antisymm hle hge
  rw [hlies.over, heq]
  exact hPc

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J

/- English proof (translation)
Introduce `A R _ _ _ _ ι hι Q hQ hmin P hP hPQ` and use `@flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ`.
-/
theorem UpperTheory.V.J.flatAss :
    ∀ (A R : Type) [CommRing A] [CommRing R] [IsNoetherianRing A] [IsNoetherianRing R] (ι : A →+* R), ι.Flat → ∀ Q : Ideal R, Q.IsPrime →
        (∀ P ∈ associatedPrimes R R, P ≤ Q → P ∈ minimalPrimes R) → ∀ P ∈ associatedPrimes A A, P ≤ Q.comap ι → P ∈ minimalPrimes A :=
  fun A R _ _ _ _ ι hι Q hQ hmin P hP hPQ =>
    @flatAss_alg A R _ _ _ _ ι.toAlgebra hι Q hQ hmin P hP hPQ
