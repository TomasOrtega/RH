import Mathlib

/- English proof (translation)
Introduce `R _ _ K _ _ _ S x`. Take `⟨⟨d, hdm⟩, hd⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x`. Simplify using `only at hd`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hdm`. Establish `hdK : algebraMap R K d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm`.

Establish `hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v`. Introduce `v`. Distinguish the cases in `hv : v ∈ S`. Take `⟨r, hr⟩` from `hd v hv`. Conclude with `⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩`.

Conclude with `⟨0, fun h => absurd h hv⟩`. Use `choose r hr using hr`. Establish `hI : Ideal.span {d} ≠ (0 : Ideal R)`. Simplify using `using hd0`. Set `T : Finset (IsDedekindDomain.HeightOneSpectrum R)` to `S ∪ (Ideal.finite_factors hI).toFinset`.

Set `e : IsDedekindDomain.HeightOneSpectrum R → ℕ` to `fun v => (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors`. Establish `he : ∀ v : IsDedekindDomain.HeightOneSpectrum R, v.intValuation d = WithZero.exp (-(e v : ℤ))` using `fun v => v.intValuation_if_neg hd0`. Establish `he0 : ∀ v, v ∉ T → e v = 0`. Introduce `v hv`. Establish `hmem : d ∉ v.asIdeal`.

Introduce `h`. Apply `hv` to reduce the goal to its premises. Simplify using `only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Conclude with `Or.inr (Ideal.dvd_span_singleton.2 h)`. Establish `h1` using `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem`.

Rewrite `h1` using `[he, ← WithZero.exp_zero, WithZero.exp_inj]`. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := T) (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h)) (fun v => if v.1 ∈ S then r v.1 else 0)`. Establish `key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v → v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1`. Introduce `v a ha`.

Rewrite using `[map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]`. Conclude with `div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le'`. Use `⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hvT : v ∈ T` using `Finset.mem_union_left _ hv`. Establish `h1` using `hy v hvT`.

Simplify using `only [hv, if_true] at h1`. Establish `h2` using `key v _ h1`. Establish `h3 : algebraMap R K (y - r v) / algebraMap R K d = algebraMap R K y / algebraMap R K d - x v`. Rewrite using `[map_sub, hr v hv]`. Clear the denominators using the available nonvanishing facts.

Rewrite `h2` using `[h3]`. Then use the resulting hypothesis. Apply `key` to reduce the goal to its premises. Distinguish the cases in `hvT : v ∈ T`. Establish `h1` using `hy v hvT`. Simplify `h1` using `[hv]`.

Simplify using `[he0 v hvT]`.
-/
theorem UpperTheory.Reformulated.B.ExistsValuationSubLeOne.exists_valuation_sub_le_one.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : IsDedekindDomain R] {K : Type u_2} [inst_2 : Field K]
    [inst_3 : Algebra R K] [inst_4 : IsFractionRing R K] (S : Finset (IsDedekindDomain.HeightOneSpectrum R))
    (x : IsDedekindDomain.HeightOneSpectrum R → K),
    ∃ (k : K),
      (∀ v ∈ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) (k - x v) ≤
            (1 : WithZero (Multiplicative ℤ))) ∧
        ∀ v ∉ S,
          (IsDedekindDomain.HeightOneSpectrum.valuation K v : K → WithZero (Multiplicative ℤ)) k ≤
            (1 : WithZero (Multiplicative ℤ)) := by
  classical
  intro R _ _ K _ _ _ S x
  obtain ⟨⟨d, hdm⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors R) S x
  simp only at hd
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdm
  have hdK : algebraMap R K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hdm
  have hr : ∀ v, ∃ r : R, v ∈ S → algebraMap R K r = algebraMap R K d * x v := by
    intro v
    by_cases hv : v ∈ S
    · obtain ⟨r, hr⟩ := hd v hv
      exact ⟨r, fun _ => by rw [hr, Algebra.smul_def]⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose r hr using hr
  have hI : Ideal.span {d} ≠ (0 : Ideal R) := by
    simpa using hd0
  let T : Finset (IsDedekindDomain.HeightOneSpectrum R) := S ∪ (Ideal.finite_factors hI).toFinset
  let e : IsDedekindDomain.HeightOneSpectrum R → ℕ := fun v =>
    (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {d} : Ideal R)).factors
  have he : ∀ v : IsDedekindDomain.HeightOneSpectrum R,
      v.intValuation d = WithZero.exp (-(e v : ℤ)) := fun v => v.intValuation_if_neg hd0
  have he0 : ∀ v, v ∉ T → e v = 0 := by
    intro v hv
    have hmem : d ∉ v.asIdeal := by
      intro h
      apply hv
      simp only [T, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      exact Or.inr (Ideal.dvd_span_singleton.2 h)
    have h1 := IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 hmem
    rw [he, ← WithZero.exp_zero, WithZero.exp_inj] at h1
    omega
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : IsDedekindDomain.HeightOneSpectrum R => v.asIdeal) e
    (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if v.1 ∈ S then r v.1 else 0)
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum R) (a : R), a ∈ v.asIdeal ^ e v →
      v.valuation K (algebraMap R K a / algebraMap R K d) ≤ 1 := by
    intro v a ha
    rw [map_div₀, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, he]
    exact div_le_one_of_le₀ ((v.intValuation_le_pow_iff_mem a (e v)).2 ha) zero_le'
  refine ⟨algebraMap R K y / algebraMap R K d, fun v hv => ?_, fun v hv => ?_⟩
  · have hvT : v ∈ T := Finset.mem_union_left _ hv
    have h1 := hy v hvT
    simp only [hv, if_true] at h1
    have h2 := key v _ h1
    have h3 : algebraMap R K (y - r v) / algebraMap R K d =
        algebraMap R K y / algebraMap R K d - x v := by
      rw [map_sub, hr v hv]
      field_simp
    rwa [h3] at h2
  · apply key
    by_cases hvT : v ∈ T
    · have h1 := hy v hvT
      simpa [hv] using h1
    · simp [he0 v hvT]
