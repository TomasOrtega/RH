import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem

open UpperTheory.V.KL

/- English proof (translation)
Establish `hI : Ideal.span {a} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ha`. Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := (Ideal.finite_factors hI).toFinset) (fun v => v.asIdeal) (fun _ => 1) (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime) (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h)) (fun v => if c v.1.asIdeal then 1 …`. Use `⟨y, fun P hP haP => ?_⟩` and prove the remaining obligations.

Establish `hPb : P ≠ ⊥`. Introduce `h`. Rewrite `haP` using `[h, Ideal.mem_bot]`. Conclude with `ha haP`. Set `v : IsDedekindDomain.HeightOneSpectrum R` to `⟨P, hP.isPrime, hPb⟩`.

Establish `hv : v ∈ (Ideal.finite_factors hI).toFinset`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `haP`. Establish `h` using `hy v hv`. Simplify using `only [pow_one] at h`.

Prove the components needed by the constructor for the conclusion. Introduce `hc`. Simplify `h` using `[v, hc]`. Introduce `hc`. Simplify `h` using `[v, hc]`.
-/
private theorem exists_crt_indicator {R : Type} [CommRing R] [IsDedekindDomain R] (a : R) (ha : a ≠ 0)
    (c : Ideal R → Prop) :
    ∃ t : R, ∀ P : Ideal R, P.IsMaximal → a ∈ P → (c P → t - 1 ∈ P) ∧ (¬ c P → t ∈ P) := by
  classical
  have hI : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := (Ideal.finite_factors hI).toFinset)
    (fun v => v.asIdeal) (fun _ => 1)
    (fun v _ => Ideal.prime_of_isPrime v.ne_bot v.isPrime)
    (fun v _ w _ hvw h => hvw (IsDedekindDomain.HeightOneSpectrum.ext h))
    (fun v => if c v.1.asIdeal then 1 else 0)
  refine ⟨y, fun P hP haP => ?_⟩
  have hPb : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at haP
    exact ha haP
  let v : IsDedekindDomain.HeightOneSpectrum R := ⟨P, hP.isPrime, hPb⟩
  have hv : v ∈ (Ideal.finite_factors hI).toFinset := by
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact haP
  have h := hy v hv
  simp only [pow_one] at h
  constructor
  · intro hc
    simpa [v, hc] using h
  · intro hc
    simpa [v, hc] using h

/- English proof (translation)
Unfold `Unimodular`. Prove the components needed by the constructor for the conclusion. Introduce `h P hP hv`. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← h, Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hv i`. Introduce `h`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Conclude with `h P hP fun i => hle (Ideal.subset_span ⟨i, rfl⟩)`.
-/
private theorem unimod_iff {R : Type} [CommRing R] {n : ℕ} (v : Fin n → R) :
    Unimodular R v ↔ ∀ P : Ideal R, P.IsMaximal → ¬ ∀ i, v i ∈ P := by
  unfold Unimodular
  constructor
  · intro h P hP hv
    apply hP.ne_top
    rw [eq_top_iff, ← h, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hv i
  · intro h
    by_contra hne
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    exact h P hP fun i => hle (Ideal.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Introduce `R _ _ n hn r hr`. Rewrite `hr` using `[unimod_iff]`. Distinguish the cases in `hz : ∀ i : Fin n, r i.castSucc = 0`. Use `⟨fun _ => 1, ?_⟩` and prove the remaining obligations. Rewrite using `[unimod_iff]`.

Introduce `P hP hall`. Apply `hr P hP` to reduce the goal to its premises. Establish `hl : r (Fin.last n) ∈ P`. Use `hall ⟨0, by omega⟩` as an intermediate fact. Simplify using `only [one_mul] at this`.

Rewrite `this` using `[hz, zero_add]`. Conclude with `this`. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact hl`.

Consider the case `cast j`. Rewrite using `[hz j]`. Conclude with `P.zero_mem`. Use `push_neg at hz`. Take `⟨j, hj⟩` from `hz`.

Choose the witnesses or unpack the hypotheses as in `⟨k, hkj⟩ : ∃ k : Fin n, k ≠ j := by`. Distinguish the cases in `h0 : j.val = 0`. Use `⟨⟨1, by omega⟩, fun h => ?_⟩` and prove the remaining obligations. Rewrite `h0` using `[← h]`. Simplify using `at h0`.

Conclude with `⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩`. Take `⟨t, ht⟩` from `exists_crt_indicator (r j.castSucc) hj (fun P => r k.castSucc ∈ P)`. Use `⟨fun i => if i = k then t else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[unimod_iff]`. Introduce `P hP hall`.

Distinguish the cases in `haP : r j.castSucc ∈ P`. Establish `hother : ∀ i : Fin n, i ≠ k → r i.castSucc ∈ P` using `fun i hi => by`. Simplify `hall i` using `[hi]`. Establish `hk : r k.castSucc + t * r (Fin.last n) ∈ P`. Simplify using `using hall k`.

Take `⟨h1, h2⟩` from `ht P hP haP`. Distinguish the cases in `hc : r k.castSucc ∈ P`. Establish `htr : t * r (Fin.last n) ∈ P`. Use `P.sub_mem hk hc` as an intermediate fact. Simplify using `using this`.

Break down `hP.isPrime.mem_or_mem htr with htP | hrP` into its components or cases. Apply `hP.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Use `P.sub_mem htP (h1 hc)` as an intermediate fact. Simplify using `using this`.

Apply `hr P hP` to reduce the goal to its premises. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact hrP`. Consider the case `cast m`.

Distinguish the cases in `hm : m = k`. Rewrite using `[hm]`. Conclude with `hc`. Conclude with `hother m hm`. Apply `hc` to reduce the goal to its premises.

Use `P.sub_mem hk (P.mul_mem_right (r (Fin.last n)) (h2 hc))` as an intermediate fact. Simplify using `using this`. Apply `haP` to reduce the goal to its premises. Use `hall j` as an intermediate fact. Simplify `this` using `[Ne.symm hkj]`.
-/
theorem UpperTheory.V.KL.dedekindSR :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R], StableRangeLe R 2 := by
  intro R _ _ n hn r hr
  rw [unimod_iff] at hr
  by_cases hz : ∀ i : Fin n, r i.castSucc = 0
  · refine ⟨fun _ => 1, ?_⟩
    rw [unimod_iff]
    intro P hP hall
    apply hr P hP
    have hl : r (Fin.last n) ∈ P := by
      have := hall ⟨0, by omega⟩
      simp only [one_mul] at this
      rw [hz, zero_add] at this
      exact this
    intro i
    induction i using Fin.lastCases with
    | last => exact hl
    | cast j =>
      rw [hz j]
      exact P.zero_mem
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    obtain ⟨k, hkj⟩ : ∃ k : Fin n, k ≠ j := by
      by_cases h0 : j.val = 0
      · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
        rw [← h] at h0
        simp at h0
      · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
    obtain ⟨t, ht⟩ := exists_crt_indicator (r j.castSucc) hj (fun P => r k.castSucc ∈ P)
    refine ⟨fun i => if i = k then t else 0, ?_⟩
    rw [unimod_iff]
    intro P hP hall
    by_cases haP : r j.castSucc ∈ P
    · have hother : ∀ i : Fin n, i ≠ k → r i.castSucc ∈ P := fun i hi => by
        simpa [hi] using hall i
      have hk : r k.castSucc + t * r (Fin.last n) ∈ P := by
        simpa using hall k
      obtain ⟨h1, h2⟩ := ht P hP haP
      by_cases hc : r k.castSucc ∈ P
      · have htr : t * r (Fin.last n) ∈ P := by
          have := P.sub_mem hk hc
          simpa using this
        rcases hP.isPrime.mem_or_mem htr with htP | hrP
        · apply hP.ne_top
          rw [Ideal.eq_top_iff_one]
          have := P.sub_mem htP (h1 hc)
          simpa using this
        · apply hr P hP
          intro i
          induction i using Fin.lastCases with
          | last => exact hrP
          | cast m =>
            by_cases hm : m = k
            · rw [hm]
              exact hc
            · exact hother m hm
      · apply hc
        have := P.sub_mem hk (P.mul_mem_right (r (Fin.last n)) (h2 hc))
        simpa using this
    · apply haP
      have := hall j
      simpa [Ne.symm hkj] using this
