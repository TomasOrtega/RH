import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FlipTwoThree

open IsLocalRing

/- English proof (translation)
Distinguish the cases in `hm : m = ⊥`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `hfin` using `(Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing`. Establish `hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B)`.

Introduce `x hx`. Simplify using `only [Set.mem_iUnion, id, SetLike.mem_coe]`. Distinguish the cases in `hx0 : x = 0`. Take `⟨P, hP, -⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m) ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))`. Conclude with `⟨P, hP, hx0 ▸ P.zero_mem⟩`.

Take `⟨P, hP, hPm⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m) ((Ideal.span_singleton_le_iff_mem _).mpr hx)`. Establish `hPp : P.IsPrime` using `hP.1.1`. Establish `hxP : x ∈ P` using `(Ideal.span_singleton_le_iff_mem _).mp hP.1.2`. Establish `hP1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP`. Establish `hfP : f ∈ P` using `h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm`.

Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P) ((Ideal.span_singleton_le_iff_mem _).mpr hfP)`. Establish `hQp : Q.IsPrime` using `hQ.1.1`. Establish `hfQ : f ∈ Q` using `(Ideal.span_singleton_le_iff_mem _).mp hQ.1.2`. Establish `hQ0 : ⊥ < Q` using `bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations.

Break down `hQP.eq_or_lt with e | hlt` into its components or cases. Conclude with `e ▸ hxP`. It suffices to derive a contradiction. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hQ0`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`.

Establish `h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1` using `(add_le_add h1 le_rfl).trans (h2.trans hP1)`. Simplify using `at h3`. Conclude with `absurd h3 (by decide)`. Take `⟨P, hP, hmP⟩` from `(Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥ (fun i hi _ _ => hi.1.1)).mp hsub`. Establish `hPp : P.IsPrime` using `hP.1.1`.

Conclude with `(Ideal.height_mono hmP).trans (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)`.
-/
private theorem UpperTheory.V.Pr.npe_height_le_one {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

/- English proof (translation)
Take `⟨p, ⟨hp, hQp, hfp⟩, hmax⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) {p : Ideal R | p.IsPrime ∧ Q ≤ p ∧ f ∉ p} ⟨Q, inferInstance, le_rfl, hf⟩`. Use `⟨p, hp, hQp, hfp, ?_⟩` and prove the remaining obligations. Use `haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top`. Use `haveI : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective`. Establish `hf0 : Ideal.Quotient.mk p f ≠ 0` using `fun h => hfp (Ideal.Quotient.eq_zero_iff_mem.mp h)`.

Establish `hh : (maximalIdeal (R ⧸ p)).height ≤ 1`. Use `UpperTheory.V.Pr.npe_height_le_one _ hf0 fun P hP hP0 _ => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hfP`. Establish `hle : p ≤ P.comap (Ideal.Quotient.mk p)` using `fun x hx => by`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]`.

Conclude with `P.zero_mem`. Use `hmax (P.comap (Ideal.Quotient.mk p)) ⟨Ideal.comap_isPrime _ _, hQp.trans hle, hfP⟩ (lt_of_le_of_ne hle fun e => hP0 ?_)` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `y hy`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Establish `: x ∈ p` using `by rw [e]; exact hy`. Conclude with `Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr this)`. Establish `hfm' : Ideal.Quotient.mk p f ∈ maximalIdeal (R ⧸ p)` using `by haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective`. Conclude with `map_nonunit _ f hfm`. Establish `hlt : (⊥ : Ideal (R ⧸ p)) < maximalIdeal (R ⧸ p)` using `bot_lt_iff_ne_bot.mpr fun e => hf0 (by simpa [e] using hfm')`.

Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`. Establish `h2 : (maximalIdeal (R ⧸ p)).height = 1` using `le_antisymm hh (le_trans le_add_self h1)`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h2]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.Pr.npe_dim_one {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (Q : Ideal R) [Q.IsPrime] {f : R} (hfm : f ∈ maximalIdeal R) (hf : f ∉ Q) :
    ∃ p : Ideal R, p.IsPrime ∧ Q ≤ p ∧ f ∉ p ∧ ringKrullDim (R ⧸ p) = 1 := by
  obtain ⟨p, ⟨hp, hQp, hfp⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) {p : Ideal R | p.IsPrime ∧ Q ≤ p ∧ f ∉ p}
    ⟨Q, inferInstance, le_rfl, hf⟩
  refine ⟨p, hp, hQp, hfp, ?_⟩
  haveI : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
  haveI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hf0 : Ideal.Quotient.mk p f ≠ 0 := fun h => hfp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hh : (maximalIdeal (R ⧸ p)).height ≤ 1 := by
    refine UpperTheory.V.Pr.npe_height_le_one _ hf0 fun P hP hP0 _ => ?_
    by_contra hfP
    have hle : p ≤ P.comap (Ideal.Quotient.mk p) := fun x hx => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact P.zero_mem
    refine hmax (P.comap (Ideal.Quotient.mk p))
      ⟨Ideal.comap_isPrime _ _, hQp.trans hle, hfP⟩ (lt_of_le_of_ne hle fun e => hP0 ?_)
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : x ∈ p := by rw [e]; exact hy
    exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr this)
  have hfm' : Ideal.Quotient.mk p f ∈ maximalIdeal (R ⧸ p) := by
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    exact map_nonunit _ f hfm
  have hlt : (⊥ : Ideal (R ⧸ p)) < maximalIdeal (R ⧸ p) :=
    bot_lt_iff_ne_bot.mpr fun e => hf0 (by simpa [e] using hfm')
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (maximalIdeal (R ⧸ p)).height = 1 := le_antisymm hh (le_trans le_add_self h1)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, h2]
  rfl

/- English proof (translation)
Rewrite using `[ringKrullDim_quotient, Order.le_krullDim_iff]`. Conclude with `⟨{ length := N toFun := fun i => ⟨q ⟨i + 1, by omega⟩, hJ.trans (q.monotone (a := ⟨1, by omega⟩) (b := ⟨i + 1, by omega⟩) (by simp [Fin.le_def]))⟩ step := fun i => q.strictMono (by simp [Fin.lt_def]) }, rfl⟩`.
-/
private theorem UpperTheory.V.Pr.npe_chain {R : Type} [CommRing R] (q : LTSeries (PrimeSpectrum R))
    (J : Ideal R) (N : ℕ) (hN : N + 1 ≤ q.length) (hJ : J ≤ (q ⟨1, by omega⟩).asIdeal) :
    (N : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) := by
  rw [ringKrullDim_quotient, Order.le_krullDim_iff]
  exact ⟨{ length := N
           toFun := fun i => ⟨q ⟨i + 1, by omega⟩,
             hJ.trans (q.monotone (a := ⟨1, by omega⟩) (b := ⟨i + 1, by omega⟩) (by simp [Fin.le_def]))⟩
           step := fun i => q.strictMono (by simp [Fin.lt_def]) }, rfl⟩

/- English proof (translation)
Introduce `R _ _ _ ϖ hϖ N hN ι _ a ha I hI`. Rewrite `hI` using `[UpperTheory.V.Pr.qdim, ringKrullDim_quotient, Order.le_krullDim_iff]`. Take `⟨l, hl⟩` from `hI`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hI0, hlast⟩ : ∃ s : LTSeries (PrimeSpectrum R), N + 1 ≤ s.length ∧ I ≤ s.head.asIdeal ∧ ϖ ∈ s.last.asIdeal := by`. Set `t : LTSeries (PrimeSpectrum R)` to `l.map Subtype.val (fun _ _ h => h)`.

Establish `ht : t.length = N + 1` using `hl`. Establish `hh : I ≤ t.head.asIdeal` using `l.head.2`. Establish `hle : t.last ≤ closedPoint R` using `le_maximalIdeal t.last.2.ne_top`. Break down `hle.eq_or_lt with e | hlt` into its components or cases. Conclude with `⟨t, ht.ge, hh, by rw [e]; exact hϖ⟩`.

Conclude with `⟨t.snoc _ hlt, by simp [ht], by simpa using hh, by rw [RelSeries.last_snoc]; exact hϖ⟩`. Take `⟨q, hq1, hqlen, hqh, -⟩` from `PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last s hlast`. Establish `hq : N + 1 ≤ q.length` using `hqlen ▸ hs`. Establish `e1 : (1 : Fin (q.length + 1)) = ⟨1, by omega⟩` using `by ext; simp [Nat.mod_eq_of_lt (show 1 < q.length + 1 by omega)]`. Rewrite `hq1` using `[e1]`.

Use `set Q := q ⟨1, by omega⟩ with hQ`. Establish `hIQ : I ≤ Q.asIdeal`. Rewrite `hI0` using `[hqh]`. Conclude with `hI0.trans (q.monotone (a := 0) (Fin.zero_le _))`. Establish `hQ2 : Q < q ⟨2, by omega⟩` using `q.strictMono (by simp [Fin.lt_def])`.

Take `⟨g, hg, hgQ⟩` from `SetLike.exists_of_lt (show Q.asIdeal < (q ⟨2, by omega⟩).asIdeal from hQ2)`. Establish `hgm : g ∈ maximalIdeal R` using `le_maximalIdeal (q ⟨2, by omega⟩).2.ne_top hg`. Establish `hna : ∀ i, ∃ x ∈ a i, x ∉ Q.asIdeal` using `fun i => SetLike.not_le_iff_exists.mp fun h => (UpperTheory.V.Pr.npe_chain q (a i) N hq h).not_gt (ha i)`. Use `choose x hxa hxQ using hna`. Use `haveI := Fintype.ofFinite ι`.

Establish `hf : g * ∏ i, x i ∉ Q.asIdeal` using `fun h => by`. Break down `Q.2.mem_or_mem h with h | h` into its components or cases. Conclude with `hgQ h`. Take `⟨i, -, hi⟩` from `Ideal.IsPrime.prod_mem_iff.mp h`. Conclude with `hxQ i hi`.

Take `⟨p, hp, hQp, hfp, hd⟩` from `UpperTheory.V.Pr.npe_dim_one Q.asIdeal (Ideal.mul_mem_right _ _ hgm) hf`. Use `⟨p, hp, hIQ.trans hQp, hd, hQp hq1, fun i hi => hfp (Ideal.mul_mem_left _ _ ?_)⟩` and prove the remaining obligations. Conclude with `Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem x (Finset.mem_univ i)) (hi (hxa i))`.
-/
theorem UpperTheory.V.Pr.nicePrimeEx :
    UpperTheory.V.Pr.NicePrimeEx := by
  classical
  intro R _ _ _ ϖ hϖ N hN ι _ a ha I hI
  rw [UpperTheory.V.Pr.qdim, ringKrullDim_quotient, Order.le_krullDim_iff] at hI
  obtain ⟨l, hl⟩ := hI
  obtain ⟨s, hs, hI0, hlast⟩ : ∃ s : LTSeries (PrimeSpectrum R), N + 1 ≤ s.length ∧
      I ≤ s.head.asIdeal ∧ ϖ ∈ s.last.asIdeal := by
    let t : LTSeries (PrimeSpectrum R) := l.map Subtype.val (fun _ _ h => h)
    have ht : t.length = N + 1 := hl
    have hh : I ≤ t.head.asIdeal := l.head.2
    have hle : t.last ≤ closedPoint R := le_maximalIdeal t.last.2.ne_top
    rcases hle.eq_or_lt with e | hlt
    · exact ⟨t, ht.ge, hh, by rw [e]; exact hϖ⟩
    · exact ⟨t.snoc _ hlt, by simp [ht], by simpa using hh, by rw [RelSeries.last_snoc]; exact hϖ⟩
  obtain ⟨q, hq1, hqlen, hqh, -⟩ := PrimeSpectrum.exist_ltSeries_mem_one_of_mem_last s hlast
  have hq : N + 1 ≤ q.length := hqlen ▸ hs
  have e1 : (1 : Fin (q.length + 1)) = ⟨1, by omega⟩ := by
    ext; simp [Nat.mod_eq_of_lt (show 1 < q.length + 1 by omega)]
  rw [e1] at hq1
  set Q := q ⟨1, by omega⟩ with hQ
  have hIQ : I ≤ Q.asIdeal := by
    rw [hqh] at hI0
    exact hI0.trans (q.monotone (a := 0) (Fin.zero_le _))
  have hQ2 : Q < q ⟨2, by omega⟩ := q.strictMono (by simp [Fin.lt_def])
  obtain ⟨g, hg, hgQ⟩ := SetLike.exists_of_lt (show Q.asIdeal < (q ⟨2, by omega⟩).asIdeal from hQ2)
  have hgm : g ∈ maximalIdeal R := le_maximalIdeal (q ⟨2, by omega⟩).2.ne_top hg
  have hna : ∀ i, ∃ x ∈ a i, x ∉ Q.asIdeal := fun i =>
    SetLike.not_le_iff_exists.mp fun h => (UpperTheory.V.Pr.npe_chain q (a i) N hq h).not_gt (ha i)
  choose x hxa hxQ using hna
  haveI := Fintype.ofFinite ι
  have hf : g * ∏ i, x i ∉ Q.asIdeal := fun h => by
    rcases Q.2.mem_or_mem h with h | h
    · exact hgQ h
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hxQ i hi
  obtain ⟨p, hp, hQp, hfp, hd⟩ := UpperTheory.V.Pr.npe_dim_one Q.asIdeal (Ideal.mul_mem_right _ _ hgm) hf
  refine ⟨p, hp, hIQ.trans hQp, hd, hQp hq1, fun i hi => hfp (Ideal.mul_mem_left _ _ ?_)⟩
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem x (Finset.mem_univ i)) (hi (hxa i))
