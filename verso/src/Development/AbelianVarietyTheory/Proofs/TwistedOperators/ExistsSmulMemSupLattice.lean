import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

open NumberField IsDedekindDomain Formalism.IndefR.Arith

namespace GlobalTheory.DenominatorExistenceTwistedOperators

/- English proof (translation)
Rewrite using `[FinitePlace.mk_apply]`. Establish `h1` using `FinitePlace.norm_le_one K v x`. Establish `h2` using `(FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx`. Conclude with `le_antisymm h1 (not_lt.mp h2)`.
-/
theorem abs_eq_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ∉ v.asIdeal) : FinitePlace.mk v (x : K) = 1 := by
  rw [FinitePlace.mk_apply]
  have h1 := FinitePlace.norm_le_one K v x
  have h2 := (FinitePlace.norm_lt_one_iff_mem K v x).not.mpr hx
  exact le_antisymm h1 (not_lt.mp h2)

/- English proof (translation)
Establish `hI : Ideal.span {d} ≠ 0`. Simplify `hd` using `[Ideal.span_singleton_eq_bot]`. Take `⟨n, J, hJ, hfac⟩` from `WfDvdMonoid.max_power_factor hI p.irreducible`. Rewrite `hJ` using `[Ideal.dvd_iff_le]`. Take `⟨s, hsJ, hsp⟩` from `SetLike.not_le_iff_exists.mp hJ`.

Use `⟨s, hsp, fun q hq => ?_⟩` and prove the remaining obligations. Establish `hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal`. Introduce `h`. Use `q.isPrime` as an intermediate fact. Establish `h1 : p.asIdeal ≤ q.asIdeal` using `Ideal.IsPrime.le_of_pow_le h`.

Conclude with `hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)`. Take `⟨t, ht, htq⟩` from `SetLike.not_le_iff_exists.mp hnle`. Use `⟨t, htq, ?_⟩` and prove the remaining obligations. Establish `: t * s ∈ Ideal.span {d}`. Rewrite using `[hfac]`.

Conclude with `Ideal.mul_mem_mul ht hsJ`. Take `⟨u, hu⟩` from `Ideal.mem_span_singleton'.mp this`. Conclude with `⟨u, hu.symm⟩`.
-/
theorem exists_prime_to_part {R : Type} [CommRing R] [IsDedekindDomain R] (p : HeightOneSpectrum R) (d : R)
    (hd : d ≠ 0) : ∃ s ∉ p.asIdeal, ∀ q : HeightOneSpectrum R, q ≠ p → ∃ t ∉ q.asIdeal, ∃ u, t * s = u * d := by
  have hI : Ideal.span {d} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hd
  obtain ⟨n, J, hJ, hfac⟩ := WfDvdMonoid.max_power_factor hI p.irreducible
  rw [Ideal.dvd_iff_le] at hJ
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.mp hJ
  refine ⟨s, hsp, fun q hq => ?_⟩
  have hnle : ¬ p.asIdeal ^ n ≤ q.asIdeal := by
    intro h
    have := q.isPrime
    have h1 : p.asIdeal ≤ q.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hq (HeightOneSpectrum.ext (p.isMaximal.eq_of_le q.isPrime.ne_top h1).symm)
  obtain ⟨t, ht, htq⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨t, htq, ?_⟩
  have : t * s ∈ Ideal.span {d} := by
    rw [hfac]; exact Ideal.mul_mem_mul ht hsJ
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp this
  exact ⟨u, hu.symm⟩

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha, hx⟩` from `hx`.

Take `⟨b, hb, hy⟩` from `hy`. Use `⟨a * b, mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `N.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `N.smul_mem _ hx`. Rewrite using `[mul_smul]`. Conclude with `N.smul_mem _ hy`. Consider the case `smul c x _ hx`. Take `⟨a, ha, hx⟩` from `hx`.

Take `⟨u, w, hw, rfl⟩` from `IsFractionRing.div_surjective (A := R) c`. Establish `hw0 : w ≠ 0` using `nonZeroDivisors.ne_zero hw`. Establish `hwK : algebraMap R K w ≠ 0` using `by simpa using hw0`. Use `⟨a * w, mul_ne_zero ha hw0, ?_⟩` and prove the remaining obligations. Establish `: (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x`.

Rewrite using `[← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[map_mul]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `N.smul_mem _ hx`.
-/
theorem exists_denominator {R K M : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower R K M] (N : Submodule R M) (x : M)
    (hx : x ∈ Submodule.span K (N : Set M)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hx
    · rw [mul_smul]; exact N.smul_mem _ hy
  | smul c x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨u, w, hw, rfl⟩ := IsFractionRing.div_surjective (A := R) c
    have hw0 : w ≠ 0 := nonZeroDivisors.ne_zero hw
    have hwK : algebraMap R K w ≠ 0 := by simpa using hw0
    refine ⟨a * w, mul_ne_zero ha hw0, ?_⟩
    have : (a * w) • (algebraMap R K u / algebraMap R K w) • x = u • a • x := by
      rw [← algebraMap_smul K (a * w), ← algebraMap_smul K u, ← algebraMap_smul K a, smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [this]
    exact N.smul_mem _ hx

/- English proof (translation)
Take `⟨d, hd, hdf⟩` from `exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)`. Take `⟨s, hs, hq⟩` from `exists_prime_to_part la d hd`. Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Establish `hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g` using `fun a g => (algebraMap_smul Ks a g).symm`. Establish `hm : s • (f : WL) ∈ Φ.WK` using `by rw [hsm]; exact Φ.WK.smul_mem _ f.2`.

Use `⟨hm, fun q y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : q = la`. Substitute `h` using the available equality. Establish `h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f` using `Subtype.ext (hsm s f)`. Rewrite using `[h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]`.

Conclude with `hf y`. Take `⟨t, ht, u, htu⟩` from `hq q h`. Establish `hmem : t • s • (f : WL) ∈ Φ.MK`. Rewrite using `[smul_smul, htu, mul_smul]`. Conclude with `Φ.MK.smul_mem _ hdf`.

Take `⟨hw, hb⟩` from `hmem`. Establish `h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩` using `Subtype.ext (hsm t _)`. Establish `h2` using `hb q y`. Rewrite `h2` using `[h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul]`. Then use the resulting hypothesis.
-/
theorem exists_smul_mem_supLattice (LL Ks WL G : Type) [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
    [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] (W : (LL →+* ℂ) → Type)
    [(σ : LL →+* ℂ) → NormedAddCommGroup (W σ)] [(σ : LL →+* ℂ) → InnerProductSpace ℂ (W σ)] [Group G]
    (Φ : FormsL LL Ks WL W G) (hspan : Submodule.span Ks (Φ.MK : Set WL) = Φ.WK)
    (la : HeightOneSpectrum (𝓞 Ks)) (f : Φ.WK) (hf : ∀ y : Φ.Pt la, Φ.nrm la y f ≤ 1) :
    ∃ s ∉ la.asIdeal, s • (f : WL) ∈ Φ.MK := by
  obtain ⟨d, hd, hdf⟩ := exists_denominator (K := Ks) Φ.MK (f : WL) (by rw [hspan]; exact f.2)
  obtain ⟨s, hs, hq⟩ := exists_prime_to_part la d hd
  refine ⟨s, hs, ?_⟩
  have hsm : ∀ (a : 𝓞 Ks) (g : WL), a • g = (a : Ks) • g := fun a g => (algebraMap_smul Ks a g).symm
  have hm : s • (f : WL) ∈ Φ.WK := by rw [hsm]; exact Φ.WK.smul_mem _ f.2
  refine ⟨hm, fun q y => ?_⟩
  by_cases h : q = la
  · subst h
    have h1 : (⟨s • (f : WL), hm⟩ : Φ.WK) = (s : Ks) • f := Subtype.ext (hsm s f)
    rw [h1, Φ.nrm_smul, abs_eq_one q s hs, one_mul]
    exact hf y
  · obtain ⟨t, ht, u, htu⟩ := hq q h
    have hmem : t • s • (f : WL) ∈ Φ.MK := by
      rw [smul_smul, htu, mul_smul]; exact Φ.MK.smul_mem _ hdf
    obtain ⟨hw, hb⟩ := hmem
    have h1 : (⟨t • s • (f : WL), hw⟩ : Φ.WK) = (t : Ks) • ⟨s • (f : WL), hm⟩ := Subtype.ext (hsm t _)
    have h2 := hb q y
    rwa [h1, Φ.nrm_smul, abs_eq_one q t ht, one_mul] at h2

end GlobalTheory.DenominatorExistenceTwistedOperators
