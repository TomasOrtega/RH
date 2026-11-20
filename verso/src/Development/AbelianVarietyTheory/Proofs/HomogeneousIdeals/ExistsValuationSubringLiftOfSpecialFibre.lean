import Mathlib

open IsLocalRing

namespace GlobalTheory

universe u

section Algebra

/- English proof (translation)
Distinguish the cases in `hm : m = ⊥`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Establish `hfin` using `(Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing`. Establish `hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B)`.

Introduce `x hx`. Simplify using `only [Set.mem_iUnion, id, SetLike.mem_coe]`. Distinguish the cases in `hx0 : x = 0`. Take `⟨P, hP, -⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m) ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))`. Conclude with `⟨P, hP, hx0 ▸ P.zero_mem⟩`.

Take `⟨P, hP, hPm⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m) ((Ideal.span_singleton_le_iff_mem _).mpr hx)`. Establish `hPp : P.IsPrime` using `hP.1.1`. Establish `hxP : x ∈ P` using `(Ideal.span_singleton_le_iff_mem _).mp hP.1.2`. Establish `hP1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP`. Establish `hfP : f ∈ P` using `h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm`.

Take `⟨Q, hQ, hQP⟩` from `Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P) ((Ideal.span_singleton_le_iff_mem _).mpr hfP)`. Establish `hQp : Q.IsPrime` using `hQ.1.1`. Establish `hfQ : f ∈ Q` using `(Ideal.span_singleton_le_iff_mem _).mp hQ.1.2`. Establish `hQ0 : ⊥ < Q` using `bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)`. Use `⟨Q, hQ, ?_⟩` and prove the remaining obligations.

Break down `hQP.eq_or_lt with e | hlt` into its components or cases. Conclude with `e ▸ hxP`. It suffices to derive a contradiction. Establish `h1` using `Ideal.height_add_one_le_of_lt_of_isPrime hQ0`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`.

Establish `h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1` using `(add_le_add h1 le_rfl).trans (h2.trans hP1)`. Simplify using `at h3`. Conclude with `absurd h3 (by decide)`. Take `⟨P, hP, hmP⟩` from `(Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥ (fun i hi _ _ => hi.1.1)).mp hsub`. Establish `hPp : P.IsPrime` using `hP.1.1`.

Conclude with `(Ideal.height_mono hmP).trans (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)`.
-/
theorem height_le_one_of_forall_mem {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
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
Establish `hfin : (I.minimalPrimes \ {p}).Finite` using `I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset`. Establish `: ¬ hfin.toFinset.inf id ≤ p`. Rewrite using `[Ideal.IsPrime.inf_le' inferInstance]`. Introduce and unpack `⟨P, hP, hle⟩`. Rewrite `hP` using `[Set.Finite.mem_toFinset]`.

Conclude with `hP.2 (hp P hP.1 hle)`. Take `⟨s, hs, hsp⟩` from `SetLike.not_le_iff_exists.mp this`. Use `⟨s, hsp, fun P hP hne => ?_⟩` and prove the remaining obligations. Conclude with `(Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs`.
-/
theorem exists_notMem_forall_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by
  classical
  have hfin : (I.minimalPrimes \ {p}).Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset
  have : ¬ hfin.toFinset.inf id ≤ p := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 (hp P hP.1 hle)
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp this
  refine ⟨s, hsp, fun P hP hne => ?_⟩
  exact (Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs

/- English proof (translation)
Establish `: IsNoetherianRing B` using `Algebra.FiniteType.isNoetherianRing O B`. Take `⟨s, hsm, hs⟩` from `exists_notMem_forall_mem_minimalPrimes (Ideal.span {algebraMap O B π}) m (fun P hP hle => by`. Establish `hPp : P.IsPrime` using `hP.1.1`. Establish `hfP : algebraMap O B π ∈ P` using `(Ideal.span_singleton_le_iff_mem _).mp hP.1.2`. Establish `hP0 : ⊥ < P` using `bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)`.

Assume the negation of the conclusion as `hne`. Establish `h2` using `Ideal.height_add_one_le_of_lt_of_isPrime hP0`. Establish `h3` using `Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)`. Establish `h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1` using `(add_le_add h2 le_rfl).trans (h3.trans h1)`. Simplify using `at h4`.

Conclude with `absurd h4 (by decide))`. Use `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_` and prove the remaining obligations. Use `isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨q, hq⟩`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen, Set.mem_singleton_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hsq`. Establish `hπq : algebraMap O B π ∈ q.asIdeal`. Establish `: π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal`. Rewrite `hq` using `[Set.mem_preimage, Set.mem_singleton_iff]`.

Rewrite using `[hq]`. Conclude with `hπm`. Conclude with `this`. Take `⟨P, hP, hPq⟩` from `Ideal.exists_minimalPrimes_le (J := q.asIdeal) ((Ideal.span_singleton_le_iff_mem _).mpr hπq)`. Establish `hPm : P = m`.

Assume the negation of the conclusion as `hne`. Conclude with `hsq (hPq (hs P hP hne))`. Substitute `hPm` using the available equality. Conclude with `Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm`. Introduce `e`.

Take `rfl : q = ⟨m, inferInstance⟩` from `congrArg Subtype.val e`. Conclude with `hsm`.
-/
theorem quasiFiniteAt_of_height_le_one {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨s, hsm, hs⟩ := exists_notMem_forall_mem_minimalPrimes
    (Ideal.span {algebraMap O B π}) m (fun P hP hle => by
      have hPp : P.IsPrime := hP.1.1
      have hfP : algebraMap O B π ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
      have hP0 : ⊥ < P := bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)
      by_contra hne
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
      have h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h3.trans h1)
      simp at h4
      exact absurd h4 (by decide))
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_
  refine isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩
  ext ⟨q, hq⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_singleton_iff]
  constructor
  · intro hsq
    have hπq : algebraMap O B π ∈ q.asIdeal := by
      have : π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
        rw [hq]
        exact hπm
      exact this
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hπq)
    have hPm : P = m := by
      by_contra hne
      exact hsq (hPq (hs P hP hne))
    subst hPm
    exact Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm
  · intro e
    obtain rfl : q = ⟨m, inferInstance⟩ := congrArg Subtype.val e
    exact hsm

/- English proof (translation)
Establish `hq : Algebra.QuasiFiniteAt O m` using `quasiFiniteAt_of_height_le_one m h1 π (fun e => hπ (hinj (by simpa using e))) hπm`. Set `K'` to `FractionRing B`. Set `L` to `Localization.AtPrime m`. Set `g : L →ₐ[B] K'` to `IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K') (fun y => by`. Establish `: (y : B) ≠ 0` using `fun e => y.2 (e ▸ m.zero_mem)`.

Conclude with `IsUnit.mk0 _ (by simpa [K'] using this))`. Establish `hqK : Algebra.QuasiFinite O K'`. Use `.of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := B) x`. Establish `hb' : algebraMap B K' b ≠ 0`.

Simplify `nonZeroDivisors.ne_zero hb` using `[K']`. Use `⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩` and prove the remaining obligations. Establish `: (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b` using `g.commutes b`. Rewrite using `[this]`. Conclude with `IsUnit.mk0 _ hb'`.

Simplify using `[div_mul_cancel₀ _ hb']`. Establish `hOK' : Function.Injective (algebraMap O K')`. Rewrite using `[IsScalarTower.algebraMap_eq O B K']`. Conclude with `(IsFractionRing.injective B K').comp hinj`. Set `_ : Algebra K K'` to `(IsFractionRing.lift (K := K) hOK').toAlgebra`.

Establish `hst : IsScalarTower O K K'` using `.of_algebraMap_eq fun a => by`. Simplify using `[RingHom.algebraMap_toAlgebra]`. Establish `: Algebra.QuasiFinite K K'` using `.of_restrictScalars O K K'`. Take `⟨O', hO', hloc⟩` from `IsLocalRing.exists_factor_valuationRing (g : L →+* K')`. Set `ψ : L →+* O'` to `(g : L →+* K').codRestrict O'.toSubring hO'`.

Establish `hψ : IsLocalHom ψ` using `hloc`. Establish `hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b` using `fun b => g.commutes b`. Use `⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L), fun a => ?_, fun a b hab => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`. Apply `IsFractionRing.injective B K'` to reduce the goal to its premises.

Rewrite using `[← hval, ← hval, hab]`. Rewrite using `[← Ideal.comap_comap, maximalIdeal_comap ψ]`. Conclude with `IsLocalization.AtPrime.under_maximalIdeal L m`.
-/
theorem exists_valuationSubring_of_height_le_one {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by
  have hq : Algebra.QuasiFiniteAt O m := quasiFiniteAt_of_height_le_one m h1 π
    (fun e => hπ (hinj (by simpa using e))) hπm
  let K' := FractionRing B
  let L := Localization.AtPrime m
  let g : L →ₐ[B] K' := IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K')
    (fun y => by
      have : (y : B) ≠ 0 := fun e => y.2 (e ▸ m.zero_mem)
      exact IsUnit.mk0 _ (by simpa [K'] using this))
  have hqK : Algebra.QuasiFinite O K' := by
    refine .of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb' : algebraMap B K' b ≠ 0 := by
      simpa [K'] using nonZeroDivisors.ne_zero hb
    refine ⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩
    · have : (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b := g.commutes b
      rw [this]
      exact IsUnit.mk0 _ hb'
    · simp [div_mul_cancel₀ _ hb']
  have hOK' : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O B K']
    exact (IsFractionRing.injective B K').comp hinj
  let _ : Algebra K K' := (IsFractionRing.lift (K := K) hOK').toAlgebra
  have hst : IsScalarTower O K K' := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.QuasiFinite K K' := .of_restrictScalars O K K'
  obtain ⟨O', hO', hloc⟩ := IsLocalRing.exists_factor_valuationRing (g : L →+* K')
  let ψ : L →+* O' := (g : L →+* K').codRestrict O'.toSubring hO'
  have hψ : IsLocalHom ψ := hloc
  have hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b := fun b =>
    g.commutes b
  refine ⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L),
    fun a => ?_, fun a b hab => ?_, ?_⟩
  · rw [hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · apply IsFractionRing.injective B K'
    rw [← hval, ← hval, hab]
  · rw [← Ideal.comap_comap, maximalIdeal_comap ψ]
    exact IsLocalization.AtPrime.under_maximalIdeal L m

/- English proof (translation)
Take `⟨p₀, hp₀, hp₀m⟩` from `h`. Take `⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩` from `set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian A A) (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩`. Use `⟨q, hqU, hqm, ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨f, rfl⟩, hfq, hfU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU`. Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := q.asIdeal)`.

Establish `: (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime` using `Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)`. Use `height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f) (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hfp`. Set `p' : PrimeSpectrum A` to `⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩`. Establish `hle : q.asIdeal ≤ p'.asIdeal` using `fun x hx => by`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk q.asIdeal x ∈ p`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hx]`. Conclude with `p.zero_mem`. Establish `hp'm : p'.asIdeal ≤ m`. Use `(Ideal.comap_mono hpm).trans ?_` and prove the remaining obligations.

Rewrite using `[Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Conclude with `sup_le le_rfl hqm`. Use `hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `x hx`.

Take `⟨x, rfl⟩` from `hsurj x`. Establish `: x ∈ q.asIdeal` using `e ▸ hx`. Simplify using `using Ideal.Quotient.eq_zero_iff_mem.mpr this`.
-/
theorem exists_mem_height_map_le_one {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by
  obtain ⟨p₀, hp₀, hp₀m⟩ := h
  obtain ⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)
    (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩
  refine ⟨q, hqU, hqm, ?_⟩
  obtain ⟨_, ⟨f, rfl⟩, hfq, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)
  refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f)
    (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_
  by_contra hfp
  let p' : PrimeSpectrum A := ⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩
  have hle : q.asIdeal ≤ p'.asIdeal := fun x hx => by
    change Ideal.Quotient.mk q.asIdeal x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  have hp'm : p'.asIdeal ≤ m := by
    refine (Ideal.comap_mono hpm).trans ?_
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_le le_rfl hqm
  refine hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := hsurj x
  have : x ∈ q.asIdeal := e ▸ hx
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr this

/- English proof (translation)
Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing O A`. Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hπm : algebraMap O A π ∈ m`. Rewrite using `[← Ideal.mem_comap, hmO, hπ.maximalIdeal_eq]`. Conclude with `Ideal.mem_span_singleton_self π`.

Take `⟨q, ⟨hqU, hqπ⟩, hqm, hht⟩` from `exists_mem_height_map_le_one m (hU.inter (PrimeSpectrum.basicOpen (algebraMap O A π)).isOpen) (by`. Take `⟨p, hpU, hpm, hp⟩` from `h`. Use `⟨p, ⟨hpU, fun hπp => hp ?_⟩, hpm⟩` and prove the remaining obligations. Use `le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_` and prove the remaining obligations. Rewrite using `[hπ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hπp)`. Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := q.asIdeal)`. Establish `hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m`. Rewrite using `[Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]`. Conclude with `sup_eq_left.mpr hqm`.

Establish `: (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal` using `(Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by`. Rewrite `hcomap` using `[e, Ideal.comap_top]`. Conclude with `hm.ne_top hcomap.symm`. Establish `hinj : Function.Injective (algebraMap O (A ⧸ q.asIdeal))`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ`. Rewrite `ha` using `[map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero]`. Conclude with `hqπ (Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero ha))`.

Take `⟨K', _, _, _, O', φ, hφ, hφi, hφm⟩` from `exists_valuationSubring_of_height_le_one (K := K) hinj (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ.ne_zero (Ideal.mem_map_of_mem _ hπm)`. Use `⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp (Ideal.Quotient.mk _), hφ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.comap_comap, hφm, hcomap]`. Use `hqU` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Express the relevant statement in the definitionally equal form `φ (Ideal.Quotient.mk _ x) ∈ (⊥ : Ideal O') ↔ _`. Rewrite using `[Ideal.mem_bot, map_eq_zero_iff φ hφi, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem exists_valuationSubring_lift_of_exists_le {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A]
    (m : Ideal A) [hm : m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hπm : algebraMap O A π ∈ m := by
    rw [← Ideal.mem_comap, hmO, hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  obtain ⟨q, ⟨hqU, hqπ⟩, hqm, hht⟩ := exists_mem_height_map_le_one m
    (hU.inter (PrimeSpectrum.basicOpen (algebraMap O A π)).isOpen)
    (by
      obtain ⟨p, hpU, hpm, hp⟩ := h
      refine ⟨p, ⟨hpU, fun hπp => hp ?_⟩, hpm⟩
      refine le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
      rw [hπ.maximalIdeal_eq, Ideal.span_singleton_le_iff_mem]
      exact hπp)
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have hcomap : (m.map (Ideal.Quotient.mk q.asIdeal)).comap (Ideal.Quotient.mk q.asIdeal) = m := by
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm).resolve_left fun e => by
      rw [e, Ideal.comap_top] at hcomap
      exact hm.ne_top hcomap.symm
  have hinj : Function.Injective (algebraMap O (A ⧸ q.asIdeal)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
    rw [map_mul, map_pow, (u.isUnit.map _).mul_right_eq_zero] at ha
    exact hqπ (Ideal.Quotient.eq_zero_iff_mem.mp (eq_zero_of_pow_eq_zero ha))
  obtain ⟨K', _, _, _, O', φ, hφ, hφi, hφm⟩ := exists_valuationSubring_of_height_le_one (K := K)
    hinj (m.map (Ideal.Quotient.mk q.asIdeal)) hht π hπ.ne_zero (Ideal.mem_map_of_mem _ hπm)
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp (Ideal.Quotient.mk _),
    hφ, ?_, ?_⟩
  · rw [← Ideal.comap_comap, hφm, hcomap]
  · convert hqU
    ext x
    change φ (Ideal.Quotient.mk _ x) ∈ (⊥ : Ideal O') ↔ _
    rw [Ideal.mem_bot, map_eq_zero_iff φ hφi, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Take `⟨P, hPm, hP, hPO⟩` from `Ideal.exists_ideal_le_liesOver_of_le (R := O) (p := ⊥) (q := m.under O) m bot_le`. Take `⟨p, hp, hpP⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le`. Establish `hpp : p.IsPrime` using `hp.1.1`. Establish `hpO : p.comap (algebraMap O A) ≠ maximalIdeal O` using `fun e => by`. Establish `: p.comap (algebraMap O A) ≤ ⊥` using `(Ideal.comap_mono hpP).trans hPO.over.ge`.

Conclude with `IsDiscreteValuationRing.not_a_field O (e ▸ le_bot_iff.mp this)`. Use `⟨⟨p, hpp⟩, ?_, hpP.trans hPm, hpO⟩` and prove the remaining obligations. Take `⟨s, hsp, hs⟩` from `exists_notMem_forall_mem_minimalPrimes ⊥ p fun Q hQ hle => le_antisymm hle (hp.2 hQ.1 hle)`. Take `⟨x, hxs, hxU⟩` from `mem_closure_iff.mp (hd ⟨p, hpp⟩ hpO) _ (PrimeSpectrum.basicOpen s).isOpen hsp`. Take `⟨Q, hQ, hQx⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le`.

Establish `hQp : Q = p`. Assume the negation of the conclusion as `hne`. Conclude with `hxs (hQx (hs Q hQ hne))`. Substitute `hQp` using the available equality. Conclude with `((PrimeSpectrum.le_iff_specializes ⟨Q, hpp⟩ x).mp hQx).mem_open hU hxU`.
-/
theorem exists_mem_le_of_flat {O A : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing A] [IsNoetherianRing A] [Algebra O A] [Module.Flat O A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ p ∈ U, p.asIdeal ≤ m ∧ p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O := by
  obtain ⟨P, hPm, hP, hPO⟩ := Ideal.exists_ideal_le_liesOver_of_le (R := O) (p := ⊥)
    (q := m.under O) m bot_le
  obtain ⟨p, hp, hpP⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
  have hpp : p.IsPrime := hp.1.1
  have hpO : p.comap (algebraMap O A) ≠ maximalIdeal O := fun e => by
    have : p.comap (algebraMap O A) ≤ ⊥ := (Ideal.comap_mono hpP).trans hPO.over.ge
    exact IsDiscreteValuationRing.not_a_field O (e ▸ le_bot_iff.mp this)
  refine ⟨⟨p, hpp⟩, ?_, hpP.trans hPm, hpO⟩
  obtain ⟨s, hsp, hs⟩ := exists_notMem_forall_mem_minimalPrimes ⊥ p
    fun Q hQ hle => le_antisymm hle (hp.2 hQ.1 hle)
  obtain ⟨x, hxs, hxU⟩ := mem_closure_iff.mp (hd ⟨p, hpp⟩ hpO) _
    (PrimeSpectrum.basicOpen s).isOpen hsp
  obtain ⟨Q, hQ, hQx⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := x.asIdeal) bot_le
  have hQp : Q = p := by
    by_contra hne
    exact hxs (hQx (hs Q hQ hne))
  subst hQp
  exact ((PrimeSpectrum.le_iff_specializes ⟨Q, hpp⟩ x).mp hQx).mem_open hU hxU

/- English proof (translation)
The claim follows from `have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A exists_valuationSubring_lift_of_exists_le m hmO hU (exists_mem_le_of_flat m hU hd)`.
-/
theorem exists_valuationSubring_lift_of_flat {O K : Type*} {A : Type u} [CommRing O]
    [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (m : Ideal A) [m.IsMaximal] (hmO : m.comap (algebraMap O A) = maximalIdeal O)
    {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (hd : ∀ p : PrimeSpectrum A, p.asIdeal.comap (algebraMap O A) ≠ maximalIdeal O →
      p ∈ closure U) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : A →+* O'),
      (∀ a : O, (φ (algebraMap O A a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      (maximalIdeal O').comap φ = m ∧ PrimeSpectrum.comap φ ⊥ ∈ U :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing O A
  exists_valuationSubring_lift_of_exists_le m hmO hU (exists_mem_le_of_flat m hU hd)

end Algebra

section Scheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]

/- English proof (translation)
Use `PrimeSpectrum.ext ?_` and prove the remaining obligations. Establish `ht : t.asIdeal = ⊥` using `@Ideal.eq_bot_of_prime F _ t.asIdeal t.isPrime`. Conclude with `(congrArg (Ideal.comap g) ht).trans (Ideal.comap_bot_of_injective _ hg)`.
-/
theorem specMap_apply_eq_bot {R F : Type u} [CommRing R] [IsDomain R] [Field F] (g : R →+* F)
    (hg : Function.Injective g) (t : Spec (.of F)) :
    Spec.map (CommRingCat.ofHom g) t = (⊥ : PrimeSpectrum R) := by
  refine PrimeSpectrum.ext ?_
  have ht : t.asIdeal = ⊥ := @Ideal.eq_bot_of_prime F _ t.asIdeal t.isPrime
  exact (congrArg (Ideal.comap g) ht).trans (Ideal.comap_bot_of_injective _ hg)

variable (K) in

/- English proof (translation)
Take `⟨A, j, hj, x, rfl⟩` from `Z.exists_Spec_apply_eq z`. Take `⟨ψ, hψ⟩` from `Spec.map_surjective (j ≫ f)`. Establish `hflat : ψ.hom.Flat`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @Flat), hψ]`. Use `infer_instance`.

Establish `hft : ψ.hom.FiniteType`. Rewrite using `[← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]`. Use `infer_instance`. Set `_ : Algebra O A` to `ψ.hom.toAlgebra`. Establish `: Module.Flat O A` using `hflat`.

Establish `: Algebra.FiniteType O A` using `hft`. Establish `hfj : ∀ p : Spec A, (f (j p)).asIdeal = p.asIdeal.comap (algebraMap O A)`. Introduce `p`. Rewrite using `[← Scheme.Hom.comp_apply, ← hψ]`. Both sides reduce to the same expression.

Establish `hx : x.asIdeal.IsMaximal`. Use `hz.preimage j.continuous` as an intermediate fact. Rewrite `this` using `[← Set.image_singleton, Set.preimage_image_eq _ j.isOpenEmbedding.injective]`. Conclude with `(PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) x).mp this`. Establish `hxO : x.asIdeal.comap (algebraMap O A) = maximalIdeal O` using `(hfj x).symm.trans (congrArg PrimeSpectrum.asIdeal hzO)`.

Take `⟨K', _, _, _, O', φ, hφ, hφm, hφW⟩` from `exists_valuationSubring_lift_of_flat (O := O) (K := K) (A := A) x.asIdeal hxO (hW.preimage j.continuous) (fun p hp => by`. Use `hd (j p) fun e => hp ((hfj p).symm.trans (congrArg PrimeSpectrum.asIdeal e))` as an intermediate fact. Conclude with `j.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage this)`. Establish `hcomap : (maximalIdeal O').comap (φ.comp ψ.hom) = maximalIdeal O`. Rewrite using `[← Ideal.comap_comap, hφm]`.

Conclude with `hxO`. Use `⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp ψ.hom, ((local_hom_TFAE _).out 4 0).mp hcomap, Spec.map (CommRingCat.ofHom φ) ≫ j, hφ, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hψ, ← Spec.map_comp]`. Both sides reduce to the same expression. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (congrArg j (PrimeSpectrum.ext hφm))`.

Introduce `t`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, specMap_apply_eq_bot _ (IsFractionRing.injective O' K')]`. Conclude with `hφW`.
-/
theorem exists_valuationSubring_lift_of_isOpen {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f] {W : Set Z} (hW : IsOpen W)
    (hd : ∀ x : Z, f x ≠ closedPoint O → x ∈ closure W)
    {z : Z} (hz : IsClosed ({z} : Set Z)) (hzO : f z = closedPoint O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧ y (closedPoint O') = z ∧
      ∀ t : Spec (.of K'), (Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y) t ∈ W := by
  obtain ⟨A, j, hj, x, rfl⟩ := Z.exists_Spec_apply_eq z
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (j ≫ f)
  have hflat : ψ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hψ]
    infer_instance
  have hft : ψ.hom.FiniteType := by
    rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), hψ]
    infer_instance
  let _ : Algebra O A := ψ.hom.toAlgebra
  have : Module.Flat O A := hflat
  have : Algebra.FiniteType O A := hft
  have hfj : ∀ p : Spec A, (f (j p)).asIdeal = p.asIdeal.comap (algebraMap O A) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← hψ]
    rfl
  have hx : x.asIdeal.IsMaximal := by
    have := hz.preimage j.continuous
    rw [← Set.image_singleton, Set.preimage_image_eq _ j.isOpenEmbedding.injective] at this
    exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal (R := A) x).mp this
  have hxO : x.asIdeal.comap (algebraMap O A) = maximalIdeal O :=
    (hfj x).symm.trans (congrArg PrimeSpectrum.asIdeal hzO)
  obtain ⟨K', _, _, _, O', φ, hφ, hφm, hφW⟩ := exists_valuationSubring_lift_of_flat (O := O) (K := K)
    (A := A) x.asIdeal hxO (hW.preimage j.continuous) (fun p hp => by
      have := hd (j p) fun e => hp ((hfj p).symm.trans (congrArg PrimeSpectrum.asIdeal e))
      exact j.isOpenEmbedding.isOpenMap.preimage_closure_subset_closure_preimage this)
  have hcomap : (maximalIdeal O').comap (φ.comp ψ.hom) = maximalIdeal O := by
    rw [← Ideal.comap_comap, hφm]
    exact hxO
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', φ.comp ψ.hom,
    ((local_hom_TFAE _).out 4 0).mp hcomap, Spec.map (CommRingCat.ofHom φ) ≫ j, hφ, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← hψ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg j (PrimeSpectrum.ext hφm))
  · intro t
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
      specMap_apply_eq_bot _ (IsFractionRing.injective O' K')]
    exact hφW

/- English proof (translation)
Establish `hbot` using `specMap_apply_eq_bot _ (IsFractionRing.injective O K)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, rfl⟩ e`. Rewrite `e` using `[hbot]`.

Conclude with `IsDiscreteValuationRing.not_a_field O (congrArg PrimeSpectrum.asIdeal e).symm`. Introduce `hx`. Use `⟨closedPoint K, (hbot _).trans ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h0 : x.asIdeal ≠ ⊥` using `fun e => hne (PrimeSpectrum.ext e.symm)`.

Conclude with `hx (PrimeSpectrum.ext (eq_maximalIdeal (x.isPrime.isMaximal h0)))`.
-/
theorem range_specMap_fractionField :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap O K))) =
      {x : Spec (.of O) | x ≠ closedPoint O} := by
  have hbot := specMap_apply_eq_bot _ (IsFractionRing.injective O K)
  ext x
  constructor
  · rintro ⟨t, rfl⟩ e
    rw [hbot] at e
    exact IsDiscreteValuationRing.not_a_field O (congrArg PrimeSpectrum.asIdeal e).symm
  · intro hx
    refine ⟨closedPoint K, (hbot _).trans ?_⟩
    by_contra hne
    have h0 : x.asIdeal ≠ ⊥ := fun e => hne (PrimeSpectrum.ext e.symm)
    exact hx (PrimeSpectrum.ext (eq_maximalIdeal (x.isPrime.isMaximal h0)))

/- English proof (translation)
Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `: IsLocalization.Away π K`. Use `IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_) (fun a b hab => ⟨0, by simpa using IsFractionRing.injective O K hab⟩)` and prove the remaining obligations. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) s`. Take `⟨n, v, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ`.

Use `⟨n, a * (v⁻¹ : Oˣ), ?_⟩` and prove the remaining obligations. Establish `h1 : algebraMap O K π ≠ 0` using `by simpa using hπ.ne_zero`. Establish `h2 : algebraMap O K v ≠ 0` using `by simp`. Simplify using `only [map_mul, map_pow, map_units_inv]`. Clear the denominators using the available nonvanishing facts.

Conclude with `IsOpenImmersion.of_isLocalization π`.
-/
theorem isOpenImmersion_specMap_fractionField :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have : IsLocalization.Away π K := by
    refine IsLocalization.Away.mk π (IsUnit.mk0 _ (by simpa using hπ.ne_zero)) (fun s => ?_)
      (fun a b hab => ⟨0, by simpa using IsFractionRing.injective O K hab⟩)
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) s
    obtain ⟨n, v, rfl⟩ :=
      IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨n, a * (v⁻¹ : Oˣ), ?_⟩
    have h1 : algebraMap O K π ≠ 0 := by simpa using hπ.ne_zero
    have h2 : algebraMap O K v ≠ 0 := by simp
    simp only [map_mul, map_pow, map_units_inv]
    field_simp
  exact IsOpenImmersion.of_isLocalization π

/- English proof (translation)
Use `isOpenImmersion_specMap_fractionField (O := O) (K := K)` as an intermediate fact. Establish `hemb` using `(pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K)))).isOpenEmbedding`. Take `⟨K', _, _, _, O', h, _, y, hh, hy, hyz, hyW⟩` from `exists_valuationSubring_lift_of_isOpen K f (hemb.isOpenMap U hU) (fun x hx => by`. Establish `: x ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K))))`. Rewrite using `[Scheme.Pullback.range_fst, Set.mem_preimage, range_specMap_fractionField]`.

Conclude with `hx`. Take `⟨x, rfl⟩` from `this`. Conclude with `image_closure_subset_closure_image hemb.continuous ⟨x, hd x, rfl⟩) hz hzO`. Establish `hcomm : (Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y) ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ Spec.map (CommRingCat.ofHom (algebraMap O K))`. Rewrite using `[Category.assoc, hy, ← Spec.map_comp, ← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `a`. Conclude with `hh a`. Use `⟨K', inferInstance, inferInstance, inferInstance, O', h, inferInstance, y, pullback.lift _ _ hcomm, hh, hy, hyz, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, fun t => ?_⟩` and prove the remaining obligations. Take `⟨x, hxU, hx⟩` from `hyW t`.

Rewrite `hx` using `[← pullback.lift_fst _ _ hcomm, Scheme.Hom.comp_apply]`. Conclude with `hemb.injective hx ▸ hxU`.
-/
theorem exists_valuationSubring_lift {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K))))}
    (hU : IsOpen U) (hd : Dense U)
    {z : Z} (hz : IsClosed ({z} : Set Z)) (hzO : f z = closedPoint O) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧ y (closedPoint O') = z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by
  have := isOpenImmersion_specMap_fractionField (O := O) (K := K)
  have hemb := (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K)))).isOpenEmbedding
  obtain ⟨K', _, _, _, O', h, _, y, hh, hy, hyz, hyW⟩ :=
    exists_valuationSubring_lift_of_isOpen K f (hemb.isOpenMap U hU) (fun x hx => by
      have : x ∈ Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap O K)))) := by
        rw [Scheme.Pullback.range_fst, Set.mem_preimage, range_specMap_fractionField]
        exact hx
      obtain ⟨x, rfl⟩ := this
      exact image_closure_subset_closure_image hemb.continuous ⟨x, hd x, rfl⟩) hz hzO
  have hcomm : (Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap O K)) := by
    rw [Category.assoc, hy, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact hh a
  refine ⟨K', inferInstance, inferInstance, inferInstance, O', h, inferInstance, y,
    pullback.lift _ _ hcomm, hh, hy, hyz, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    fun t => ?_⟩
  obtain ⟨x, hxU, hx⟩ := hyW t
  rw [← pullback.lift_fst _ _ hcomm, Scheme.Hom.comp_apply] at hx
  exact hemb.injective hx ▸ hxU

/- English proof (translation)
Establish `: IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O)))` using `IsClosedImmersion.spec_of_surjective _ residue_surjective`. Use `exists_valuationSubring_lift f hU hd ?_ ?_` and prove the remaining obligations. Rewrite using `[← Set.image_singleton]`. Conclude with `(pullback.fst f (Spec.map (CommRingCat.ofHom (residue O)))).isClosedEmbedding.isClosedMap _ hz`. Rewrite using `[← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]`.

Conclude with `PrimeSpectrum.comap_residue O _`.
-/
theorem exists_valuationSubring_lift_of_specialFibre {Z : Scheme.{u}} (f : Z ⟶ Spec (.of O))
    [Flat f] [LocallyOfFiniteType f]
    {U : Set ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K))))}
    (hU : IsOpen U) (hd : Dense U)
    {z : ↥(pullback f (Spec.map (CommRingCat.ofHom (residue O))))}
    (hz : IsClosed ({z} : Set _)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (h : O →+* O') (_ : IsLocalHom h)
      (y : Spec (.of O') ⟶ Z)
      (y' : Spec (.of K') ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap O K)))),
      (∀ a : O, (h a : K') = algebraMap K K' (algebraMap O K a)) ∧
      y ≫ f = Spec.map (CommRingCat.ofHom h) ∧
      y (closedPoint O') = pullback.fst f (Spec.map (CommRingCat.ofHom (residue O))) z ∧
      y' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap O' K')) ≫ y ∧
      y' ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap K K')) ∧
      ∀ t, y' t ∈ U := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (residue O))) :=
    IsClosedImmersion.spec_of_surjective _ residue_surjective
  refine exists_valuationSubring_lift f hU hd ?_ ?_
  · rw [← Set.image_singleton]
    exact (pullback.fst f (Spec.map (CommRingCat.ofHom (residue O)))).isClosedEmbedding.isClosedMap
      _ hz
  · rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact PrimeSpectrum.comap_residue O _

end Scheme

end GlobalTheory
