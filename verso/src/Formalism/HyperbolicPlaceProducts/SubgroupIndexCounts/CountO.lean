import Formalism.HyperbolicPlaceProducts.Statement

open Module NumberField

noncomputable section

namespace Formalism.SLP.P

namespace CountO

/- English proof (translation)
Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Establish `hne : Ideal.span {(p : ℤ)} ≠ ⊥`. Simplify using `[hp.ne_zero]`. Use `⟨IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 E), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hne`.

Introduce `P hP hpP`. Rewrite using `[IsDedekindDomain.mem_primesOverFinset_iff hne]`. Use `⟨hP.isPrime, ⟨?_⟩⟩` and prove the remaining obligations. Use `Ideal.IsMaximal.eq_of_le hmax ?_ ?_` and prove the remaining obligations. Conclude with `(Ideal.comap_ne_top _ hP.ne_top)`.

Rewrite using `[Ideal.span_le]`. Simplify using `using hpP`.
-/
theorem primes_card (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p.Prime) :
    ∃ Ps : Finset (Ideal (𝓞 E)), Ps.card ≤ finrank ℚ E ∧
      ∀ P : Ideal (𝓞 E), P.IsMaximal → ((p : ℕ) : 𝓞 E) ∈ P → P ∈ Ps := by
  classical
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  have hne : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    simp [hp.ne_zero]
  refine ⟨IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 E), ?_, ?_⟩
  · exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E hne
  · intro P hP hpP
    rw [IsDedekindDomain.mem_primesOverFinset_iff hne]
    refine ⟨hP.isPrime, ⟨?_⟩⟩
    refine Ideal.IsMaximal.eq_of_le hmax ?_ ?_
    · exact (Ideal.comap_ne_top _ hP.ne_top)
    · rw [Ideal.span_le]
      simpa using hpP

section DedekindLFunctions

variable {R : Type} [CommRing R] [IsDedekindDomain R]

/- English proof (translation)
Set `Rp` to `Localization.AtPrime P`. Establish `: IsDiscreteValuationRing Rp` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP Rp`. Establish `hinj : Function.Injective (algebraMap R Rp)` using `IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors`. Set `f : ι → ℕ∞` to `fun i => IsDiscreteValuationRing.addVal Rp (algebraMap R Rp (c i))`. Take `⟨j, hj, hjc⟩` from `hc`.

Take `⟨i0, hi0, hmin⟩` from `Finset.exists_min_image t f ⟨j, hj⟩`. Establish `hi0ne : c i0 ≠ 0`. Introduce `h0`. Establish `h1 : f i0 = ⊤` using `by simp [f, h0]`. Establish `h2 : f j ≠ ⊤`.

Simplify using `only [f, ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `(map_ne_zero_iff _ hinj).mpr hjc`. Conclude with `h2 (top_le_iff.mp (h1 ▸ hmin j hj))`. Establish `hdvd : ∀ i ∈ t, algebraMap R Rp (c i0) ∣ algebraMap R Rp (c i)` using `fun i hi => (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin i hi)`. Use `choose! w hw using hdvd`.

Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples P.primeCompl t w`. Establish `hb' : ∀ i ∈ t, ∃ r : R, algebraMap R Rp r = (b : R) • w i` using `fun i hi => RingHom.mem_rangeS.mp (hb i hi)`. Use `choose! d hd using hb'`. Use `⟨i0, hi0, hi0ne, (b : R), b.2, d, fun i hi => ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul, hd i hi, hw i hi, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_local_min (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {ι : Type} (t : Finset ι)
    (c : ι → R) (hc : ∃ i ∈ t, c i ≠ 0) :
    ∃ i0 ∈ t, c i0 ≠ 0 ∧ ∃ s : R, s ∉ P ∧ ∃ d : ι → R, ∀ i ∈ t, s * c i = c i0 * d i := by
  classical
  let Rp := Localization.AtPrime P
  have : IsDiscreteValuationRing Rp :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP Rp
  have hinj : Function.Injective (algebraMap R Rp) :=
    IsLocalization.injective Rp P.primeCompl_le_nonZeroDivisors
  let f : ι → ℕ∞ := fun i => IsDiscreteValuationRing.addVal Rp (algebraMap R Rp (c i))
  obtain ⟨j, hj, hjc⟩ := hc
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image t f ⟨j, hj⟩
  have hi0ne : c i0 ≠ 0 := by
    intro h0
    have h1 : f i0 = ⊤ := by simp [f, h0]
    have h2 : f j ≠ ⊤ := by
      simp only [f, ne_eq, IsDiscreteValuationRing.addVal_eq_top_iff]
      exact (map_ne_zero_iff _ hinj).mpr hjc
    exact h2 (top_le_iff.mp (h1 ▸ hmin j hj))
  have hdvd : ∀ i ∈ t, algebraMap R Rp (c i0) ∣ algebraMap R Rp (c i) := fun i hi =>
    (IsDiscreteValuationRing.addVal_le_iff_dvd).mp (hmin i hi)
  choose! w hw using hdvd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples P.primeCompl t w
  have hb' : ∀ i ∈ t, ∃ r : R, algebraMap R Rp r = (b : R) • w i :=
    fun i hi => RingHom.mem_rangeS.mp (hb i hi)
  choose! d hd using hb'
  refine ⟨i0, hi0, hi0ne, (b : R), b.2, d, fun i hi => ?_⟩
  apply hinj
  rw [map_mul, map_mul, hd i hi, hw i hi, Algebra.smul_def]
  ring

/- English proof (translation)
Take `⟨i0, hi0, hne0, s, hs, d, hd⟩` from `exists_local_min P hP t g hne`. Use `⟨i0, hi0, d, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : s * g i0 = g i0 * d i0` using `hd i0 hi0`. Establish `h2 : d i0 = s`. Apply `mul_left_cancel₀ hne0` to reduce the goal to its premises.

Rewrite using `[← h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Conclude with `hs`. Apply `htf (g i0) hne0` to reduce the goal to its premises.

Rewrite using `[Finset.smul_sum]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, hd i hi]`. Use `_ = s • ∑ i ∈ t, g i • v i := by rw [Finset.smul_sum]`.

Use `_ = 0 := by rw [hg, smul_zero]`.
-/
theorem exists_rel_not_mem {X : Type} [AddCommGroup X] [Module R X]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0)
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) {ι : Type} (t : Finset ι) (v : ι → X)
    (g : ι → R) (hg : ∑ i ∈ t, g i • v i = 0) (hne : ∃ i ∈ t, g i ≠ 0) :
    ∃ i0 ∈ t, ∃ d : ι → R, d i0 ∉ P ∧ ∑ i ∈ t, d i • v i = 0 := by
  obtain ⟨i0, hi0, hne0, s, hs, d, hd⟩ := exists_local_min P hP t g hne
  refine ⟨i0, hi0, d, ?_, ?_⟩
  · have h1 : s * g i0 = g i0 * d i0 := hd i0 hi0
    have h2 : d i0 = s := by
      apply mul_left_cancel₀ hne0
      rw [← h1]; ring
    rw [h2]; exact hs
  · apply htf (g i0) hne0
    rw [Finset.smul_sum]
    calc ∑ i ∈ t, g i0 • d i • v i = ∑ i ∈ t, s • g i • v i := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [smul_smul, smul_smul, hd i hi]
      _ = s • ∑ i ∈ t, g i • v i := by rw [Finset.smul_sum]
      _ = 0 := by rw [hg, smul_zero]

/- English proof (translation)
Establish `hex : ∃ n, ∃ s : Finset X, s.card = n ∧ Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤`. Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := R) (M := X)`. Conclude with `⟨s.card, s, rfl, by rw [hs, top_sup_eq]⟩`. Take `⟨s, hsc, hs⟩` from `Nat.find_spec hex`. Use `⟨s, ?_, hs⟩` and prove the remaining obligations.

Rewrite using `[hsc]`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hnli : ¬ LinearIndependent R (fun x : s => (x : X))` using `fun h => by`. Use `hli s _ h` as an intermediate fact.

Rewrite `this` using `[Fintype.card_coe]`. Use linear arithmetic over natural numbers and integers. Rewrite `hnli` using `[linearIndependent_iff']`. Use `push Not at hnli`. Take `⟨t, g, hg, i, hit, hgi⟩` from `hnli`.

Take `⟨i0, hi0, d, hd0, hd⟩` from `exists_rel_not_mem htf P hP t (fun x : s => (x : X)) g hg ⟨i, hit, hgi⟩`. Use `set s' := s.erase (i0 : X) with hs'def`. Establish `hmem : (i0 : X) ∈ Submodule.span R (s' : Set X) ⊔ P • ⊤`. Take `⟨a, b, hb, hab⟩` from `Ideal.IsMaximal.exists_inv hPm hd0`. Establish `h1 : d i0 • (i0 : X) ∈ Submodule.span R (s' : Set X)`.

Establish `h2 : d i0 • (i0 : X) = - ∑ i ∈ t.erase i0, d i • (i : X)`. Rewrite `hd` using `[← Finset.add_sum_erase t _ hi0]`. Conclude with `eq_neg_of_add_eq_zero_left hd`. Rewrite using `[h2]`. Use `Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (Submodule.subset_span ?_))` and prove the remaining obligations.

Establish `hne : i ≠ i0` using `Finset.ne_of_mem_erase hi`. Simplify using `only [s', Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]`. Conclude with `⟨i.2, fun h => hne (Subtype.ext h)⟩`. Establish `h3 : (i0 : X) = a • (d i0 • (i0 : X)) + b • (i0 : X)`. Rewrite using `[smul_smul, ← add_smul, hab, one_smul]`.

Rewrite using `[h3]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ h1)) (Submodule.mem_sup_right (Submodule.smul_mem_smul hb Submodule.mem_top))`. Establish `hs' : Submodule.span R (s' : Set X) ⊔ P • ⊤ = ⊤`. Rewrite using `[eq_top_iff]`. Use `le_trans hs.ge (sup_le ?_ le_sup_right)` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Distinguish the cases in `hx0 : x = (i0 : X)`. Rewrite using `[hx0]`. Conclude with `hmem`.

Conclude with `Submodule.mem_sup_left (Submodule.subset_span (by simp [s', hx0, hx]))`. Establish `hcard : s'.card < Nat.find hex`. Rewrite using `[← hsc, hs'def, Finset.card_erase_of_mem i0.2]`. Establish `: 0 < s.card` using `Finset.card_pos.mpr ⟨i0, i0.2⟩`. Use linear arithmetic over natural numbers and integers.

Conclude with `Nat.find_min hex hcard ⟨s', rfl, hs'⟩`.
-/
theorem exists_gen_mod (P : Ideal R) [hPm : P.IsMaximal] (hP : P ≠ ⊥) {X : Type}
    [AddCommGroup X] [Module R X] [Module.Finite R X]
    (htf : ∀ a : R, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0) (k : ℕ)
    (hli : ∀ (ι : Type) [Fintype ι] (v : ι → X), LinearIndependent R v → Fintype.card ι ≤ k) :
    ∃ s : Finset X, s.card ≤ k ∧ Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤ := by
  classical
  have hex : ∃ n, ∃ s : Finset X, s.card = n ∧ Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤ := by
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := X)
    exact ⟨s.card, s, rfl, by rw [hs, top_sup_eq]⟩
  obtain ⟨s, hsc, hs⟩ := Nat.find_spec hex
  refine ⟨s, ?_, hs⟩
  rw [hsc]
  by_contra hlt
  push Not at hlt
  have hnli : ¬ LinearIndependent R (fun x : s => (x : X)) := fun h => by
    have := hli s _ h
    rw [Fintype.card_coe] at this
    omega
  rw [linearIndependent_iff'] at hnli
  push Not at hnli
  obtain ⟨t, g, hg, i, hit, hgi⟩ := hnli
  obtain ⟨i0, hi0, d, hd0, hd⟩ :=
    exists_rel_not_mem htf P hP t (fun x : s => (x : X)) g hg ⟨i, hit, hgi⟩
  set s' := s.erase (i0 : X) with hs'def
  have hmem : (i0 : X) ∈ Submodule.span R (s' : Set X) ⊔ P • ⊤ := by
    obtain ⟨a, b, hb, hab⟩ := Ideal.IsMaximal.exists_inv hPm hd0
    have h1 : d i0 • (i0 : X) ∈ Submodule.span R (s' : Set X) := by
      have h2 : d i0 • (i0 : X) = - ∑ i ∈ t.erase i0, d i • (i : X) := by
        rw [← Finset.add_sum_erase t _ hi0] at hd
        exact eq_neg_of_add_eq_zero_left hd
      rw [h2]
      refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
      simp only [s', Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
      exact ⟨i.2, fun h => hne (Subtype.ext h)⟩
    have h3 : (i0 : X) = a • (d i0 • (i0 : X)) + b • (i0 : X) := by
      rw [smul_smul, ← add_smul, hab, one_smul]
    rw [h3]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ h1))
      (Submodule.mem_sup_right (Submodule.smul_mem_smul hb Submodule.mem_top))
  have hs' : Submodule.span R (s' : Set X) ⊔ P • ⊤ = ⊤ := by
    rw [eq_top_iff]
    refine le_trans hs.ge (sup_le ?_ le_sup_right)
    rw [Submodule.span_le]
    intro x hx
    by_cases hx0 : x = (i0 : X)
    · rw [hx0]; exact hmem
    · exact Submodule.mem_sup_left (Submodule.subset_span (by simp [s', hx0, hx]))
  have hcard : s'.card < Nat.find hex := by
    rw [← hsc, hs'def, Finset.card_erase_of_mem i0.2]
    have : 0 < s.card := Finset.card_pos.mpr ⟨i0, i0.2⟩
    omega
  exact Nat.find_min hex hcard ⟨s', rfl, hs'⟩

/- English proof (translation)
Set `F : (X →ₗ[R] R ⧸ P) → (s → R ⧸ P)` to `fun φ x => φ x`. Establish `hF : Function.Injective F`. Introduce `φ₁ φ₂ h`. Establish `hle : Submodule.span R (s : Set X) ⊔ P • ⊤ ≤ LinearMap.ker (φ₁ - φ₂)`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce `x hx`. Use `congrFun h ⟨x, hx⟩` as an intermediate fact. Simplify using `only [F] at this`. Simplify using `[this]`.

Use `Submodule.smul_le.mpr fun r hr n _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]`. Rewrite `hle` using `[hs, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero]`. Conclude with `hle`. Establish `: Finite (X →ₗ[R] R ⧸ P)` using `Finite.of_injective F hF`.

Use `⟨this, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem card_hom_le (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (k : ℕ) (s : Finset X) (hsk : s.card ≤ k)
    (hs : Submodule.span R (s : Set X) ⊔ P • ⊤ = ⊤) :
    Finite (X →ₗ[R] R ⧸ P) ∧ Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (R ⧸ P) ^ k := by
  classical
  let F : (X →ₗ[R] R ⧸ P) → (s → R ⧸ P) := fun φ x => φ x
  have hF : Function.Injective F := by
    intro φ₁ φ₂ h
    have hle : Submodule.span R (s : Set X) ⊔ P • ⊤ ≤ LinearMap.ker (φ₁ - φ₂) := by
      refine sup_le ?_ ?_
      · rw [Submodule.span_le]
        intro x hx
        have := congrFun h ⟨x, hx⟩
        simp only [F] at this
        simp [this]
      · refine Submodule.smul_le.mpr fun r hr n _ => ?_
        rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
    rw [hs, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at hle
    exact hle
  have : Finite (X →ₗ[R] R ⧸ P) := Finite.of_injective F hF
  refine ⟨this, ?_⟩
  calc Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (s → R ⧸ P) := Nat.card_le_card_of_injective F hF
    _ = Nat.card (R ⧸ P) ^ s.card := by rw [Nat.card_fun]; simp
    _ ≤ Nat.card (R ⧸ P) ^ k := Nat.pow_le_pow_right Nat.card_pos hsk

end DedekindLFunctions

section DedekindLFunctions

variable {R : Type} [CommRing R] [IsDedekindDomain R]

/- English proof (translation)
Establish `hcardQ : Nat.card (X ⧸ L) = Nat.card (R ⧸ P)` using `hL`. Establish `: Nontrivial (R ⧸ P)` using `Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top`. Establish `hfin : Finite (X ⧸ L)` using `Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact Nat.card_pos.ne')`. Establish `hnt : Nontrivial (X ⧸ L)`. Rewrite using `[← Finite.one_lt_card_iff_nontrivial, hcardQ]`.

Conclude with `Finite.one_lt_card`. Take `⟨v, hv⟩` from `exists_ne (0 : X ⧸ L)`. Set `τ : R →ₗ[R] X ⧸ L` to `LinearMap.toSpanSingleton R (X ⧸ L) v`. Establish `hker : P ≤ LinearMap.ker τ`. Introduce `a ha`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective L v`. Simplify using `only [LinearMap.mem_ker, τ, LinearMap.toSpanSingleton_apply]`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hPL (Submodule.smul_mem_smul ha Submodule.mem_top)`. Set `τ' : R ⧸ P →ₗ[R] X ⧸ L` to `Submodule.liftQ P τ hker`.

Establish `hinj : Function.Injective τ'`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `z hz`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective P z`. Rewrite `hz` using `[LinearMap.mem_ker]`.

Establish `hz' : a • v = 0` using `hz`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Assume the negation of the conclusion as `ha`. Take `⟨b, i, hi, hbi⟩` from `Ideal.IsMaximal.exists_inv hPm ha`. Establish `hiv : i • v = 0` using `hker hi`.

Apply `hv` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hbij : Function.Bijective τ'` using `hinj.bijective_of_nat_card_le (by rw [hcardQ])`. Set `e` to `LinearEquiv.ofBijective τ' hbij`. Use `⟨e.symm.toLinearMap ∘ₗ L.mkQ, ?_⟩` and prove the remaining obligations.

Rewrite using `[LinearEquiv.ker_comp, Submodule.ker_mkQ]`.
-/
theorem exists_hom_ker (P : Ideal R) [hPm : P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (L : Submodule R X) (hPL : P • ⊤ ≤ L)
    (hL : L.toAddSubgroup.index = Nat.card (R ⧸ P)) :
    ∃ φ : X →ₗ[R] R ⧸ P, LinearMap.ker φ = L := by
  classical
  have hcardQ : Nat.card (X ⧸ L) = Nat.card (R ⧸ P) := hL
  have : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top
  have hfin : Finite (X ⧸ L) :=
    Nat.finite_of_card_ne_zero (by rw [hcardQ]; exact Nat.card_pos.ne')
  have hnt : Nontrivial (X ⧸ L) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardQ]
    exact Finite.one_lt_card
  obtain ⟨v, hv⟩ := exists_ne (0 : X ⧸ L)
  let τ : R →ₗ[R] X ⧸ L := LinearMap.toSpanSingleton R (X ⧸ L) v
  have hker : P ≤ LinearMap.ker τ := by
    intro a ha
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective L v
    simp only [LinearMap.mem_ker, τ, LinearMap.toSpanSingleton_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hPL (Submodule.smul_mem_smul ha Submodule.mem_top)
  let τ' : R ⧸ P →ₗ[R] X ⧸ L := Submodule.liftQ P τ hker
  have hinj : Function.Injective τ' := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective P z
    rw [LinearMap.mem_ker] at hz
    have hz' : a • v = 0 := hz
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    by_contra ha
    obtain ⟨b, i, hi, hbi⟩ := Ideal.IsMaximal.exists_inv hPm ha
    have hiv : i • v = 0 := hker hi
    apply hv
    calc v = (b * a + i) • v := by rw [hbi, one_smul]
      _ = b • (a • v) + i • v := by rw [add_smul, mul_smul]
      _ = 0 := by rw [hz', hiv, smul_zero, add_zero]
  have hbij : Function.Bijective τ' :=
    hinj.bijective_of_nat_card_le (by rw [hcardQ])
  let e := LinearEquiv.ofBijective τ' hbij
  refine ⟨e.symm.toLinearMap ∘ₗ L.mkQ, ?_⟩
  rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

def hyp (P : Ideal R) (X : Type) [AddCommGroup X] [Module R X] : Set (Submodule R X) :=
  {L | P • ⊤ ≤ L ∧ L.toAddSubgroup.index = Nat.card (R ⧸ P)}

/- English proof (translation)
Take `⟨hfin, hcard⟩` from `hhom`. Set `F : Submodule R X → (X →ₗ[R] R ⧸ P)` to `fun L => if h : L ∈ hyp P X then Classical.choose (exists_hom_ker P L h.1 h.2) else 0`. Establish `hF : ∀ L ∈ hyp P X, LinearMap.ker (F L) = L`. Introduce `L hL`. Simplify using `only [F, dif_pos hL]`.

Conclude with `Classical.choose_spec (exists_hom_ker P L hL.1 hL.2)`. Establish `hinj : Set.InjOn F (hyp P X)`. Introduce `L₁ h₁ L₂ h₂ h`. Rewrite using `[← hF L₁ h₁, ← hF L₂ h₂, h]`. Establish `hfinS : (hyp P X).Finite` using `Set.Finite.of_finite_image (Set.toFinite _) hinj`.

Use `⟨hfinS, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem hyp_count (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)] {X : Type}
    [AddCommGroup X] [Module R X] (k : ℕ)
    (hhom : Finite (X →ₗ[R] R ⧸ P) ∧ Nat.card (X →ₗ[R] R ⧸ P) ≤ Nat.card (R ⧸ P) ^ k) :
    (hyp P X).Finite ∧ (hyp P X).ncard ≤ Nat.card (R ⧸ P) ^ k := by
  classical
  obtain ⟨hfin, hcard⟩ := hhom
  let F : Submodule R X → (X →ₗ[R] R ⧸ P) := fun L =>
    if h : L ∈ hyp P X then Classical.choose (exists_hom_ker P L h.1 h.2) else 0
  have hF : ∀ L ∈ hyp P X, LinearMap.ker (F L) = L := by
    intro L hL
    simp only [F, dif_pos hL]
    exact Classical.choose_spec (exists_hom_ker P L hL.1 hL.2)
  have hinj : Set.InjOn F (hyp P X) := by
    intro L₁ h₁ L₂ h₂ h
    rw [← hF L₁ h₁, ← hF L₂ h₂, h]
  have hfinS : (hyp P X).Finite := Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfinS, ?_⟩
  calc (hyp P X).ncard ≤ (Set.univ : Set (X →ₗ[R] R ⧸ P)).ncard :=
        Set.ncard_le_ncard_of_injOn F (fun _ _ => Set.mem_univ _) hinj (Set.toFinite _)
    _ = Nat.card (X →ₗ[R] R ⧸ P) := Set.ncard_univ _
    _ ≤ _ := hcard

/- English proof (translation)
Take `⟨L, hL, hNL⟩` from `(eq_top_or_exists_le_coatom N).resolve_left hN`. Establish `hs : IsSimpleModule R (X ⧸ L)` using `isSimpleModule_iff_isCoatom.mpr hL`. Take `⟨P, hPm, ⟨e⟩⟩` from `isSimpleModule_iff_quot_maximal.mp hs`. Use `⟨P, hPm, L, ⟨?_, ?_⟩, hNL⟩` and prove the remaining obligations. Use `Submodule.smul_le.mpr fun r hr n _ => ?_` and prove the remaining obligations.

Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← e.map_eq_zero_iff, Submodule.Quotient.mk_smul, map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]`. Conclude with `Nat.card_congr e.toEquiv`.
-/
theorem exists_hyp_above {X : Type} [AddCommGroup X] [Module R X] [Module.Finite R X]
    (N : Submodule R X) (hN : N ≠ ⊤) :
    ∃ P : Ideal R, P.IsMaximal ∧ ∃ L ∈ hyp P X, N ≤ L := by
  obtain ⟨L, hL, hNL⟩ := (eq_top_or_exists_le_coatom N).resolve_left hN
  have hs : IsSimpleModule R (X ⧸ L) := isSimpleModule_iff_isCoatom.mpr hL
  obtain ⟨P, hPm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hs
  refine ⟨P, hPm, L, ⟨?_, ?_⟩, hNL⟩
  · refine Submodule.smul_le.mpr fun r hr n _ => ?_
    rw [← Submodule.Quotient.mk_eq_zero, ← e.map_eq_zero_iff, Submodule.Quotient.mk_smul,
      map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_mul]
  · exact Nat.card_congr e.toEquiv

end DedekindLFunctions

section Mul

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

def idxSet (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (m : ℕ) :
    Set (Submodule R X) :=
  {N | N.toAddSubgroup.index = m}

def mulSub (R X : Type) [CommRing R] [AddCommGroup X] [Module R X] (c : ℕ) : Submodule R X :=
  LinearMap.range (c • (LinearMap.id : X →ₗ[R] X))

/- English proof (translation)
Assemble the required witnesses or components as `⟨x, by simp⟩`.
-/
theorem nsmul_mem_mulSub (c : ℕ) (x : X) : c • x ∈ mulSub R X c := ⟨x, by simp⟩

/- English proof (translation)
Take `⟨w, rfl⟩` from `hy`. Conclude with `⟨w, by simp⟩`.
-/
theorem mem_mulSub {c : ℕ} {y : X} (hy : y ∈ mulSub R X c) : ∃ w : X, y = c • w := by
  obtain ⟨w, rfl⟩ := hy
  exact ⟨w, by simp⟩

/- English proof (translation)
Use `set K := N ⊔ mulSub R X a with hK`. Establish `hle : N.toAddSubgroup ≤ K.toAddSubgroup` using `Submodule.toAddSubgroup_mono le_sup_left`. Establish `hdvd : K.toAddSubgroup.index ∣ a * b` using `hN ▸ AddSubgroup.index_dvd_of_le hle`. Establish `hne : K.toAddSubgroup.index ≠ 0` using `fun h => (Nat.mul_pos ha hb).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))`. Establish `hcop : Nat.Coprime K.toAddSubgroup.index b`.

Apply `Nat.coprime_of_dvd` to reduce the goal to its premises. Introduce `q hq hqK hqb`. Establish `: Fact q.Prime` using `⟨hq⟩`. Establish `: Finite (X ⧸ K.toAddSubgroup)` using `Nat.finite_of_card_ne_zero hne`. Take `⟨z, hz⟩` from `exists_prime_addOrderOf_dvd_card' (G := X ⧸ K.toAddSubgroup) q hqK`.

Take `⟨x, rfl⟩` from `QuotientAddGroup.mk_surjective z`. Establish `hax : a • (x : X ⧸ K.toAddSubgroup) = 0`. Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `Submodule.mem_sup_right (nsmul_mem_mulSub a x)`. Establish `hqa : q ∣ a` using `hz ▸ addOrderOf_dvd_of_nsmul_eq_zero hax`.

Establish `h1 : q ∣ Nat.gcd a b` using `Nat.dvd_gcd hqa hqb`. Rewrite `h1` using `[hab.gcd_eq_one, Nat.dvd_one]`. Conclude with `hq.one_lt.ne' h1`. Conclude with `hcop.dvd_of_dvd_mul_right hdvd`.
-/
theorem index_sup_mulSub_dvd (N : Submodule R X) {a b : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) (hN : N.toAddSubgroup.index = a * b) :
    (N ⊔ mulSub R X a).toAddSubgroup.index ∣ a := by
  set K := N ⊔ mulSub R X a with hK
  have hle : N.toAddSubgroup ≤ K.toAddSubgroup := Submodule.toAddSubgroup_mono le_sup_left
  have hdvd : K.toAddSubgroup.index ∣ a * b := hN ▸ AddSubgroup.index_dvd_of_le hle
  have hne : K.toAddSubgroup.index ≠ 0 :=
    fun h => (Nat.mul_pos ha hb).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have hcop : Nat.Coprime K.toAddSubgroup.index b := by
    apply Nat.coprime_of_dvd
    intro q hq hqK hqb
    have : Fact q.Prime := ⟨hq⟩
    have : Finite (X ⧸ K.toAddSubgroup) := Nat.finite_of_card_ne_zero hne
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := X ⧸ K.toAddSubgroup) q hqK
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hax : a • (x : X ⧸ K.toAddSubgroup) = 0 := by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact Submodule.mem_sup_right (nsmul_mem_mulSub a x)
    have hqa : q ∣ a := hz ▸ addOrderOf_dvd_of_nsmul_eq_zero hax
    have h1 : q ∣ Nat.gcd a b := Nat.dvd_gcd hqa hqb
    rw [hab.gcd_eq_one, Nat.dvd_one] at h1
    exact hq.one_lt.ne' h1
  exact hcop.dvd_of_dvd_mul_right hdvd

/- English proof (translation)
Establish `hkill : ∀ w : X, (a * b) • w ∈ N` using `fun w => by`. Use `AddSubgroup.nsmul_index_mem N.toAddSubgroup w` as an intermediate fact. Rewrite `this` using `[hN]`. Conclude with `this`. Use `le_antisymm ?_ (le_inf le_sup_left le_sup_left)` and prove the remaining obligations.

Introduce and unpack `x ⟨hx1, hx2⟩`. Take `⟨y1, hy1, z1, hz1, rfl⟩` from `Submodule.mem_sup.mp hx1`. Take `⟨y2, hy2, z2, hz2, h2⟩` from `Submodule.mem_sup.mp hx2`. Take `⟨w1, rfl⟩` from `mem_mulSub hz1`. Take `⟨w2, rfl⟩` from `mem_mulSub hz2`.

Use `set x := y1 + a • w1 with hxdef`. Establish `hbx : b • x ∈ N`. Rewrite using `[hxdef, smul_add, smul_smul, mul_comm b a]`. Conclude with `N.add_mem (N.toAddSubgroup.nsmul_mem hy1 b) (hkill w1)`. Establish `hax : a • x ∈ N`.

Rewrite using `[← h2, smul_add, smul_smul]`. Conclude with `N.add_mem (N.toAddSubgroup.nsmul_mem hy2 a) (hkill w2)`. Establish `h` using `Nat.gcd_eq_gcd_ab a b`. Rewrite `h` using `[hab.gcd_eq_one, Nat.cast_one]`. Establish `e1 : x = (Nat.gcdA a b) • (a • x) + (Nat.gcdB a b) • (b • x)`.

Rewrite using `[← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, ← add_smul, mul_comm, mul_comm (Nat.gcdB a b), ← h, one_smul]`. Rewrite using `[e1]`. Conclude with `N.add_mem (N.toAddSubgroup.zsmul_mem hax _) (N.toAddSubgroup.zsmul_mem hbx _)`.
-/
theorem inf_sup_mulSub (N : Submodule R X) {a b : ℕ} (hab : a.Coprime b)
    (hN : N.toAddSubgroup.index = a * b) :
    (N ⊔ mulSub R X a) ⊓ (N ⊔ mulSub R X b) = N := by
  have hkill : ∀ w : X, (a * b) • w ∈ N := fun w => by
    have := AddSubgroup.nsmul_index_mem N.toAddSubgroup w
    rw [hN] at this
    exact this
  refine le_antisymm ?_ (le_inf le_sup_left le_sup_left)
  rintro x ⟨hx1, hx2⟩
  obtain ⟨y1, hy1, z1, hz1, rfl⟩ := Submodule.mem_sup.mp hx1
  obtain ⟨y2, hy2, z2, hz2, h2⟩ := Submodule.mem_sup.mp hx2
  obtain ⟨w1, rfl⟩ := mem_mulSub hz1
  obtain ⟨w2, rfl⟩ := mem_mulSub hz2
  set x := y1 + a • w1 with hxdef
  have hbx : b • x ∈ N := by
    rw [hxdef, smul_add, smul_smul, mul_comm b a]
    exact N.add_mem (N.toAddSubgroup.nsmul_mem hy1 b) (hkill w1)
  have hax : a • x ∈ N := by
    rw [← h2, smul_add, smul_smul]
    exact N.add_mem (N.toAddSubgroup.nsmul_mem hy2 a) (hkill w2)
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have e1 : x = (Nat.gcdA a b) • (a • x) + (Nat.gcdB a b) • (b • x) := by
    rw [← natCast_zsmul, ← natCast_zsmul, ← mul_smul, ← mul_smul, ← add_smul, mul_comm,
      mul_comm (Nat.gcdB a b), ← h, one_smul]
  rw [e1]
  exact N.add_mem (N.toAddSubgroup.zsmul_mem hax _) (N.toAddSubgroup.zsmul_mem hbx _)

/- English proof (translation)
Establish `e1 : (N.comap L.subtype).toAddSubgroup = N.toAddSubgroup.comap L.subtype.toAddMonoidHom`. Use extensionality with `x`. Both sides reduce to the same expression. Establish `e2 : L.subtype.toAddMonoidHom.range = L.toAddSubgroup`. Use extensionality with `x`.

Simplify using the standard rewrite rules. Rewrite using `[e1, AddSubgroup.index_comap, e2]`. Conclude with `AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono h)`.
-/
theorem index_comap_mul (N L : Submodule R X) (h : N ≤ L) :
    (N.comap L.subtype).toAddSubgroup.index * L.toAddSubgroup.index = N.toAddSubgroup.index := by
  have e1 : (N.comap L.subtype).toAddSubgroup =
      N.toAddSubgroup.comap L.subtype.toAddMonoidHom := by
    ext x; rfl
  have e2 : L.subtype.toAddMonoidHom.range = L.toAddSubgroup := by
    ext x; simp
  rw [e1, AddSubgroup.index_comap, e2]
  exact AddSubgroup.relIndex_mul_index (Submodule.toAddSubgroup_mono h)

/- English proof (translation)
Set `F : Submodule R X → Submodule R X × Submodule R X` to `fun N => (N ⊔ mulSub R X a, N ⊔ mulSub R X b)`. Establish `hmaps : ∀ N ∈ idxSet R X (a * b), F N ∈ idxSet R X a ×ˢ idxSet R X b`. Introduce `N hN`. Establish `hN' : N.toAddSubgroup.index = a * b` using `hN`. Establish `d1` using `index_sup_mulSub_dvd N hab ha hb hN'`.

Establish `d2` using `index_sup_mulSub_dvd N hab.symm hb ha (by rw [hN', mul_comm])`. Establish `hinf` using `inf_sup_mulSub N hab hN'`. Establish `hle : a * b ≤ (N ⊔ mulSub R X a).toAddSubgroup.index * (N ⊔ mulSub R X b).toAddSubgroup.index`. Rewrite using `[← hN']`. Use `conv_lhs => rw [← hinf]`.

Conclude with `AddSubgroup.index_inf_le (H := (N ⊔ mulSub R X a).toAddSubgroup) (K := (N ⊔ mulSub R X b).toAddSubgroup)`. Use `set i1 := (N ⊔ mulSub R X a).toAddSubgroup.index`. Use `set i2 := (N ⊔ mulSub R X b).toAddSubgroup.index`. Establish `l1 : i1 ≤ a` using `Nat.le_of_dvd ha d1`. Establish `l2 : i2 ≤ b` using `Nat.le_of_dvd hb d2`.

Establish `e1 : i1 = a`. Use `le_antisymm l1 ?_` and prove the remaining obligations. Establish `: a * b ≤ i1 * b` using `hle.trans (Nat.mul_le_mul_left _ l2)`. Conclude with `Nat.le_of_mul_le_mul_right this hb`. Establish `e2 : i2 = b`.

Use `le_antisymm l2 ?_` and prove the remaining obligations. Establish `: a * b ≤ a * i2` using `hle.trans (Nat.mul_le_mul_right _ l1)`. Conclude with `Nat.le_of_mul_le_mul_left this ha`. Conclude with `⟨e1, e2⟩`. Establish `hinj : Set.InjOn F (idxSet R X (a * b))`.

Introduce `N₁ h₁ N₂ h₂ h`. Simplify using `only [F, Prod.mk.injEq] at h`. Rewrite using `[← inf_sup_mulSub N₁ hab h₁, ← inf_sup_mulSub N₂ hab h₂, h.1, h.2]`. Use `⟨Set.Finite.of_finite_image ((h1.prod h2).subset (Set.image_subset_iff.mpr hmaps)) hinj, ?_⟩` and prove the remaining obligations. Rewrite using `[← Set.ncard_prod]`.

Conclude with `Set.ncard_le_ncard_of_injOn F hmaps hinj (h1.prod h2)`.
-/
theorem mul_count {a b : ℕ} (hab : a.Coprime b) (ha : 0 < a) (hb : 0 < b)
    (h1 : (idxSet R X a).Finite) (h2 : (idxSet R X b).Finite) :
    (idxSet R X (a * b)).Finite ∧
      (idxSet R X (a * b)).ncard ≤ (idxSet R X a).ncard * (idxSet R X b).ncard := by
  let F : Submodule R X → Submodule R X × Submodule R X :=
    fun N => (N ⊔ mulSub R X a, N ⊔ mulSub R X b)
  have hmaps : ∀ N ∈ idxSet R X (a * b), F N ∈ idxSet R X a ×ˢ idxSet R X b := by
    intro N hN
    have hN' : N.toAddSubgroup.index = a * b := hN
    have d1 := index_sup_mulSub_dvd N hab ha hb hN'
    have d2 := index_sup_mulSub_dvd N hab.symm hb ha (by rw [hN', mul_comm])
    have hinf := inf_sup_mulSub N hab hN'
    have hle : a * b ≤ (N ⊔ mulSub R X a).toAddSubgroup.index *
        (N ⊔ mulSub R X b).toAddSubgroup.index := by
      rw [← hN']
      conv_lhs => rw [← hinf]
      exact AddSubgroup.index_inf_le (H := (N ⊔ mulSub R X a).toAddSubgroup)
        (K := (N ⊔ mulSub R X b).toAddSubgroup)
    set i1 := (N ⊔ mulSub R X a).toAddSubgroup.index
    set i2 := (N ⊔ mulSub R X b).toAddSubgroup.index
    have l1 : i1 ≤ a := Nat.le_of_dvd ha d1
    have l2 : i2 ≤ b := Nat.le_of_dvd hb d2
    have e1 : i1 = a := by
      refine le_antisymm l1 ?_
      have : a * b ≤ i1 * b := hle.trans (Nat.mul_le_mul_left _ l2)
      exact Nat.le_of_mul_le_mul_right this hb
    have e2 : i2 = b := by
      refine le_antisymm l2 ?_
      have : a * b ≤ a * i2 := hle.trans (Nat.mul_le_mul_right _ l1)
      exact Nat.le_of_mul_le_mul_left this ha
    exact ⟨e1, e2⟩
  have hinj : Set.InjOn F (idxSet R X (a * b)) := by
    intro N₁ h₁ N₂ h₂ h
    simp only [F, Prod.mk.injEq] at h
    rw [← inf_sup_mulSub N₁ hab h₁, ← inf_sup_mulSub N₂ hab h₂, h.1, h.2]
  refine ⟨Set.Finite.of_finite_image ((h1.prod h2).subset (Set.image_subset_iff.mpr hmaps)) hinj,
    ?_⟩
  rw [← Set.ncard_prod]
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (h1.prod h2)

end Mul

section NF

open NumberField

variable (E : Type) [Field E] [NumberField E]

def TF (X : Type) [AddCommGroup X] [Module (𝓞 E) X] : Prop :=
  ∀ a : 𝓞 E, a ≠ 0 → ∀ x : X, a • x = 0 → x = 0

def LIB (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (k : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (v : ι → X), LinearIndependent (𝓞 E) v → Fintype.card ι ≤ k

variable {E}

/- English proof (translation)
Introduce `a ha x hx`. Conclude with `Subtype.ext (h a ha x (congrArg Subtype.val hx))`.
-/
theorem TF.submodule {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (h : TF E X)
    (L : Submodule (𝓞 E) X) : TF E L := by
  intro a ha x hx
  exact Subtype.ext (h a ha x (congrArg Subtype.val hx))

/- English proof (translation)
Introduce `ι _ v hv`. Conclude with `h ι (L.subtype ∘ v) (hv.map' L.subtype (Submodule.ker_subtype L))`.
-/
theorem LIB.submodule {X : Type} [AddCommGroup X] [Module (𝓞 E) X] {k : ℕ} (h : LIB E X k)
    (L : Submodule (𝓞 E) X) : LIB E L k := by
  intro ι _ v hv
  exact h ι (L.subtype ∘ v) (hv.map' L.subtype (Submodule.ker_subtype L))

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Use `letI : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P`. Distinguish the cases in `hfin : Finite (𝓞 E ⧸ P)`. Take `⟨ℓ, hℓ⟩` from `CharP.exists (𝓞 E ⧸ P) haveI := hℓ haveI : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _`. Take `⟨n, hℓp, hn⟩` from `FiniteField.card (𝓞 E ⧸ P) ℓ`.

Establish `hdvd : ℓ ∣ Nat.card (𝓞 E ⧸ P)`. Rewrite using `[Nat.card_eq_fintype_card, hn]`. Conclude with `dvd_pow_self ℓ (PNat.ne_zero n)`. Establish `h2 : ℓ ∣ p` using `hℓp.dvd_of_dvd_pow (dvd_trans hdvd h)`. Conclude with `(CharP.cast_eq_zero_iff (𝓞 E ⧸ P) ℓ p).2 h2`.

Use `haveI : Infinite (𝓞 E ⧸ P) := not_finite_iff_infinite.1 hfin`. Rewrite `h` using `[Nat.card_eq_zero_of_infinite]`. Establish `h0 : p ^ e = 0` using `zero_dvd_iff.1 h`. Establish `hp : p = 0`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases.

Simplify using `[he] at h0`. Conclude with `(pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 he)).1 h0`. Simplify using `[hp]`.
-/
theorem mem_of_card_dvd {P : Ideal (𝓞 E)} [P.IsMaximal] {p e : ℕ}
    (h : Nat.card (𝓞 E ⧸ P) ∣ p ^ e) : ((p : ℕ) : 𝓞 E) ∈ P := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  letI : Field (𝓞 E ⧸ P) := Ideal.Quotient.field P
  by_cases hfin : Finite (𝓞 E ⧸ P)
  · obtain ⟨ℓ, hℓ⟩ := CharP.exists (𝓞 E ⧸ P)
    haveI := hℓ
    haveI : Fintype (𝓞 E ⧸ P) := Fintype.ofFinite _
    obtain ⟨n, hℓp, hn⟩ := FiniteField.card (𝓞 E ⧸ P) ℓ
    have hdvd : ℓ ∣ Nat.card (𝓞 E ⧸ P) := by
      rw [Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self ℓ (PNat.ne_zero n)
    have h2 : ℓ ∣ p := hℓp.dvd_of_dvd_pow (dvd_trans hdvd h)
    exact (CharP.cast_eq_zero_iff (𝓞 E ⧸ P) ℓ p).2 h2
  · haveI : Infinite (𝓞 E ⧸ P) := not_finite_iff_infinite.1 hfin
    rw [Nat.card_eq_zero_of_infinite] at h
    have h0 : p ^ e = 0 := zero_dvd_iff.1 h
    have hp : p = 0 := by
      rcases Nat.eq_zero_or_pos e with he | he
      · simp [he] at h0
      · exact (pow_eq_zero_iff (Nat.pos_iff_ne_zero.1 he)).1 h0
    simp [hp]

/- English proof (translation)
Use `⟨s.finite_toSet.biUnion (fun b hb => ht b hb), ?_⟩` and prove the remaining obligations. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.set_biUnion_insert, Finset.sum_insert ha]`.

Establish `ih'` using `ih (fun b hb => ht b (Finset.mem_insert_of_mem hb))`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ncard_biUnion_le {α β : Type} (s : Finset β) (t : β → Set α)
    (ht : ∀ b ∈ s, (t b).Finite) :
    (⋃ b ∈ s, t b).Finite ∧ (⋃ b ∈ s, t b).ncard ≤ ∑ b ∈ s, (t b).ncard := by
  classical
  refine ⟨s.finite_toSet.biUnion (fun b hb => ht b hb), ?_⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have ih' := ih (fun b hb => ht b (Finset.mem_insert_of_mem hb))
    calc (t a ∪ ⋃ b ∈ s, t b).ncard ≤ (t a).ncard + (⋃ b ∈ s, t b).ncard := Set.ncard_union_le _ _
      _ ≤ _ := Nat.add_le_add_left ih' _

/- English proof (translation)
Proceed by induction on `e using Nat.strong_induction_on with`. Consider the case `_ e ih`. Introduce `X _ _ _ htf hli`. Break down `Nat.eq_zero_or_pos e with rfl | he` into its components or cases. Establish `h1 : idxSet (𝓞 E) X (p ^ 0) = {⊤}`.

Use extensionality with `N`. Simplify using `only [idxSet, pow_zero, Set.mem_ofPred_eq, AddSubgroup.index_eq_one, Set.mem_singleton_iff, Submodule.toAddSubgroup_eq_top]`. Rewrite using `[h1]`. Simplify using the standard rewrite rules. Establish `: IsNoetherian (𝓞 E) X` using `isNoetherian_of_isNoetherianRing_of_finite _ _`.

Use `set n := finrank ℚ E with hn_def`. Establish `hn : 0 < n` using `Module.finrank_pos`. Take `⟨Ps, hPs, hPmem⟩` from `primes_card E p hp`. Set `G : Finset (Ideal (𝓞 E))` to `Ps.filter (fun P => P.IsMaximal ∧ Nat.card (𝓞 E ⧸ P) ∣ p ^ e)`. Establish `hGf : ∀ P ∈ G, ∃ f : ℕ, 1 ≤ f ∧ f ≤ e ∧ Nat.card (𝓞 E ⧸ P) = p ^ f`.

Introduce `P hP`. Take `⟨_, hPm, hdvd⟩` from `Finset.mem_filter.mp hP`. Take `⟨f, hfe, hf⟩` from `(Nat.dvd_prime_pow hp).mp hdvd`. Use `⟨f, ?_, hfe, hf⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos f with rfl | hf0` into its components or cases.

It suffices to derive a contradiction. Establish `: Nontrivial (𝓞 E ⧸ P)` using `Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top`. Establish `h2 : 1 < Nat.card (𝓞 E ⧸ P)` using `Finite.one_lt_card`. Rewrite `h2` using `[hf, pow_zero]`. Conclude with `lt_irrefl _ h2`.

Conclude with `hf0`. Use `choose! f hf1 hfe hfc using hGf`. Set `A : Ideal (𝓞 E) → Submodule (𝓞 E) X → Set (Submodule (𝓞 E) X)` to `fun P L => (Submodule.map L.subtype) '' idxSet (𝓞 E) L (p ^ (e - f P))`. Establish `hhyp : ∀ P ∈ G, (hyp P X).Finite ∧ (hyp P X).ncard ≤ (p ^ f P) ^ k`. Introduce `P hP`.

Establish `hPm : P.IsMaximal` using `(Finset.mem_filter.mp hP).2.1`. Establish `hP0 : P ≠ ⊥` using `(Ideal.bot_lt_of_maximal P (RingOfIntegers.not_isField E)).ne'`. Take `⟨s, hsk, hs⟩` from `exists_gen_mod P hP0 htf k hli`. Use `hyp_count P k (card_hom_le P k s hsk hs)` as an intermediate fact. Rewrite `this` using `[hfc P hP]`.

Conclude with `this`. Establish `hA : ∀ P ∈ G, ∀ L ∈ hyp P X, (A P L).Finite ∧ (A P L).ncard ≤ n ^ (e - f P) * (p ^ (e - f P)) ^ k`. Introduce `P hP L _`. Establish `h` using `ih (e - f P) (by have := hf1 P hP; omega) L (htf.submodule L) (hli.submodule L)`. Conclude with `⟨h.1.image _, (Set.ncard_image_le h.1).trans h.2⟩`.

Set `H : Ideal (𝓞 E) → Finset (Submodule (𝓞 E) X)` to `fun P => if h : P ∈ G then (hhyp P h).1.toFinset else ∅`. Establish `hH : ∀ P ∈ G, ∀ L, L ∈ H P ↔ L ∈ hyp P X`. Introduce `P hP L`. Simplify using `only [H, dif_pos hP, Set.Finite.mem_toFinset]`. Establish `hHc : ∀ P ∈ G, (H P).card ≤ (p ^ f P) ^ k`.

Introduce `P hP`. Simplify using `only [H, dif_pos hP]`. Rewrite using `[← Set.ncard_eq_toFinset_card _ (hhyp P hP).1]`. Conclude with `(hhyp P hP).2`. Establish `hcover : idxSet (𝓞 E) X (p ^ e) ⊆ ⋃ P ∈ G, ⋃ L ∈ H P, A P L`.

Introduce `N hN`. Establish `hN' : N.toAddSubgroup.index = p ^ e` using `hN`. Establish `hNtop : N ≠ ⊤`. Introduce and unpack `rfl`. Establish `h1 : (⊤ : Submodule (𝓞 E) X).toAddSubgroup.index = 1` using `by simp`.

Rewrite `h1` using `[hN']`. Conclude with `(Nat.one_lt_pow he.ne' hp.one_lt).ne' h1`. Take `⟨P, hPm, L, hL, hNL⟩` from `exists_hyp_above N hNtop`. Establish `hdvd : Nat.card (𝓞 E ⧸ P) ∣ p ^ e`. Rewrite using `[← hL.2, ← hN']`.

Conclude with `AddSubgroup.index_dvd_of_le (Submodule.toAddSubgroup_mono hNL)`. Establish `hPG : P ∈ G` using `Finset.mem_filter.mpr ⟨hPmem P hPm (mem_of_card_dvd hdvd), hPm, hdvd⟩`. Establish `hrel : (N.comap L.subtype).toAddSubgroup.index = p ^ (e - f P)`. Establish `h1` using `index_comap_mul N L hNL`. Rewrite `h1` using `[hL.2, hfc P hPG, hN']`.

Establish `h2 : p ^ (e - f P) * p ^ f P = p ^ e`. Rewrite using `[← pow_add, Nat.sub_add_cancel (hfe P hPG)]`. Conclude with `Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (h1.trans h2.symm)`. Establish `hmemA : N ∈ A P L`. Use `⟨N.comap L.subtype, hrel, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.mpr hNL]`. Conclude with `Set.mem_iUnion₂.mpr ⟨P, hPG, Set.mem_iUnion₂.mpr ⟨L, (hH P hPG L).mpr hL, hmemA⟩⟩`. Establish `hinner : ∀ P ∈ G, (⋃ L ∈ H P, A P L).Finite ∧ (⋃ L ∈ H P, A P L).ncard ≤ n ^ (e - 1) * (p ^ e) ^ k`. Introduce `P hP`. Take `⟨hfin, hle⟩` from `ncard_biUnion_le (H P) (A P) (fun L hL => (hA P hP L ((hH P hP L).mp hL)).1)`.

Use `⟨hfin, hle.trans ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, smul_eq_mul]`. Use `_ ≤ (p ^ f P) ^ k * (n ^ (e - f P) * (p ^ (e - f P)) ^ k) := Nat.mul_le_mul_right _ (hHc P hP)`. Use `_ = n ^ (e - f P) * (p ^ e) ^ k := by`.

Rewrite using `[mul_left_comm, ← mul_pow, ← pow_add, Nat.add_sub_cancel' (hfe P hP)]`. Use `_ ≤ n ^ (e - 1) * (p ^ e) ^ k := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn (by have := hf1 P hP; omega))`. Take `⟨hfinU, hleU⟩` from `ncard_biUnion_le G (fun P => ⋃ L ∈ H P, A P L) (fun P hP => (hinner P hP).1)`. Use `⟨hfinU.subset hcover, (Set.ncard_le_ncard hcover hfinU).trans (hleU.trans ?_)⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]`.
-/
theorem count_prime_pow (k p : ℕ) (hp : p.Prime) (e : ℕ) :
    ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X],
      TF E X → LIB E X k →
      (idxSet (𝓞 E) X (p ^ e)).Finite ∧
        (idxSet (𝓞 E) X (p ^ e)).ncard ≤ finrank ℚ E ^ e * (p ^ e) ^ k := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro X _ _ _ htf hli
  rcases Nat.eq_zero_or_pos e with rfl | he
  · have h1 : idxSet (𝓞 E) X (p ^ 0) = {⊤} := by
      ext N
      simp only [idxSet, pow_zero, Set.mem_ofPred_eq, AddSubgroup.index_eq_one,
        Set.mem_singleton_iff, Submodule.toAddSubgroup_eq_top]
    rw [h1]
    simp
  classical
  have : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite _ _
  set n := finrank ℚ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  obtain ⟨Ps, hPs, hPmem⟩ := primes_card E p hp
  let G : Finset (Ideal (𝓞 E)) :=
    Ps.filter (fun P => P.IsMaximal ∧ Nat.card (𝓞 E ⧸ P) ∣ p ^ e)
  have hGf : ∀ P ∈ G, ∃ f : ℕ, 1 ≤ f ∧ f ≤ e ∧ Nat.card (𝓞 E ⧸ P) = p ^ f := by
    intro P hP
    obtain ⟨_, hPm, hdvd⟩ := Finset.mem_filter.mp hP
    obtain ⟨f, hfe, hf⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    refine ⟨f, ?_, hfe, hf⟩
    rcases Nat.eq_zero_or_pos f with rfl | hf0
    · exfalso
      have : Nontrivial (𝓞 E ⧸ P) := Ideal.Quotient.nontrivial_iff.mpr hPm.ne_top
      have h2 : 1 < Nat.card (𝓞 E ⧸ P) := Finite.one_lt_card
      rw [hf, pow_zero] at h2
      exact lt_irrefl _ h2
    · exact hf0
  choose! f hf1 hfe hfc using hGf
  let A : Ideal (𝓞 E) → Submodule (𝓞 E) X → Set (Submodule (𝓞 E) X) :=
    fun P L => (Submodule.map L.subtype) '' idxSet (𝓞 E) L (p ^ (e - f P))
  have hhyp : ∀ P ∈ G, (hyp P X).Finite ∧ (hyp P X).ncard ≤ (p ^ f P) ^ k := by
    intro P hP
    have hPm : P.IsMaximal := (Finset.mem_filter.mp hP).2.1
    have hP0 : P ≠ ⊥ := (Ideal.bot_lt_of_maximal P (RingOfIntegers.not_isField E)).ne'
    obtain ⟨s, hsk, hs⟩ := exists_gen_mod P hP0 htf k hli
    have := hyp_count P k (card_hom_le P k s hsk hs)
    rw [hfc P hP] at this
    exact this
  have hA : ∀ P ∈ G, ∀ L ∈ hyp P X,
      (A P L).Finite ∧ (A P L).ncard ≤ n ^ (e - f P) * (p ^ (e - f P)) ^ k := by
    intro P hP L _
    have h := ih (e - f P) (by have := hf1 P hP; omega) L (htf.submodule L) (hli.submodule L)
    exact ⟨h.1.image _, (Set.ncard_image_le h.1).trans h.2⟩
  let H : Ideal (𝓞 E) → Finset (Submodule (𝓞 E) X) :=
    fun P => if h : P ∈ G then (hhyp P h).1.toFinset else ∅
  have hH : ∀ P ∈ G, ∀ L, L ∈ H P ↔ L ∈ hyp P X := by
    intro P hP L
    simp only [H, dif_pos hP, Set.Finite.mem_toFinset]
  have hHc : ∀ P ∈ G, (H P).card ≤ (p ^ f P) ^ k := by
    intro P hP
    simp only [H, dif_pos hP]
    rw [← Set.ncard_eq_toFinset_card _ (hhyp P hP).1]
    exact (hhyp P hP).2
  have hcover : idxSet (𝓞 E) X (p ^ e) ⊆ ⋃ P ∈ G, ⋃ L ∈ H P, A P L := by
    intro N hN
    have hN' : N.toAddSubgroup.index = p ^ e := hN
    have hNtop : N ≠ ⊤ := by
      rintro rfl
      have h1 : (⊤ : Submodule (𝓞 E) X).toAddSubgroup.index = 1 := by simp
      rw [hN'] at h1
      exact (Nat.one_lt_pow he.ne' hp.one_lt).ne' h1
    obtain ⟨P, hPm, L, hL, hNL⟩ := exists_hyp_above N hNtop
    have hdvd : Nat.card (𝓞 E ⧸ P) ∣ p ^ e := by
      rw [← hL.2, ← hN']
      exact AddSubgroup.index_dvd_of_le (Submodule.toAddSubgroup_mono hNL)
    have hPG : P ∈ G := Finset.mem_filter.mpr ⟨hPmem P hPm (mem_of_card_dvd hdvd), hPm, hdvd⟩
    have hrel : (N.comap L.subtype).toAddSubgroup.index = p ^ (e - f P) := by
      have h1 := index_comap_mul N L hNL
      rw [hL.2, hfc P hPG, hN'] at h1
      have h2 : p ^ (e - f P) * p ^ f P = p ^ e := by
        rw [← pow_add, Nat.sub_add_cancel (hfe P hPG)]
      exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos _) (h1.trans h2.symm)
    have hmemA : N ∈ A P L := by
      refine ⟨N.comap L.subtype, hrel, ?_⟩
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hNL]
    exact Set.mem_iUnion₂.mpr ⟨P, hPG, Set.mem_iUnion₂.mpr ⟨L, (hH P hPG L).mpr hL, hmemA⟩⟩
  have hinner : ∀ P ∈ G, (⋃ L ∈ H P, A P L).Finite ∧
      (⋃ L ∈ H P, A P L).ncard ≤ n ^ (e - 1) * (p ^ e) ^ k := by
    intro P hP
    obtain ⟨hfin, hle⟩ := ncard_biUnion_le (H P) (A P)
      (fun L hL => (hA P hP L ((hH P hP L).mp hL)).1)
    refine ⟨hfin, hle.trans ?_⟩
    calc ∑ L ∈ H P, (A P L).ncard ≤ ∑ _L ∈ H P, n ^ (e - f P) * (p ^ (e - f P)) ^ k :=
          Finset.sum_le_sum fun L hL => (hA P hP L ((hH P hP L).mp hL)).2
      _ = (H P).card * (n ^ (e - f P) * (p ^ (e - f P)) ^ k) := by
          rw [Finset.sum_const, smul_eq_mul]
      _ ≤ (p ^ f P) ^ k * (n ^ (e - f P) * (p ^ (e - f P)) ^ k) :=
          Nat.mul_le_mul_right _ (hHc P hP)
      _ = n ^ (e - f P) * (p ^ e) ^ k := by
          rw [mul_left_comm, ← mul_pow, ← pow_add, Nat.add_sub_cancel' (hfe P hP)]
      _ ≤ n ^ (e - 1) * (p ^ e) ^ k :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hn (by have := hf1 P hP; omega))
  obtain ⟨hfinU, hleU⟩ := ncard_biUnion_le G (fun P => ⋃ L ∈ H P, A P L)
    (fun P hP => (hinner P hP).1)
  refine ⟨hfinU.subset hcover, (Set.ncard_le_ncard hcover hfinU).trans (hleU.trans ?_)⟩
  calc ∑ P ∈ G, (⋃ L ∈ H P, A P L).ncard ≤ ∑ _P ∈ G, n ^ (e - 1) * (p ^ e) ^ k :=
        Finset.sum_le_sum fun P hP => (hinner P hP).2
    _ = G.card * (n ^ (e - 1) * (p ^ e) ^ k) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ n * (n ^ (e - 1) * (p ^ e) ^ k) :=
        Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans hPs)
    _ = n ^ e * (p ^ e) ^ k := by
        rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel he]

end NF

end CountO

open CountO in
/- English proof (translation)
Introduce `E _ _ M _ _ _ _ j hj`. Use `set k := finrank (𝓞 E) M`. Establish `htf : TF E M` using `fun a ha x hx => by`. Establish `h` using `Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M) (mem_nonZeroDivisors_of_ne_zero ha)`. Conclude with `h (hx.trans (smul_zero a).symm)`.

Establish `hli : LIB E M k` using `fun ι _ v hv => hv.fintype_card_le_finrank`. Establish `key : ∀ j : ℕ, 1 ≤ j → (idxSet (𝓞 E) M j).Finite ∧ (idxSet (𝓞 E) M j).ncard ≤ finrank ℚ E ^ (Nat.primeFactorsList j).length * j ^ k`. Introduce `j`. Proceed by induction on `j using Nat.recOnPosPrimePosCoprime with`. Consider the case `prime_pow p e hp _`.

Introduce `_`. Establish `h` using `count_prime_pow k p hp e M htf hli`. Rewrite using `[hp.primeFactorsList_pow, List.length_replicate]`. Conclude with `h`. Consider the case `zero => intro h`.

Use linear arithmetic over natural numbers and integers. Consider the case `one`. Introduce `_`. Establish `h` using `count_prime_pow k 2 Nat.prime_two 0 M htf hli`. Simplify using `using h`.

Consider the case `coprime a b ha hb hab iha ihb`. Introduce `_`. Take `⟨fa, ca⟩` from `iha (by omega)`. Take `⟨fb, cb⟩` from `ihb (by omega)`. Take `⟨fab, cab⟩` from `mul_count hab (by omega) (by omega) fa fb`.

Use `⟨fab, cab.trans ?_⟩` and prove the remaining obligations. Rewrite using `[(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append, pow_add, mul_pow]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `key j hj`.
-/
theorem card_submodules_of_index_le : Formalism.SLP.SubmoduleIndexCountO := by
  intro E _ _ M _ _ _ _ j hj
  set k := finrank (𝓞 E) M
  have htf : TF E M := fun a ha x hx => by
    have h := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := M)
      (mem_nonZeroDivisors_of_ne_zero ha)
    exact h (hx.trans (smul_zero a).symm)
  have hli : LIB E M k := fun ι _ v hv => hv.fintype_card_le_finrank
  have key : ∀ j : ℕ, 1 ≤ j → (idxSet (𝓞 E) M j).Finite ∧
      (idxSet (𝓞 E) M j).ncard ≤
        finrank ℚ E ^ (Nat.primeFactorsList j).length * j ^ k := by
    intro j
    induction j using Nat.recOnPosPrimePosCoprime with
    | prime_pow p e hp _ =>
      intro _
      have h := count_prime_pow k p hp e M htf hli
      rw [hp.primeFactorsList_pow, List.length_replicate]
      exact h
    | zero => intro h; omega
    | one =>
      intro _
      have h := count_prime_pow k 2 Nat.prime_two 0 M htf hli
      simpa using h
    | coprime a b ha hb hab iha ihb =>
      intro _
      obtain ⟨fa, ca⟩ := iha (by omega)
      obtain ⟨fb, cb⟩ := ihb (by omega)
      obtain ⟨fab, cab⟩ := mul_count hab (by omega) (by omega) fa fb
      refine ⟨fab, cab.trans ?_⟩
      rw [(Nat.perm_primeFactorsList_mul (by omega) (by omega)).length_eq, List.length_append,
        pow_add, mul_pow]
      calc (idxSet (𝓞 E) M a).ncard * (idxSet (𝓞 E) M b).ncard
          ≤ (finrank ℚ E ^ (Nat.primeFactorsList a).length * a ^ k) *
            (finrank ℚ E ^ (Nat.primeFactorsList b).length * b ^ k) := Nat.mul_le_mul ca cb
        _ = _ := by ring
  exact key j hj

end Formalism.SLP.P
