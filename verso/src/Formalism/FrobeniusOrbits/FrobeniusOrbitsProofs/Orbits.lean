import Mathlib
import Formalism.FrobeniusOrbits.HostOrbitsPlaces
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.CoprimeTwoPow
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.Galois

open Polynomial

noncomputable section

namespace Formalism.FrobeniusOrbits

namespace Orbits

/- English proof (translation)
Unfold `c0`. Apply `orderOf_eq_prime` to reduce the goal to its premises. Apply the tactic sequence `ext <;> simp`. Introduce `h`. Use `congrArg Prod.fst h` as an intermediate fact.

Simplify using `at this`.
-/
lemma orderOf_conjugation_eq_two : orderOf c0 = 2 := by
  unfold c0
  apply orderOf_eq_prime
  · ext <;> simp
  · intro h
    have := congrArg Prod.fst h
    simp at this

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma chD_apply (e : ℕ) (g : GG e) : chD e g = g.1.2 := rfl

/- English proof (translation)
Use `haveI : FiniteDimensional ℚ K := Module.Finite.trans E K`. Use `haveI : CharZero K := by first`. Consider the case `exact algebraRat.charZero K`. Consider the case `exact (algebraMap ℚ K).charZero`. Rewrite using `[Module.finrank_mul_finrank ℚ E K]`.

Establish `hint : IsIntegral ℚ μ` using `.of_finite ℚ μ`. Establish `h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1` using `by haveI : NeZero g := ⟨hg.ne_zero⟩`. Establish `hroot : aeval μ (cyclotomic g ℚ) = 0`. Rewrite using `[aeval_def, ← eval_map, map_cyclotomic]`. Conclude with `(isRoot_cyclotomic_iff.mpr hμ)`.

Rewrite using `[IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ), natDegree_cyclotomic, Nat.totient_prime hg]`. Rewrite using `[← h1, ← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K]`. Conclude with `Nat.le_mul_of_pos_right _ Module.finrank_pos`.
-/
lemma prim_bound {E K : Type*} [Field E] [Field K] [Algebra ℚ E] [Algebra ℚ K] [Algebra E K]
    [IsScalarTower ℚ E K] [FiniteDimensional ℚ E] [FiniteDimensional E K] (g : ℕ) (hg : g.Prime)
    (μ : K) (hμ : IsPrimitiveRoot μ g) :
    g - 1 ≤ Module.finrank ℚ E * Module.finrank E K := by
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : CharZero K := by
    first
    | exact algebraRat.charZero K
    | exact (algebraMap ℚ K).charZero
  rw [Module.finrank_mul_finrank ℚ E K]
  have hint : IsIntegral ℚ μ := .of_finite ℚ μ
  have h1 : Module.finrank ℚ (IntermediateField.adjoin ℚ {μ}) = g - 1 := by
    haveI : NeZero g := ⟨hg.ne_zero⟩
    have hroot : aeval μ (cyclotomic g ℚ) = 0 := by
      rw [aeval_def, ← eval_map, map_cyclotomic]
      exact (isRoot_cyclotomic_iff.mpr hμ)
    rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hg.pos) hroot (cyclotomic.monic g ℚ),
      natDegree_cyclotomic, Nat.totient_prime hg]
  rw [← h1, ← Module.finrank_mul_finrank ℚ (IntermediateField.adjoin ℚ {μ}) K]
  exact Nat.le_mul_of_pos_right _ Module.finrank_pos

/- English proof (translation)
Use `haveI := Fact.mk hg`. Establish `hint : IsIntegral E M` using `IsIntegral.of_finite E M`. Establish `hm0 : minpoly E M ≠ 0` using `minpoly.ne_zero hint`. Establish `hmk : (minpoly E M).natDegree ≤ k`. Establish `h1 : minpoly E M ∣ M.charpoly` using `minpoly.dvd E M (Matrix.aeval_self_charpoly M)`.

Establish `h2` using `natDegree_le_of_dvd h1 M.charpoly_monic.ne_zero`. Rewrite `h2` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]`. Then use the resulting hypothesis. Establish `hfac : (X ^ g - 1 : E[X]) = (X - 1) * cyclotomic g E`. Rewrite using `[mul_comm, cyclotomic_prime_mul_X_sub_one]`. Establish `hdvd : minpoly E M ∣ (X - 1) * cyclotomic g E`.

Rewrite using `[← hfac]`. Apply `minpoly.dvd` to reduce the goal to its premises. Simplify using `[hM]`. Establish `hnd : ¬ minpoly E M ∣ X - 1`. Introduce and unpack `⟨q, hq⟩`.

Apply `hne` to reduce the goal to its premises. Establish `h0 : aeval M (X - 1 : E[X]) = 0` using `by rw [hq, map_mul, minpoly.aeval, zero_mul]`. Simplify `h0` using `[sub_eq_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf, hfm, hfΦ⟩ : ∃ f : E[X], Irreducible f ∧ f ∣ minpoly E M ∧ f ∣ cyclotomic g E := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Establish `hcop : IsCoprime (minpoly E M) (cyclotomic g E)` using `isCoprime_of_irreducible_dvd (fun h => hm0 h.1) (fun z hz hzm hzΦ => hcon z hz hzm hzΦ)`. Conclude with `hnd (hcop.dvd_of_dvd_mul_right hdvd)`. Establish `hfk : f.natDegree ≤ k` using `(natDegree_le_of_dvd hfm hm0).trans hmk`. Use `haveI : Fact (Irreducible f) := ⟨hf⟩`.

Establish `hf0 : f ≠ 0` using `hf.ne_zero`. Use `haveI : FiniteDimensional E (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite`. Establish `hrank : Module.finrank E (AdjoinRoot f) = f.natDegree`. Rewrite using `[(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]`. Use `haveI : CharZero (AdjoinRoot f) := by first`.

Consider the case `exact algebraRat.charZero (AdjoinRoot f)`. Consider the case `exact (algebraMap ℚ (AdjoinRoot f)).charZero`. Use `haveI : NeZero g := ⟨hg.ne_zero⟩`. Establish `hμ : IsPrimitiveRoot (AdjoinRoot.root f) g`. Rewrite using `[← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot f)), IsRoot, eval_map]`.

Take `⟨q, hq⟩` from `hfΦ`. Rewrite using `[hq, eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]`. Establish `hb` using `prim_bound (E := E) (K := AdjoinRoot f) g hg _ hμ`. Rewrite `hb` using `[hrank]`. Conclude with `hb.trans (Nat.mul_le_mul_left _ hfk)`.
-/
lemma dim_bound {E : Type*} [Field E] [Algebra ℚ E] [FiniteDimensional ℚ E]
    (k g : ℕ) (hg : g.Prime) (M : Matrix (Fin k) (Fin k) E) (hM : M ^ g = 1) (hne : M ≠ 1) :
    g - 1 ≤ Module.finrank ℚ E * k := by
  classical
  haveI := Fact.mk hg
  have hint : IsIntegral E M := IsIntegral.of_finite E M
  have hm0 : minpoly E M ≠ 0 := minpoly.ne_zero hint
  have hmk : (minpoly E M).natDegree ≤ k := by
    have h1 : minpoly E M ∣ M.charpoly := minpoly.dvd E M (Matrix.aeval_self_charpoly M)
    have h2 := natDegree_le_of_dvd h1 M.charpoly_monic.ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h2
  have hfac : (X ^ g - 1 : E[X]) = (X - 1) * cyclotomic g E := by
    rw [mul_comm, cyclotomic_prime_mul_X_sub_one]
  have hdvd : minpoly E M ∣ (X - 1) * cyclotomic g E := by
    rw [← hfac]
    apply minpoly.dvd
    simp [hM]
  have hnd : ¬ minpoly E M ∣ X - 1 := by
    rintro ⟨q, hq⟩
    apply hne
    have h0 : aeval M (X - 1 : E[X]) = 0 := by rw [hq, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h0
  obtain ⟨f, hf, hfm, hfΦ⟩ : ∃ f : E[X], Irreducible f ∧ f ∣ minpoly E M ∧ f ∣ cyclotomic g E := by
    by_contra hcon
    push_neg at hcon
    have hcop : IsCoprime (minpoly E M) (cyclotomic g E) :=
      isCoprime_of_irreducible_dvd (fun h => hm0 h.1) (fun z hz hzm hzΦ => hcon z hz hzm hzΦ)
    exact hnd (hcop.dvd_of_dvd_mul_right hdvd)
  have hfk : f.natDegree ≤ k := (natDegree_le_of_dvd hfm hm0).trans hmk
  haveI : Fact (Irreducible f) := ⟨hf⟩
  have hf0 : f ≠ 0 := hf.ne_zero
  haveI : FiniteDimensional E (AdjoinRoot f) := (AdjoinRoot.powerBasis hf0).finite
  have hrank : Module.finrank E (AdjoinRoot f) = f.natDegree := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim]
  haveI : CharZero (AdjoinRoot f) := by
    first
    | exact algebraRat.charZero (AdjoinRoot f)
    | exact (algebraMap ℚ (AdjoinRoot f)).charZero
  haveI : NeZero g := ⟨hg.ne_zero⟩
  have hμ : IsPrimitiveRoot (AdjoinRoot.root f) g := by
    rw [← isRoot_cyclotomic_iff, ← map_cyclotomic g (algebraMap E (AdjoinRoot f)), IsRoot, eval_map]
    obtain ⟨q, hq⟩ := hfΦ
    rw [hq, eval₂_mul, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, zero_mul]
  have hb := prim_bound (E := E) (K := AdjoinRoot f) g hg _ hμ
  rw [hrank] at hb
  exact hb.trans (Nat.mul_le_mul_left _ hfk)

end Orbits

open Orbits

/- English proof (translation)
Unfold `HostOrbits`. Introduce `e φ hφ`. Apply the tactic sequence `have hb : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]`. Use `⟨fun τ hτ i => ?_, fun h0 hne => ?_⟩` and prove the remaining obligations. Establish `hτ2 : τ.1.2 = 1` using `by simpa [Psi, chD] using hτ`.

Establish `hm : (φ ^ i * τ).1.2 = (-1) ^ i` using `by simp [hb, hτ2]`. Establish `: φ ^ i * τ ∈ Psi e ↔ (φ ^ i * τ).1.2 = 1` using `by simp [Psi, chD]`. Rewrite using `[this, hm]`. Conclude with `neg_one_pow_eq_one_iff_even (by decide)`. Establish `hpow : ∀ x : HGrp e, x ^ (2 ^ (e + 1)) = 1`.

Introduce `x`. Take `⟨u, rfl⟩` from `QuotientGroup.mk_surjective x`. Establish `hc : Fintype.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1)`. Rewrite using `[ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two]`. Simplify using the standard rewrite rules.

Rewrite using `[← QuotientGroup.mk_pow, ← hc, pow_card_eq_one, QuotientGroup.mk_one]`. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hpow φ.2))`. Establish `hj0 : j ≠ 0`. Introduce and unpack `rfl`. Conclude with `hne (orderOf_eq_one_iff.mp (by simpa using hj))`.

Establish `hev : Even (orderOf φ.2)`. Rewrite using `[hj]`. Conclude with `(Nat.even_pow.mpr ⟨even_two, hj0⟩)`. Use `⟨hev, ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.orderOf, h0, orderOf_conjugation_eq_two]`.

Conclude with `Nat.lcm_eq_right (even_iff_two_dvd.mp hev)`.
-/
theorem hostOrbits : HostOrbits := by
  unfold HostOrbits
  intro e φ hφ
  have hb : φ.1.2 = -1 := by rcases hφ with h | h <;> simp [h, c0]
  refine ⟨fun τ hτ i => ?_, fun h0 hne => ?_⟩
  · have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
    have hm : (φ ^ i * τ).1.2 = (-1) ^ i := by simp [hb, hτ2]
    have : φ ^ i * τ ∈ Psi e ↔ (φ ^ i * τ).1.2 = 1 := by simp [Psi, chD]
    rw [this, hm]
    exact neg_one_pow_eq_one_iff_even (by decide)
  ·
    have hpow : ∀ x : HGrp e, x ^ (2 ^ (e + 1)) = 1 := by
      intro x
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
      have hc : Fintype.card (ZMod (2 ^ (e + 2)))ˣ = 2 ^ (e + 1) := by
        rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow_succ Nat.prime_two]
        simp
      rw [← QuotientGroup.mk_pow, ← hc, pow_card_eq_one, QuotientGroup.mk_one]
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one (hpow φ.2))
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hj))
    have hev : Even (orderOf φ.2) := by
      rw [hj]
      exact (Nat.even_pow.mpr ⟨even_two, hj0⟩)
    refine ⟨hev, ?_⟩
    rw [Prod.orderOf, h0, orderOf_conjugation_eq_two]
    exact Nat.lcm_eq_right (even_iff_two_dvd.mp hev)

/- English proof (translation)
Unfold `HostOrbitsPlaces`. Introduce `e φ hφ τ hτ i`. Establish `hτ2 : τ.1.2 = 1` using `by simpa [Psi, chD] using hτ`. Establish `hne : (-1 : ℤˣ) ≠ 1` using `by decide`. Break down `Nat.even_or_odd i with hi | hi` into its components or cases.

Establish `hc : φ.1 ^ i = 1`. Break down `hφ with h | h` into its components or cases. Apply the tactic sequence `rw [h, c0]; ext <;> simp [hi.neg_one_pow]`. Apply the tactic sequence `rw [h]; ext <;> simp [hi.neg_one_pow]`. Establish `hp : placeOf (φ ^ i * τ) = φ ^ i * τ`.

Unfold `placeOf`. Rewrite using `[if_pos]`. Simplify using `[Prod.pow_fst, hc, hτ2]`. Rewrite using `[hp]`. Use `⟨by simp, fun _ => by simp [hc], fun _ => by simp [hc, hi]⟩` and prove the remaining obligations.

Establish `hp : placeOf (φ ^ i * τ) = cc e * (φ ^ i * τ)`. Unfold `placeOf`. Rewrite using `[if_neg]`. Break down `hφ with h | h` into its components or cases. Simplify using `[h, c0, hi.neg_one_pow, hτ2, hne]`.

Simplify using `[h, hi.neg_one_pow, hτ2, hne]`. Rewrite using `[hp]`. Use `⟨by simp [cc], fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2]`. Establish `hni : ¬ Even i` using `Nat.not_even_iff_odd.mpr hi`.

Apply the tactic sequence `ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2, hni, sg]`.
-/
theorem hostOrbitsPlaces : HostOrbitsPlaces := by
  unfold HostOrbitsPlaces
  intro e φ hφ τ hτ i
  have hτ2 : τ.1.2 = 1 := by simpa [Psi, chD] using hτ
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Nat.even_or_odd i with hi | hi
  · have hc : φ.1 ^ i = 1 := by
      rcases hφ with h | h
      · rw [h, c0]; ext <;> simp [hi.neg_one_pow]
      · rw [h]; ext <;> simp [hi.neg_one_pow]
    have hp : placeOf (φ ^ i * τ) = φ ^ i * τ := by
      unfold placeOf
      rw [if_pos]
      simp [Prod.pow_fst, hc, hτ2]
    rw [hp]
    refine ⟨by simp, fun _ => by simp [hc], fun _ => by simp [hc, hi]⟩
  · have hp : placeOf (φ ^ i * τ) = cc e * (φ ^ i * τ) := by
      unfold placeOf
      rw [if_neg]
      rcases hφ with h | h
      · simp [h, c0, hi.neg_one_pow, hτ2, hne]
      · simp [h, hi.neg_one_pow, hτ2, hne]
    rw [hp]
    refine ⟨by simp [cc], fun h => ?_, fun h => ?_⟩
    · ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2]
    · have hni : ¬ Even i := Nat.not_even_iff_odd.mpr hi
      ext <;> simp [cc, c0, h, hi.neg_one_pow, hτ2, hni, sg]

/- English proof (translation)
Unfold `HostOrbitCount`. Introduce `e φ h0 τ hτ`. Establish `hpl : ∀ i : ℕ, placeOf (φ ^ i * τ) = (τ.1, φ.2 ^ i * τ.2)`. Introduce `i`. Take `⟨h2, h1, -⟩` from `hostOrbitsPlaces e φ (Or.inl h0) τ hτ i`.

Conclude with `Prod.ext (h1 h0) h2`. Establish `hr : (Set.range fun i : ℕ => placeOf (φ ^ i * τ)) = (fun x : HGrp e => ((τ.1, x * τ.2) : GG e)) '' Set.range (fun i : ℕ => φ.2 ^ i)`. Use extensionality with `y`. Simplify using `[hpl]`. Rewrite using `[hr, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]`.

Rewrite using `[show Set.range (fun i : ℕ => φ.2 ^ i) = (Submonoid.powers φ.2 : Set (HGrp e)) from (Submonoid.coe_powers φ.2).symm, ← Nat.card_coe_set_eq]`. Conclude with `Nat.card_submonoidPowers`.
-/
theorem hostOrbitCount : HostOrbitCount := by
  unfold HostOrbitCount
  intro e φ h0 τ hτ
  have hpl : ∀ i : ℕ, placeOf (φ ^ i * τ) = (τ.1, φ.2 ^ i * τ.2) := by
    intro i
    obtain ⟨h2, h1, -⟩ := hostOrbitsPlaces e φ (Or.inl h0) τ hτ i
    exact Prod.ext (h1 h0) h2
  have hr : (Set.range fun i : ℕ => placeOf (φ ^ i * τ)) =
      (fun x : HGrp e => ((τ.1, x * τ.2) : GG e)) '' Set.range (fun i : ℕ => φ.2 ^ i) := by
    ext y
    simp [hpl]
  rw [hr, Set.ncard_image_of_injective _ (fun x y hxy => by simpa using hxy)]
  rw [show Set.range (fun i : ℕ => φ.2 ^ i) = (Submonoid.powers φ.2 : Set (HGrp e)) from
    (Submonoid.coe_powers φ.2).symm, ← Nat.card_coe_set_eq]
  exact Nat.card_submonoidPowers

/- English proof (translation)
Unfold `HostFiniteOrder`. Introduce `e q d hqd L _ _ ζ a b h k g hg M hM hne`. Use `dim_bound k g hg M hM hne` as an intermediate fact. Rewrite `this` using `[Galois.finrank_cmField hqd h]`. Then use the resulting hypothesis.
-/
theorem hostFiniteOrder : HostFiniteOrder := by
  unfold HostFiniteOrder
  intro e q d hqd L _ _ ζ a b h k g hg M hM hne
  have := dim_bound k g hg M hM hne
  rwa [Galois.finrank_cmField hqd h] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨hostOrbits, hostOrbitsPlaces, hostOrbitCount, hostFiniteOrder⟩`.
-/
theorem hostOrbitsFin : HostOrbits ∧ HostOrbitsPlaces ∧ HostOrbitCount ∧ HostFiniteOrder :=
  ⟨hostOrbits, hostOrbitsPlaces, hostOrbitCount, hostFiniteOrder⟩

end Formalism.FrobeniusOrbits
