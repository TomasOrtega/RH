import Mathlib
open NumberField

namespace GlobalTheory

namespace CyclotomicKummerDescent

/- English proof (translation)
Establish `hp : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.mp hl`. Establish `h1 : (l : ℤ) ∣ (t : ℤ) - 1` using `(dvd_pow_self _ two_ne_zero).trans ht`. Establish `h2 : ¬ (l : ℤ) ∣ (t : ℤ)` using `fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)`. Establish `hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) = emultiplicity (l : ℤ) ((t : ℤ) - 1) + r`. Break down `hl.eq_two_or_odd' with rfl | hodd` into its components or cases.

Establish `h` using `Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht) (by simpa using h2)`. Establish `h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r`. Use `push_cast`. Conclude with `emultiplicity_pow_self_of_prime Int.prime_two r`. Rewrite `h` using `[h3]`.

Simplify using `using h`. Rewrite using `[Int.emultiplicity_pow_sub_pow hl hodd h1 h2, emultiplicity_pow_self_of_prime hl.prime]`. Rewrite `hlte` using `[one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm]`. Establish `hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤`. Rewrite using `[← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]`.

Use `⟨by simpa using hl.ne_one, ?_⟩` and prove the remaining obligations. Establish `: (1 : ℤ) < t` using `by exact_mod_cast ht1`. Use linear arithmetic over natural numbers and integers. Establish `h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞)` using `WithTop.add_left_cancel hfin hlte`. Rewrite `h4` using `[emultiplicity_eq_coe]`.

Conclude with `h4` after adjusting the coercions.
-/
theorem geom_sum_valuation {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ∣ (t : ℤ) - 1 := (dvd_pow_self _ two_ne_zero).trans ht
  have h2 : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)
  have hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) =
      emultiplicity (l : ℤ) ((t : ℤ) - 1) + r := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have h := Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht)
        (by simpa using h2)
      have h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r := by
        push_cast
        exact emultiplicity_pow_self_of_prime Int.prime_two r
      rw [h3] at h
      simpa using h
    · rw [Int.emultiplicity_pow_sub_pow hl hodd h1 h2,
        emultiplicity_pow_self_of_prime hl.prime]
  rw [one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm] at hlte
  have hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤ := by
    rw [← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]
    refine ⟨by simpa using hl.ne_one, ?_⟩
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  have h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞) :=
    WithTop.add_left_cancel hfin hlte
  rw [emultiplicity_eq_coe] at h4
  exact_mod_cast h4

/- English proof (translation)
Use `haveI := IsCyclotomicExtension.finiteDimensional {M} E K`. Use `haveI := IsCyclotomicExtension.isGalois {M} E K`. Use `haveI : NumberField K := NumberField.of_module_finite E K`. Use `set H := (hζ.autToPow E).range with hH`. Establish `hcard : Nat.card H = Module.finrank E K`.

Rewrite using `[← IsGalois.card_aut_eq_finrank]`. Conclude with `(Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm`. Establish `htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K`. Rewrite using `[Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ, Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]`. Conclude with `minpoly.natDegree_le ζ`.

Establish `hidx : H.index * Nat.card H = M.totient`. Rewrite using `[Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]`. Establish `hle : H.index ≤ Module.finrank ℚ E`. Rewrite `htot` using `[← hidx, hcard]`. Conclude with `Nat.le_of_mul_le_mul_right htot Module.finrank_pos`.

Establish `hdvd : H.index ∣ (Module.finrank ℚ E).factorial` using `Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle`. Establish `hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H`. Take `⟨c, hc⟩` from `hdvd`. Rewrite using `[hc, pow_mul]`. Conclude with `H.pow_mem (H.pow_index_mem _) c`.

Take `⟨τ, hτ⟩` from `hmem`. Use `⟨τ, ?_⟩` and prove the remaining obligations. Rewrite using `[← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]`. Conclude with `(pow_eq_pow_mod _ hζ.pow_eq_one).symm`.
-/
theorem exists_aut {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {g : ℕ}
    (hg : g.Coprime M) :
    ∃ τ : K ≃ₐ[E] K, τ ζ = ζ ^ (g ^ (Module.finrank ℚ E).factorial) := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  haveI : NumberField K := NumberField.of_module_finite E K
  set H := (hζ.autToPow E).range with hH
  have hcard : Nat.card H = Module.finrank E K := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm
  have htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K := by
    rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]
    exact minpoly.natDegree_le ζ
  have hidx : H.index * Nat.card H = M.totient := by
    rw [Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hle : H.index ≤ Module.finrank ℚ E := by
    rw [← hidx, hcard] at htot
    exact Nat.le_of_mul_le_mul_right htot Module.finrank_pos
  have hdvd : H.index ∣ (Module.finrank ℚ E).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle
  have hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact H.pow_mem (H.pow_index_mem _) c
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, ?_⟩
  rw [← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

/- English proof (translation)
Use `haveI := IsCyclotomicExtension.finiteDimensional {M} E K`. Use `haveI := IsCyclotomicExtension.isGalois {M} E K`. Establish `hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ'`. Introduce `σ σ' h`. Apply `hζ.autToPow_injective E` to reduce the goal to its premises.

Rewrite `h` using `[← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ']`. Conclude with `Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))`. Establish `hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ` using `fun σ => hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])`. Establish `hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1)`. Introduce `η hη`.

Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hη`. Rewrite using `[map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]`. Establish `hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w`. Introduce `σ`. Use `⟨σ w / w, ?_, by field_simp⟩` and prove the remaining obligations.

Rewrite using `[div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]`. Establish `hne : ∀ a : K, a ^ M = 1 → a ≠ 0`. Introduce and unpack `a ha rfl`. Rewrite `ha` using `[zero_pow (NeZero.ne M)]`. Conclude with `zero_ne_one ha`.

Take `⟨α, hαM, hα⟩` from `hcoc τ`. Establish `hα0` using `hne α hαM`. Establish `hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧ (τ ^ m) ζ = ζ ^ ((k + 1) ^ m)`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow, map_pow, hτ, hα, hroot α hαM, geom_sum_succ]`. Apply the tactic sequence `constructor <;> ring`. Establish `hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]`. Use linear arithmetic over natural numbers and integers.

Establish `hτn : τ ^ n = 1`. Apply `hext` to reduce the goal to its premises. Take `⟨c, hc⟩` from `hN`. Rewrite using `[(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]`. Simplify using the standard rewrite rules.

Establish `hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1`. Establish `h` using `(hiter n).1`. Rewrite `h` using `[hτn, AlgEquiv.one_apply]`. Conclude with `mul_right_cancel₀ hw0 (by rw [← h, one_mul])`. Establish `hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α`.

Introduce `σ`. Take `⟨a, haM, ha⟩` from `hcoc σ`. Establish `ha0` using `hne a haM`. Establish `h` using `congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)`. Simplify using `only [AlgEquiv.mul_apply] at h`.

Rewrite `h` using `[hα, ha, map_mul, map_mul, ha, hα, hroot a haM]`. Establish `hσα : σ α = a ^ k * α` using `mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)`. Rewrite using `[map_div₀, map_pow, hσα, ha, mul_pow]`. Clear the denominators using the available nonvanishing facts. Take `⟨v, hv⟩` from `(IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix`.

Conclude with `⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩`.
-/
theorem descent {E K : Type} [Field E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k n : ℕ}
    (τ : K ≃ₐ[E] K) (hτ : τ ζ = ζ ^ (k + 1))
    (hN : M ∣ (∑ i ∈ Finset.range n, (k + 1) ^ i) * k) {u : E} {w : K} (hw0 : w ≠ 0)
    (hw : w ^ M = algebraMap E K u) :
    ∃ (α : K) (v : E), α ^ M = 1 ∧ α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 ∧
      algebraMap E K v * α = w ^ k := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  have hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ' := by
    intro σ σ' h
    apply hζ.autToPow_injective E
    rw [← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ'] at h
    exact Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ := fun σ =>
    hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])
  have hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1) := by
    intro η hη
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
    rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]
  have hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w := by
    intro σ
    refine ⟨σ w / w, ?_, by field_simp⟩
    rw [div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]
  have hne : ∀ a : K, a ^ M = 1 → a ≠ 0 := by
    rintro a ha rfl
    rw [zero_pow (NeZero.ne M)] at ha
    exact zero_ne_one ha
  obtain ⟨α, hαM, hα⟩ := hcoc τ
  have hα0 := hne α hαM
  have hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧
      (τ ^ m) ζ = ζ ^ ((k + 1) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow,
        map_pow, hτ, hα, hroot α hαM, geom_sum_succ]
      constructor <;> ring
  have hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]; omega
  have hτn : τ ^ n = 1 := by
    apply hext
    obtain ⟨c, hc⟩ := hN
    rw [(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]
    simp
  have hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 := by
    have h := (hiter n).1
    rw [hτn, AlgEquiv.one_apply] at h
    exact mul_right_cancel₀ hw0 (by rw [← h, one_mul])
  have hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α := by
    intro σ
    obtain ⟨a, haM, ha⟩ := hcoc σ
    have ha0 := hne a haM
    have h := congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)
    simp only [AlgEquiv.mul_apply] at h
    rw [hα, ha, map_mul, map_mul, ha, hα, hroot a haM] at h
    have hσα : σ α = a ^ k * α :=
      mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)
    rw [map_div₀, map_pow, hσα, ha, mul_pow]
    field_simp
  obtain ⟨v, hv⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact ⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩

end CyclotomicKummerDescent

open CyclotomicKummerDescent in

/- English proof (translation)
Introduce `E _ _ l r hl`. Use `set m := (Module.finrank ℚ E).factorial with hm`. Establish `ht1 : 1 < (1 + l ^ 2) ^ m` using `Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)`. Take `⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1` from `⟨_, (Nat.sub_add_cancel ht1.le).symm⟩`. Establish `hk0 : k ≠ 0` using `by omega`.

Take `⟨s, e, he, hke⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one`. Establish `hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1`. Use `sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m` as an intermediate fact. Simplify using `using this`. Take `⟨hN1, hN2⟩` from `geom_sum_valuation hl ht1 hdiv r`.

Rewrite `hN1`, `hN2` using `[hk]`. Use `⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩` and prove the remaining obligations. Introduce `Ω _ _ ζ hζ u w hwK hw`. Use `haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩`. Establish `hint : IsIntegral E ζ` using `(hζ.isIntegral (NeZero.pos _)).tower_top`.

Use `set K := IntermediateField.adjoin E {ζ} with hK`. Use `haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by`. Express the relevant statement in the definitionally equal form `IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra`. Rewrite using `[hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]`. Conclude with `hζ.adjoin_isCyclotomicExtension E`.

Set `ζ' : K` to `⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩`. Establish `hζ' : IsPrimitiveRoot ζ' (l ^ (r + s))` using `IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective`. Set `w' : K` to `⟨w, hwK⟩`. Establish `hw' : w' ^ (l ^ (r + s)) = algebraMap E K u` using `Subtype.ext hw`. Break down `eq_or_ne u 0 with rfl | hu` into its components or cases.

Conclude with `⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩`. Establish `hw0 : w' ≠ 0`. Introduce `h`. Rewrite `hw'` using `[h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero]`. Conclude with `hu hw'`.

Establish `hg : (1 + l ^ 2).Coprime (l ^ (r + s))`. Apply `Nat.Coprime.pow_right` to reduce the goal to its premises. Rewrite using `[sq, Nat.coprime_add_mul_left_left]`. Conclude with `Nat.coprime_one_left l`. Take `⟨τ, hτ⟩` from `exists_aut (E := E) hζ' hg`.

Rewrite `hτ` using `[← hm, hk]`. Take `⟨α, v, hαM, hαN, hv⟩` from `descent hζ' (n := l ^ r) τ hτ (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'`. Establish `hαr : α ^ (l ^ r) = 1`. Take `⟨j, -, hj⟩` from `(Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)`. Establish `h1` using `orderOf_dvd_of_pow_eq_one hαN`.

Rewrite `h1` using `[hj]`. Establish `hjr : j ≤ r`. Assume the negation of the conclusion as `hc`. Conclude with `hN2 ((pow_dvd_pow l (by omega)).trans h1)`. Conclude with `orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)`.

Establish `hvu : v ^ (l ^ r) = u ^ e`. Apply `(algebraMap E K).injective` to reduce the goal to its premises. Establish `h` using `congrArg (· ^ (l ^ r)) hv`. Simplify using `only [mul_pow, hαr, mul_one] at h`. Rewrite using `[map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)`. Take `⟨a, b, hab⟩` from `hco`. Use `⟨v ^ a * u ^ b, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a, zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab, zpow_one]`.
-/
theorem exists_pow_descent_cyclotomic :
    ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u →
        ∃ v : E, v ^ (l ^ r) = u := by
  intro E _ _ l r hl
  set m := (Module.finrank ℚ E).factorial with hm
  have ht1 : 1 < (1 + l ^ 2) ^ m :=
    Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)
  obtain ⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1 := ⟨_, (Nat.sub_add_cancel ht1.le).symm⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨s, e, he, hke⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one
  have hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m
    simpa using this
  obtain ⟨hN1, hN2⟩ := geom_sum_valuation hl ht1 hdiv r
  rw [hk] at hN1 hN2
  refine ⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩
  intro Ω _ _ ζ hζ u w hwK hw
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hint : IsIntegral E ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  set K := IntermediateField.adjoin E {ζ} with hK
  haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by
    change IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra
    rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension E
  let ζ' : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζ' : IsPrimitiveRoot ζ' (l ^ (r + s)) :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let w' : K := ⟨w, hwK⟩
  have hw' : w' ^ (l ^ (r + s)) = algebraMap E K u := Subtype.ext hw
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩
  have hw0 : w' ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero] at hw'
    exact hu hw'
  have hg : (1 + l ^ 2).Coprime (l ^ (r + s)) := by
    apply Nat.Coprime.pow_right
    rw [sq, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left l
  obtain ⟨τ, hτ⟩ := exists_aut (E := E) hζ' hg
  rw [← hm, hk] at hτ
  obtain ⟨α, v, hαM, hαN, hv⟩ := descent hζ' (n := l ^ r) τ hτ
    (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'
  have hαr : α ^ (l ^ r) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)
    have h1 := orderOf_dvd_of_pow_eq_one hαN
    rw [hj] at h1
    have hjr : j ≤ r := by
      by_contra hc
      exact hN2 ((pow_dvd_pow l (by omega)).trans h1)
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)
  have hvu : v ^ (l ^ r) = u ^ e := by
    apply (algebraMap E K).injective
    have h := congrArg (· ^ (l ^ r)) hv
    simp only [mul_pow, hαr, mul_one] at h
    rw [map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨v ^ a * u ^ b, ?_⟩
  rw [mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab,
    zpow_one]

end GlobalTheory
