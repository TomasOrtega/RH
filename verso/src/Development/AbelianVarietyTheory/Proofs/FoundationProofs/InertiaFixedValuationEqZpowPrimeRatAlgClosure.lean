import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsDirichletCharacterSmoothed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDiscreteValuationRingFixedFieldInertia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerOfValuationRingFixedFieldInertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col

namespace GlobalTheory.InertiaFixedValue

open GlobalTheory.Published.AbVarRed IsLocalRing

/- English proof (translation)
Take `⟨v, hv, hl⟩` from `h`. Establish `hlZ : ((l : ℤ) : 𝓞 ℚ) ∈ v.asIdeal` using `by rw [Int.cast_natCast]; exact hl`. Establish `hiff : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (l : ℤ) ∣ n`. Prove the components needed by the constructor for the conclusion. Introduce `hn`.

Assume the negation of the conclusion as `hnd`. Establish `hpr : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)`. Take `⟨a, b, hab⟩` from `(Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd`. Apply `v.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`.

Establish `e : ((a * l + b * n : ℤ) : 𝓞 ℚ) = 1` using `by rw [hab, Int.cast_one]`. Rewrite using `[← e]`. Use `push_cast`. Conclude with `v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hlZ) (v.asIdeal.mul_mem_left _ hn)`. Introduce and unpack `⟨m, rfl⟩`.

Use `push_cast`. Conclude with `v.asIdeal.mul_mem_right _ (by exact_mod_cast hlZ)`. Rewrite using `[← hiff, ← hv (n : 𝓞 ℚ)]`. Simplify using the standard rewrite rules.
-/
theorem valuation_intCast_lt_one_iff {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (n : ℤ) : A.valuation (n : Ω) < 1 ↔ (l : ℤ) ∣ n := by
  obtain ⟨v, hv, hl⟩ := h
  have hlZ : ((l : ℤ) : 𝓞 ℚ) ∈ v.asIdeal := by rw [Int.cast_natCast]; exact hl
  have hiff : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ (l : ℤ) ∣ n := by
    constructor
    · intro hn
      by_contra hnd
      have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
      obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hpr.irreducible).2 hnd
      apply v.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((a * l + b * n : ℤ) : 𝓞 ℚ) = 1 := by rw [hab, Int.cast_one]
      rw [← e]
      push_cast
      exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left _ hlZ) (v.asIdeal.mul_mem_left _ hn)
    · rintro ⟨m, rfl⟩
      push_cast
      exact v.asIdeal.mul_mem_right _ (by exact_mod_cast hlZ)
  rw [← hiff, ← hv (n : 𝓞 ℚ)]
  simp

/- English proof (translation)
The claim follows from `le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A z)) (not_lt.1 fun hlt => hz ((valuation_intCast_lt_one_iff h z).1 hlt))`.
-/
private theorem valuation_intCast_eq_one_of_not_dvd {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (z : ℤ) (hz : ¬ (l : ℤ) ∣ z) : A.valuation (z : Ω) = 1 :=
  le_antisymm ((A.valuation_le_one_iff _).2 (intCast_mem A z))
    (not_lt.1 fun hlt => hz ((valuation_intCast_lt_one_iff h z).1 hlt))

/- English proof (translation)
Introduce `hd`. Establish `hn : ¬ (l : ℤ) ∣ q.num`. Introduce `hn`. Establish `h1 : l ∣ q.num.natAbs` using `Int.ofNat_dvd_left.1 hn`. Establish `h2 : l ∣ q.den` using `by exact_mod_cast hd`.

Establish `h3 : l ∣ 1`. Use `Nat.dvd_gcd h1 h2` as an intermediate fact. Rewrite `this` using `[Nat.Coprime.gcd_eq_one q.reduced]`. Then use the resulting hypothesis. Conclude with `(Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h3)`. Establish `e0 : algebraMap ℚ Ω q * ((q.den : ℤ) : Ω) = (q.num : Ω)`.

Rewrite using `[← map_intCast (algebraMap ℚ Ω) (q.den : ℤ), ← map_intCast (algebraMap ℚ Ω) q.num, ← map_mul]`. Use `congr 1`. Rewrite using `[Int.cast_natCast]`. Conclude with `Rat.mul_den_eq_num q`. Establish `e : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) = 1`.

Rewrite using `[← map_mul, e0, valuation_intCast_eq_one_of_not_dvd h _ hn]`. Establish `hlt : A.valuation ((q.den : ℤ) : Ω) < 1` using `(valuation_intCast_lt_one_iff h _).2 hd`. Establish `hlt1 : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) < 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite `hlt1` using `[e]`.

Conclude with `lt_irrefl _ hlt1`.
-/
private theorem not_dvd_den_of_valuation_le_one {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
    {A : ValuationSubring Ω} (h : OverL l A) (q : ℚ) (hq : A.valuation (algebraMap ℚ Ω q) ≤ 1) :
    ¬ (l : ℤ) ∣ (q.den : ℤ) := by
  intro hd

  have hn : ¬ (l : ℤ) ∣ q.num := by
    intro hn
    have h1 : l ∣ q.num.natAbs := Int.ofNat_dvd_left.1 hn
    have h2 : l ∣ q.den := by exact_mod_cast hd
    have h3 : l ∣ 1 := by
      have := Nat.dvd_gcd h1 h2
      rwa [Nat.Coprime.gcd_eq_one q.reduced] at this
    exact (Fact.out : l.Prime).ne_one (Nat.dvd_one.1 h3)
  have e0 : algebraMap ℚ Ω q * ((q.den : ℤ) : Ω) = (q.num : Ω) := by
    rw [← map_intCast (algebraMap ℚ Ω) (q.den : ℤ), ← map_intCast (algebraMap ℚ Ω) q.num, ← map_mul]
    congr 1
    rw [Int.cast_natCast]
    exact Rat.mul_den_eq_num q
  have e : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) = 1 := by
    rw [← map_mul, e0, valuation_intCast_eq_one_of_not_dvd h _ hn]
  have hlt : A.valuation ((q.den : ℤ) : Ω) < 1 := (valuation_intCast_lt_one_iff h _).2 hd
  have hlt1 : A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω) < 1 :=
    calc A.valuation (algebraMap ℚ Ω q) * A.valuation ((q.den : ℤ) : Ω)
        ≤ 1 * A.valuation ((q.den : ℤ) : Ω) := by gcongr
      _ = A.valuation ((q.den : ℤ) : Ω) := one_mul _
      _ < 1 := hlt
  rw [e] at hlt1
  exact lt_irrefl _ hlt1

/- English proof (translation)
Unfold `IsAbove`. Establish `hcast : ∀ z : ℤ, algebraMap R ℚ (algebraMap ℤ R z) = z` using `fun z => eq_intCast ((algebraMap R ℚ).comp (algebraMap ℤ R)) z`. Establish `hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ)` using `fun s hd => Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)`. Establish `hmk : ∀ (a : ℤ) (s : (Ideal.span {(l : ℤ)}).primeCompl), algebraMap R ℚ (IsLocalization.mk' R a s) = (a : ℚ) / ((s : ℤ) : ℚ)`. Introduce `a s`.

Establish `hne : ((s : ℤ) : ℚ) ≠ 0`. Establish `: (s : ℤ) ≠ 0` using `fun h0 => hs0 s (h0 ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Rewrite using `[eq_div_iff hne, ← hcast a, ← hcast (s : ℤ), ← map_mul, IsLocalization.mk'_spec]`. Use extensionality with `x`.

Rewrite using `[Subring.mem_comap, RingHom.mem_range]`. Express the relevant statement in the definitionally equal form `algebraMap ℚ Ω x ∈ A ↔ _`. Rewrite using `[← A.valuation_le_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hden` using `not_dvd_den_of_valuation_le_one h x hx`. Use `⟨IsLocalization.mk' R x.num ⟨(x.den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hmk]`. Use `push_cast`. Conclude with `Rat.num_div_den x`.

Introduce and unpack `⟨r, rfl⟩`. Take `⟨⟨a, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Ideal.span {(l : ℤ)}).primeCompl r`. Rewrite using `[hmk, map_div₀, map_intCast, map_intCast, map_div₀, valuation_intCast_eq_one_of_not_dvd h _ (hs0 s), div_one]`. Conclude with `(A.valuation_le_one_iff _).2 (intCast_mem A a)`.
-/
theorem isAbove_of_overL {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω}
    (h : OverL l A) (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R ℚ] [IsFractionRing R ℚ]
    [Algebra ℤ R] [(Ideal.span {(l : ℤ)}).IsPrime] [IsLocalization.AtPrime R (Ideal.span {(l : ℤ)})] :
    IsAbove R ℚ A.toSubring := by
  unfold IsAbove
  have hcast : ∀ z : ℤ, algebraMap R ℚ (algebraMap ℤ R z) = z := fun z =>
    eq_intCast ((algebraMap R ℚ).comp (algebraMap ℤ R)) z
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hmk : ∀ (a : ℤ) (s : (Ideal.span {(l : ℤ)}).primeCompl),
      algebraMap R ℚ (IsLocalization.mk' R a s) = (a : ℚ) / ((s : ℤ) : ℚ) := by
    intro a s
    have hne : ((s : ℤ) : ℚ) ≠ 0 := by
      have : (s : ℤ) ≠ 0 := fun h0 => hs0 s (h0 ▸ dvd_zero _)
      exact_mod_cast this
    rw [eq_div_iff hne, ← hcast a, ← hcast (s : ℤ), ← map_mul, IsLocalization.mk'_spec]
  ext x
  rw [Subring.mem_comap, RingHom.mem_range]
  change algebraMap ℚ Ω x ∈ A ↔ _
  rw [← A.valuation_le_one_iff]
  constructor
  · intro hx
    have hden := not_dvd_den_of_valuation_le_one h x hx
    refine ⟨IsLocalization.mk' R x.num
      ⟨(x.den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩, ?_⟩
    rw [hmk]
    push_cast
    exact Rat.num_div_den x
  · rintro ⟨r, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(l : ℤ)}).primeCompl r
    rw [hmk, map_div₀, map_intCast, map_intCast, map_div₀, valuation_intCast_eq_one_of_not_dvd h _ (hs0 s),
      div_one]
    exact (A.valuation_le_one_iff _).2 (intCast_mem A a)

/- English proof (translation)
Use `set p : Ω := algebraMap K Ω (algebraMap R K π) with hp`. Establish `hpF : p ∈ IntermediateField.fixedField (inertia K V)` using `IntermediateField.algebraMap_mem _ _`. Establish `hp0 : p ≠ 0`. Rewrite using `[hp, Ne, map_eq_zero_iff _ (algebraMap K Ω).injective, map_eq_zero_iff _ (IsFractionRing.injective R K)]`. Conclude with `hπ.ne_zero`.

Establish `hstep : ∀ n : ℕ, ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ≠ 0 → x ∈ V → x / p ^ n ∉ V → ∃ k : ℕ, V.valuation x = V.valuation p ^ k`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `x _ _ hxV hn`.

Rewrite `hn` using `[pow_zero, div_one]`. Conclude with `absurd hxV hn`. Consider the case `succ n ih`. Introduce `x hxF hx0 hxV hn`. Distinguish the cases in `hxu : x ∈ V.nonunits`.

Establish `hd : x / p ∈ V` using `GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ x hxF hxu`. Establish `hdn : x / p / p ^ n ∉ V` using `by rwa [div_div, ← pow_succ']`. Take `⟨k, hk⟩` from `ih (x / p) (div_mem hxF hpF) (div_ne_zero hx0 hp0) hd hdn`. Use `⟨k + 1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`. Conclude with `le_antisymm ((V.valuation_le_one_iff x).2 hxV) (not_lt.1 fun hlt => hxu (V.mem_nonunits_iff.2 hlt))`. Distinguish the cases in `hcV : c ∈ V`. Take `⟨n, hn⟩` from `GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c hc0`.

Take `⟨k, hk⟩` from `hstep n c hc hc0 hcV hn`. Conclude with `⟨k, by rw [hk, zpow_natCast]⟩`. Establish `hi : c⁻¹ ∈ V` using `(V.mem_or_inv_mem c).resolve_left hcV`. Take `⟨n, hn⟩` from `GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c⁻¹ (inv_ne_zero hc0)`. Take `⟨k, hk⟩` from `hstep n c⁻¹ (inv_mem hc) (inv_ne_zero hc0) hi hn`.

Use `⟨-(k : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[zpow_neg, zpow_natCast, ← hk, map_inv₀, inv_inv]`.
-/
theorem valuation_eq_zpow_of_fixed {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [PerfectField (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (V : ValuationSubring Ω) (hV : IsAbove R K V.toSubring) {π : R} (hπ : Irreducible π)
    {c : Ω} (hc0 : c ≠ 0) (hc : c ∈ IntermediateField.fixedField (inertia K V)) :
    ∃ k : ℤ, V.valuation c = V.valuation (algebraMap K Ω (algebraMap R K π)) ^ k := by
  set p : Ω := algebraMap K Ω (algebraMap R K π) with hp
  have hpF : p ∈ IntermediateField.fixedField (inertia K V) := IntermediateField.algebraMap_mem _ _
  have hp0 : p ≠ 0 := by
    rw [hp, Ne, map_eq_zero_iff _ (algebraMap K Ω).injective,
      map_eq_zero_iff _ (IsFractionRing.injective R K)]
    exact hπ.ne_zero

  have hstep : ∀ n : ℕ, ∀ x : Ω, x ∈ IntermediateField.fixedField (inertia K V) → x ≠ 0 → x ∈ V →
      x / p ^ n ∉ V → ∃ k : ℕ, V.valuation x = V.valuation p ^ k := by
    intro n
    induction n with
    | zero =>
      intro x _ _ hxV hn
      rw [pow_zero, div_one] at hn
      exact absurd hxV hn
    | succ n ih =>
      intro x hxF hx0 hxV hn
      by_cases hxu : x ∈ V.nonunits
      · have hd : x / p ∈ V := GlobalTheory.FixInertUnram.div_uniformizer_mem R K Ω V hV π hπ x hxF hxu
        have hdn : x / p / p ^ n ∉ V := by rwa [div_div, ← pow_succ']
        obtain ⟨k, hk⟩ := ih (x / p) (div_mem hxF hpF) (div_ne_zero hx0 hp0) hd hdn
        refine ⟨k + 1, ?_⟩
        calc V.valuation x = V.valuation (x / p * p) := by rw [div_mul_cancel₀ x hp0]
          _ = V.valuation p ^ (k + 1) := by rw [map_mul, hk, pow_succ]
      · refine ⟨0, ?_⟩
        rw [pow_zero]
        exact le_antisymm ((V.valuation_le_one_iff x).2 hxV)
          (not_lt.1 fun hlt => hxu (V.mem_nonunits_iff.2 hlt))
  by_cases hcV : c ∈ V
  · obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c hc0
    obtain ⟨k, hk⟩ := hstep n c hc hc0 hcV hn
    exact ⟨k, by rw [hk, zpow_natCast]⟩
  · have hi : c⁻¹ ∈ V := (V.mem_or_inv_mem c).resolve_left hcV
    obtain ⟨n, hn⟩ := GlobalTheory.not_mem_div_uniformizer_pow R K Ω V hV π hπ c⁻¹ (inv_ne_zero hc0)
    obtain ⟨k, hk⟩ := hstep n c⁻¹ (inv_mem hc) (inv_ne_zero hc0) hi hn
    refine ⟨-(k : ℤ), ?_⟩
    rw [zpow_neg, zpow_natCast, ← hk, map_inv₀, inv_inv]

/- English proof (translation)
Introduce `l _ Ω _ _ _ A hA c hc0 hc`. Establish `hpr : Prime (l : ℤ)` using `Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)`. Establish `hne : Ideal.span {(l : ℤ)} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `(Fact.out : l.Prime).ne_zero` after adjusting the coercions.

Establish `hM : (Ideal.span {(l : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpr.irreducible`. Establish `hP : (Ideal.span {(l : ℤ)}).IsPrime` using `hM.isPrime`. Use `set B := A.comap (algebraMap ℚ Ω) with hB`. Establish `hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ)` using `fun s hd => Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)`. Establish `hloc : IsLocalization.AtPrime B (Ideal.span {(l : ℤ)})`.

Use `⟨⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Establish `hs'` using `hs0 s`. Establish `hsq : ((s : ℤ) : ℚ) ≠ 0`. Establish `: (s : ℤ) ≠ 0` using `fun h0 => hs' (h0 ▸ dvd_zero _)`.

Conclude with `this` after adjusting the coercions. Establish `hinv : ((s : ℤ) : ℚ)⁻¹ ∈ B`. Rewrite using `[hB, ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, map_intCast, map_inv₀, valuation_intCast_eq_one_of_not_dvd hA _ hs', inv_one]`. Use `IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)` and prove the remaining obligations. Simplify using `[hsq]`.

Introduce `z`. Establish `hz : A.valuation (algebraMap ℚ Ω (z : ℚ)) ≤ 1` using `(A.valuation_le_one_iff _).2 (ValuationSubring.mem_comap.1 z.2)`. Establish `hden` using `not_dvd_den_of_valuation_le_one hA _ hz`. Use `⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [MulMemClass.coe_mul, eq_intCast, SubringClass.coe_intCast, Int.cast_natCast]`.

Conclude with `Rat.mul_den_eq_num _`. Introduce `x y hxy`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `hq : (x : ℚ) = y`. Use `congrArg (fun b : B => (b : ℚ)) hxy` as an intermediate fact.

Simplify using `using this`. Simplify using `only [OneMemClass.coe_one, one_mul]`. Conclude with `hq` after adjusting the coercions. Establish `: IsDiscreteValuationRing B` using `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hne B`. Establish `: NeZero l` using `⟨(Fact.out : l.Prime).ne_zero⟩`.

Establish `: Finite (ℤ ⧸ Ideal.span {(l : ℤ)})` using `Finite.of_equiv _ (Int.quotientSpanNatEquivZMod l).symm.toEquiv`. Establish `: Finite (ResidueField B)` using `Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(l : ℤ)}) B).toEquiv`. Establish `hAb : IsAbove B ℚ A.toSubring` using `isAbove_of_overL hA B`. Establish `hirr : Irreducible (algebraMap ℤ B l)`. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer, ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(l : ℤ)}) B, Ideal.map_span, Set.image_singleton]`.

Establish `hs : ∀ σ ∈ inertia ℚ A, σ ∈ Ine (F` using `ℚ) A := by`. Introduce `σ hσ`. Rewrite using `[mem_Ine]`. Unfold `inertia at hσ`. Take `⟨τ, hτ, rfl⟩` from `Subgroup.mem_map.1 hσ`.

Use `⟨τ.2, fun x hx => ?_⟩` and prove the remaining obligations. Use `set a : A := ⟨x, (A.valuation_le_one_iff x).1 hx⟩`. Establish `hfix : τ • IsLocalRing.residue A a = IsLocalRing.residue A a`. Use `congrArg (fun f => f (IsLocalRing.residue A a)) (MonoidHom.mem_ker.1 hτ)` as an intermediate fact. Simplify using `using this`.

Establish `h0 : IsLocalRing.residue A (τ • a - a) = 0`. Rewrite using `[map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]`. Establish `hm : τ • a - a ∈ IsLocalRing.maximalIdeal A` using `Ideal.Quotient.eq_zero_iff_mem.1 h0`. Conclude with `(A.valuation_lt_one_iff _).1 hm`. Establish `hfixc : c ∈ IntermediateField.fixedField (inertia ℚ A)` using `(IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hc σ (hs σ hσ)`.

Take `⟨k, hk⟩` from `valuation_eq_zpow_of_fixed A hAb hirr hc0 hfixc`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Simplify using the standard rewrite rules.
-/
theorem valuation_eq_zpow_of_ine_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω), OverL l A → ∀ c : Ω, c ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s c = c) →
    ∃ k : ℤ, A.valuation c = A.valuation (l : Ω) ^ k := by
  intro l _ Ω _ _ _ A hA c hc0 hc
  have hpr : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 (Fact.out : l.Prime)
  have hne : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hM : (Ideal.span {(l : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpr.irreducible
  have hP : (Ideal.span {(l : ℤ)}).IsPrime := hM.isPrime

  set B := A.comap (algebraMap ℚ Ω) with hB
  have hs0 : ∀ s : (Ideal.span {(l : ℤ)}).primeCompl, ¬ (l : ℤ) ∣ (s : ℤ) := fun s hd =>
    Ideal.mem_primeCompl_iff.1 s.2 (Ideal.mem_span_singleton.2 hd)
  have hloc : IsLocalization.AtPrime B (Ideal.span {(l : ℤ)}) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · intro s
      have hs' := hs0 s
      have hsq : ((s : ℤ) : ℚ) ≠ 0 := by
        have : (s : ℤ) ≠ 0 := fun h0 => hs' (h0 ▸ dvd_zero _)
        exact_mod_cast this
      have hinv : ((s : ℤ) : ℚ)⁻¹ ∈ B := by
        rw [hB, ValuationSubring.mem_comap, ← A.valuation_le_one_iff, map_inv₀, map_intCast, map_inv₀,
          valuation_intCast_eq_one_of_not_dvd hA _ hs', inv_one]
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      simp [hsq]
    · intro z
      have hz : A.valuation (algebraMap ℚ Ω (z : ℚ)) ≤ 1 :=
        (A.valuation_le_one_iff _).2 (ValuationSubring.mem_comap.1 z.2)
      have hden := not_dvd_den_of_valuation_le_one hA _ hz
      refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ),
        Ideal.mem_primeCompl_iff.2 fun hm => hden (Ideal.mem_span_singleton.1 hm)⟩⟩, Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, eq_intCast, SubringClass.coe_intCast, Int.cast_natCast]
      exact Rat.mul_den_eq_num _
    · intro x y hxy
      refine ⟨1, ?_⟩
      have hq : (x : ℚ) = y := by
        have := congrArg (fun b : B => (b : ℚ)) hxy
        simpa using this
      simp only [OneMemClass.coe_one, one_mul]
      exact_mod_cast hq
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ hne B
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have : Finite (ℤ ⧸ Ideal.span {(l : ℤ)}) := Finite.of_equiv _ (Int.quotientSpanNatEquivZMod l).symm.toEquiv
  have : Finite (ResidueField B) :=
    Finite.of_equiv _ (IsLocalization.AtPrime.equivQuotMaximalIdeal (Ideal.span {(l : ℤ)}) B).toEquiv
  have hAb : IsAbove B ℚ A.toSubring := isAbove_of_overL hA B
  have hirr : Irreducible (algebraMap ℤ B l) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(l : ℤ)}) B, Ideal.map_span,
      Set.image_singleton]

  have hs : ∀ σ ∈ inertia ℚ A, σ ∈ Ine (F := ℚ) A := by
    intro σ hσ
    rw [mem_Ine]
    unfold inertia at hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hσ
    refine ⟨τ.2, fun x hx => ?_⟩
    set a : A := ⟨x, (A.valuation_le_one_iff x).1 hx⟩
    have hfix : τ • IsLocalRing.residue A a = IsLocalRing.residue A a := by
      have := congrArg (fun f => f (IsLocalRing.residue A a)) (MonoidHom.mem_ker.1 hτ)
      simpa using this
    have h0 : IsLocalRing.residue A (τ • a - a) = 0 := by
      rw [map_sub, IsLocalRing.ResidueField.residue_smul, hfix, sub_self]
    have hm : τ • a - a ∈ IsLocalRing.maximalIdeal A := Ideal.Quotient.eq_zero_iff_mem.1 h0
    exact (A.valuation_lt_one_iff _).1 hm
  have hfixc : c ∈ IntermediateField.fixedField (inertia ℚ A) :=
    (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hc σ (hs σ hσ)
  obtain ⟨k, hk⟩ := valuation_eq_zpow_of_fixed A hAb hirr hc0 hfixc
  refine ⟨k, ?_⟩
  rw [hk]
  simp

end GlobalTheory.InertiaFixedValue
