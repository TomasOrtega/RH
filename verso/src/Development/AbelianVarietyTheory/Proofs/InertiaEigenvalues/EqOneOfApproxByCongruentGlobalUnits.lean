import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Use `haveI : Finite (R ⧸ Ideal.span {g})ˣ := Finite.of_injective (fun u => (u : R ⧸ Ideal.span {g})) (fun _ _ h => Units.ext h)`. Use `⟨Nat.card (R ⧸ Ideal.span {g})ˣ, Nat.card_pos, fun ε => ?_⟩` and prove the remaining obligations. Establish `h` using `pow_card_eq_one' (G := (R ⧸ Ideal.span {g})ˣ) (x := Units.map (Ideal.Quotient.mk _).toMonoidHom ε)`. Establish `h2 : Ideal.Quotient.mk (Ideal.span {g}) ((ε : R) ^ Nat.card (R ⧸ Ideal.span {g})ˣ - 1) = 0`. Use `congrArg Units.val h` as an intermediate fact.

Simplify using `only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one] at this`. Rewrite using `[map_sub, map_pow, this, map_one, sub_self]`. Rewrite `h2` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `h2`.
-/
theorem unit_pow_dvd_sub_one_of_finite {R : Type} [CommRing R] (g : R)
    [Finite (R ⧸ Ideal.span {g})] :
    ∃ m : ℕ, 0 < m ∧ ∀ ε : Rˣ, g ∣ (ε : R) ^ m - 1 := by
  haveI : Finite (R ⧸ Ideal.span {g})ˣ := Finite.of_injective (fun u => (u : R ⧸ Ideal.span {g})) (fun _ _ h => Units.ext h)
  refine ⟨Nat.card (R ⧸ Ideal.span {g})ˣ, Nat.card_pos, fun ε => ?_⟩
  have h := pow_card_eq_one' (G := (R ⧸ Ideal.span {g})ˣ) (x := Units.map (Ideal.Quotient.mk _).toMonoidHom ε)
  have h2 : Ideal.Quotient.mk (Ideal.span {g}) ((ε : R) ^ Nat.card (R ⧸ Ideal.span {g})ˣ - 1) = 0 := by
    have := congrArg Units.val h
    simp only [Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.val_one] at this
    rw [map_sub, map_pow, this, map_one, sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h2
  exact h2

end GlobalTheory

namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum in

/- English proof (translation)
Introduce `hCh E _ _ w x hx hap`. Establish `hE : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k` using `fun k => valuedAdicCompletion_eq_valuation' w k`. Use `set q : ℕ := Ideal.absNorm w.asIdeal with hqdef`. Establish `hq0 : q ≠ 0`. Rewrite using `[hqdef, Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `w.ne_bot`. Establish `hqmem : (q : 𝓞 E) ∈ w.asIdeal` using `Ideal.absNorm_mem _`. Use `set γ := w.intValuation (q : 𝓞 E) with hγdef`. Establish `hγ : γ < 1` using `(w.intValuation_lt_one_iff_mem _).2 hqmem`. Establish `key : ∀ n : ℕ, Valued.v (x - 1) ≤ γ ^ (n + 1)`.

Introduce `n`. Use `set g : 𝓞 E := (q : 𝓞 E) ^ (n + 1) with hgdef`. Establish `hg0 : g ≠ 0` using `pow_ne_zero _ (Nat.cast_ne_zero.2 hq0)`. Use `haveI : Finite (𝓞 E ⧸ Ideal.span {g}) := by`. Use `(Ideal.absNorm_ne_zero_iff _).1 ?_` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hg0`. Take `⟨m, hm, hmg⟩` from `unit_pow_dvd_sub_one_of_finite g`. Take `⟨a, ha0, hacop, hch⟩` from `hCh E m q hm (Nat.pos_of_ne_zero hq0)`. Establish `hanot : (a : 𝓞 E) ∉ w.asIdeal`.

Introduce `ha`. Take `⟨s, t, hst⟩` from `(Nat.isCoprime_iff_coprime.2 hacop).map (Int.castRingHom (𝓞 E))`. Apply `w.isPrime.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hst]`. Simplify using `only [eq_intCast, Int.cast_natCast]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hqmem)`. Establish `hva : w.intValuation (a : 𝓞 E) = 1` using `intValuation_eq_one_iff.2 hanot`. Establish `haE : (a : E) = algebraMap (𝓞 E) E (a : 𝓞 E)` using `(map_natCast _ _).symm`. Establish `ha0E : (a : E) ≠ 0` using `Nat.cast_ne_zero.2 ha0.ne'`. Establish `hvaE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (a : E) ≤ 1` using `fun v => by`.

Rewrite using `[haE, valuation_of_algebraMap]`. Conclude with `v.intValuation_le_one _`. Establish `hwaE : w.valuation E (a : E) = 1` using `by rw [haE, valuation_of_algebraMap]; exact hva`. Use `set t : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 E) E g) with htdef`. Establish `hvt : Valued.v t = γ ^ (n + 1)`.

Rewrite using `[htdef, hE, valuation_of_algebraMap, hgdef, map_pow]`. Establish `ht0 : t ≠ 0`. Introduce `h`. Use `hvt` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `(pow_ne_zero _ (by have hq0' : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq0; rw [hγdef]; exact w.intValuation_ne_zero _ hq0')) this.symm`. Take `⟨k, hkv, hkw⟩` from `hap a ha0 t ht0`. Rewrite `hkw` using `[hvt]`. Establish `hγn : γ ^ (n + 1) < 1` using `pow_lt_one₀ zero_le' hγ (Nat.succ_ne_zero n)`. Establish `hwk : w.valuation E (k : E) = 1`.

Rewrite using `[← hE, ← hx]`. Conclude with `Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hkw (hx ▸ hγn))`. Establish `hk1 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E) - 1) ≤ 1`. Introduce `v`. Distinguish the cases in `hv : v = w`.

Substitute `hv` using the available equality. Conclude with `Valuation.map_sub_le _ hwk.le (by rw [map_one])`. Establish `h1` using `(hkv v hv).1`. Establish `: (k : E) - 1 = ((k : E) - 1) / (a : E) * (a : E)` using `by field_simp`. Rewrite using `[this, map_mul]`.

Conclude with `mul_le_one' h1 (hvaE v)`. Establish `hkle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) ≤ 1`. Introduce `v`. Establish `: (k : E) = ((k : E) - 1) + 1` using `by ring`. Rewrite using `[this]; exact Valuation.map_add_le _ (hk1 v) (by rw [map_one])`.

Establish `hkile : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E)⁻¹) ≤ 1`. Introduce `v`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality. Rewrite using `[map_inv₀, hwk, inv_one]`.

Conclude with `(hkv v hv).2`. Take `⟨κ, hκ⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkle`. Take `⟨κ', hκ'⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkile`. Establish `hinj : Function.Injective (algebraMap (𝓞 E) E)` using `IsFractionRing.injective (𝓞 E) E`. Establish `hkk : κ * κ' = 1` using `hinj (by rw [map_mul, hκ, hκ', map_one, mul_inv_cancel₀ k.ne_zero])`.

Set `u : (𝓞 E)ˣ` to `⟨κ, κ', hkk, by rw [mul_comm]; exact hkk⟩`. Establish `hdivE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (((k : E) - 1) / (a : E)) ≤ 1`. Introduce `v`. Distinguish the cases in `hv : v = w`. Substitute `hv` using the available equality.

Rewrite using `[map_div₀, hwaE, div_one]`. Conclude with `hk1 _`. Conclude with `(hkv v hv).1`. Take `⟨y, hy⟩` from `mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hdivE`. Establish `hdvd : (a : 𝓞 E) ∣ (u : 𝓞 E) - 1`.

Use `⟨y, hinj ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 E) E (κ - 1) = algebraMap (𝓞 E) E ((a : 𝓞 E) * y)`. Rewrite using `[map_sub, map_one, hκ, map_mul, hy, ← haE]`. Clear the denominators using the available nonvanishing facts. Take `⟨ε, hε⟩` from `hch u hdvd`.

Establish `hgk : g ∣ κ - 1`. Use `hmg ε` as an intermediate fact. Rewrite `this` using `[← Units.val_pow_eq_pow_val, ← hε]`. Conclude with `this`. Establish `hwk1 : w.valuation E ((k : E) - 1) ≤ γ ^ (n + 1)`.

Take `⟨c, hc⟩` from `hgk`. Rewrite using `[← hκ, ← map_one (algebraMap (𝓞 E) E), ← map_sub, valuation_of_algebraMap, hc, map_mul]`. Establish `: w.intValuation g = γ ^ (n + 1)` using `by rw [hgdef, map_pow]`. Rewrite using `[this]`. Conclude with `mul_le_of_le_one_right' (w.intValuation_le_one c)`.

Establish `hsplit : x - 1 = -(algebraMap E (w.adicCompletion E) (k : E) - x) + algebraMap E (w.adicCompletion E) ((k : E) - 1)`. Rewrite using `[map_sub, map_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsplit]`. Use `Valuation.map_add_le _ ?_ ?_` and prove the remaining obligations.

Rewrite using `[Valuation.map_neg]`. Conclude with `hkw`. Rewrite using `[hE]`. Conclude with `hwk1`. Assume the negation of the conclusion as `hne`.

Establish `hne' : Valued.v (x - 1) ≠ 0` using `(Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hγ (Units.mk0 _ hne')`. Establish `h1` using `key n`. Establish `h2 : γ ^ (n + 1) ≤ γ ^ n` using `by rw [pow_succ]; exact mul_le_of_le_one_right' hγ.le`. Conclude with `absurd (lt_of_le_of_lt (h1.trans h2) hn) (lt_irrefl _)`.
-/
theorem eq_one_of_approx_by_congruent_units : ChevalleyUnits → ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : w.adicCompletion E), Valued.v x = 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → x = 1 := by
  intro hCh E _ _ w x hx hap
  have hE : ∀ k : E, Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    fun k => valuedAdicCompletion_eq_valuation' w k
  set q : ℕ := Ideal.absNorm w.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have hqmem : (q : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  set γ := w.intValuation (q : 𝓞 E) with hγdef
  have hγ : γ < 1 := (w.intValuation_lt_one_iff_mem _).2 hqmem
  have key : ∀ n : ℕ, Valued.v (x - 1) ≤ γ ^ (n + 1) := by
    intro n
    set g : 𝓞 E := (q : 𝓞 E) ^ (n + 1) with hgdef
    have hg0 : g ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hq0)
    haveI : Finite (𝓞 E ⧸ Ideal.span {g}) := by
      refine (Ideal.absNorm_ne_zero_iff _).1 ?_
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hg0
    obtain ⟨m, hm, hmg⟩ := unit_pow_dvd_sub_one_of_finite g
    obtain ⟨a, ha0, hacop, hch⟩ := hCh E m q hm (Nat.pos_of_ne_zero hq0)

    have hanot : (a : 𝓞 E) ∉ w.asIdeal := by
      intro ha
      obtain ⟨s, t, hst⟩ := (Nat.isCoprime_iff_coprime.2 hacop).map (Int.castRingHom (𝓞 E))
      apply w.isPrime.ne_top
      rw [Ideal.eq_top_iff_one, ← hst]
      simp only [eq_intCast, Int.cast_natCast]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hqmem)
    have hva : w.intValuation (a : 𝓞 E) = 1 := intValuation_eq_one_iff.2 hanot
    have haE : (a : E) = algebraMap (𝓞 E) E (a : 𝓞 E) := (map_natCast _ _).symm
    have ha0E : (a : E) ≠ 0 := Nat.cast_ne_zero.2 ha0.ne'
    have hvaE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (a : E) ≤ 1 := fun v => by
      rw [haE, valuation_of_algebraMap]; exact v.intValuation_le_one _
    have hwaE : w.valuation E (a : E) = 1 := by rw [haE, valuation_of_algebraMap]; exact hva
    set t : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 E) E g) with htdef
    have hvt : Valued.v t = γ ^ (n + 1) := by
      rw [htdef, hE, valuation_of_algebraMap, hgdef, map_pow]
    have ht0 : t ≠ 0 := by
      intro h; have := hvt; rw [h, map_zero] at this
      exact (pow_ne_zero _ (by have hq0' : (q : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hq0; rw [hγdef]; exact w.intValuation_ne_zero _ hq0')) this.symm
    obtain ⟨k, hkv, hkw⟩ := hap a ha0 t ht0
    rw [hvt] at hkw
    have hγn : γ ^ (n + 1) < 1 := pow_lt_one₀ zero_le' hγ (Nat.succ_ne_zero n)

    have hwk : w.valuation E (k : E) = 1 := by
      rw [← hE, ← hx]
      exact Valuation.map_eq_of_sub_lt _ (lt_of_le_of_lt hkw (hx ▸ hγn))
    have hk1 : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E) - 1) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv
        exact Valuation.map_sub_le _ hwk.le (by rw [map_one])
      · have h1 := (hkv v hv).1
        have : (k : E) - 1 = ((k : E) - 1) / (a : E) * (a : E) := by field_simp
        rw [this, map_mul]
        exact mul_le_one' h1 (hvaE v)
    have hkle : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (k : E) ≤ 1 := by
      intro v
      have : (k : E) = ((k : E) - 1) + 1 := by ring
      rw [this]; exact Valuation.map_add_le _ (hk1 v) (by rw [map_one])
    have hkile : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E ((k : E)⁻¹) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_inv₀, hwk, inv_one]
      · exact (hkv v hv).2
    obtain ⟨κ, hκ⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkle
    obtain ⟨κ', hκ'⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hkile
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := IsFractionRing.injective (𝓞 E) E
    have hkk : κ * κ' = 1 := hinj (by rw [map_mul, hκ, hκ', map_one, mul_inv_cancel₀ k.ne_zero])
    let u : (𝓞 E)ˣ := ⟨κ, κ', hkk, by rw [mul_comm]; exact hkk⟩
    have hdivE : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 := by
      intro v
      by_cases hv : v = w
      · subst hv; rw [map_div₀, hwaE, div_one]; exact hk1 _
      · exact (hkv v hv).1
    obtain ⟨y, hy⟩ := mem_integers_of_valuation_le_one (R := 𝓞 E) (K := E) _ hdivE
    have hdvd : (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 := by
      refine ⟨y, hinj ?_⟩
      show algebraMap (𝓞 E) E (κ - 1) = algebraMap (𝓞 E) E ((a : 𝓞 E) * y)
      rw [map_sub, map_one, hκ, map_mul, hy, ← haE]
      field_simp
    obtain ⟨ε, hε⟩ := hch u hdvd
    have hgk : g ∣ κ - 1 := by
      have := hmg ε
      rw [← Units.val_pow_eq_pow_val, ← hε] at this
      exact this
    have hwk1 : w.valuation E ((k : E) - 1) ≤ γ ^ (n + 1) := by
      obtain ⟨c, hc⟩ := hgk
      rw [← hκ, ← map_one (algebraMap (𝓞 E) E), ← map_sub, valuation_of_algebraMap, hc, map_mul]
      have : w.intValuation g = γ ^ (n + 1) := by rw [hgdef, map_pow]
      rw [this]
      exact mul_le_of_le_one_right' (w.intValuation_le_one c)
    have hsplit : x - 1 = -(algebraMap E (w.adicCompletion E) (k : E) - x)
        + algebraMap E (w.adicCompletion E) ((k : E) - 1) := by
      rw [map_sub, map_one]; ring
    rw [hsplit]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Valuation.map_neg]; exact hkw
    · rw [hE]; exact hwk1
  by_contra hne
  have hne' : Valued.v (x - 1) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hγ (Units.mk0 _ hne')
  have h1 := key n
  have h2 : γ ^ (n + 1) ≤ γ ^ n := by rw [pow_succ]; exact mul_le_of_le_one_right' hγ.le
  exact absurd (lt_of_le_of_lt (h1.trans h2) hn) (lt_irrefl _)

end GlobalTheory
