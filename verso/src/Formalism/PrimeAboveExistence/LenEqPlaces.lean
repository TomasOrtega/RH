import Formalism.ConjugateSelfDual.Statement

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.VB.Cmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

/- English proof (translation)
Establish `hv : A.valuation.Integers A` using `⟨Subtype.val_injective, fun a => A.valuation_le_one a, fun {r} hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩⟩`. Establish `hx : IsIntegral ℤ (algebraMap K Ω' (x : K))` using `(NumberField.RingOfIntegers.isIntegral_coe x).algebraMap`. Conclude with `hv.isIntegral_iff_v_le_one.1 hx.tower_top`.
-/
theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hv : A.valuation.Integers A :=
    ⟨Subtype.val_injective, fun a => A.valuation_le_one a,
      fun {r} hr => ⟨⟨r, A.mem_of_valuation_le_one r hr⟩, rfl⟩⟩
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap
  exact hv.isIntegral_iff_v_le_one.1 hx.tower_top

def ltIdeal : Ideal (𝓞 K) where
  carrier := {x | A.valuation (algebraMap K Ω' (x : K)) < 1}
  add_mem' := by
    intro a b ha hb
    have e : ((a + b : 𝓞 K) : K) = (a : K) + (b : K) := by norm_cast
    show A.valuation (algebraMap K Ω' ((a + b : 𝓞 K) : K)) < 1
    rw [e, map_add]
    exact Valuation.map_add_lt _ ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    have e : ((c • x : 𝓞 K) : K) = (c : K) * (x : K) := by rw [smul_eq_mul]; norm_cast
    show A.valuation (algebraMap K Ω' ((c • x : 𝓞 K) : K)) < 1
    rw [e, map_mul, map_mul]
    calc A.valuation (algebraMap K Ω' (c : K)) * A.valuation (algebraMap K Ω' (x : K))
        ≤ 1 * A.valuation (algebraMap K Ω' (x : K)) := mul_le_mul_of_nonneg_right (val_le_one A c) zero_le'
      _ = A.valuation (algebraMap K Ω' (x : K)) := one_mul _
      _ < 1 := hx

/- English proof (translation)
Conclude with `Iff.rfl`.
-/
theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by exact Iff.rfl

/- English proof (translation)
Establish `hprime : (ltIdeal (K` using `K) A).IsPrime := by`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, mem_ltIdeal]`. Simplify using the standard rewrite rules. Introduce `x y hxy`.

Rewrite `hxy` using `[mem_ltIdeal]`. Rewrite using `[mem_ltIdeal, mem_ltIdeal]`. Establish `e : ((x * y : 𝓞 K) : K) = (x : K) * (y : K)` using `by norm_cast`. Rewrite `hxy` using `[e, map_mul, map_mul]`. Break down `lt_or_eq_of_le (val_le_one A x) with hx | hx` into its components or cases.

Conclude with `Or.inl hx`. Break down `lt_or_eq_of_le (val_le_one A y) with hy | hy` into its components or cases. Conclude with `Or.inr hy`. Rewrite `hxy` using `[hx, hy, one_mul]`. Conclude with `absurd hxy (lt_irrefl 1)`.

Establish `hmem : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K` using `K) A := by`. Rewrite using `[mem_ltIdeal]`. Simplify using `using h`. Establish `hne : ((n : ℕ) : 𝓞 K) ≠ 0` using `by exact_mod_cast hn.ne'`. Use `⟨⟨ltIdeal (K := K) A, hprime, fun hbot => hne (Ideal.mem_bot.1 (hbot ▸ hmem))⟩, fun x => (mem_ltIdeal A x).symm, fun x => mem_ltIdeal A x⟩` and prove the remaining obligations.
-/
private theorem exists_placeOver_of_valuation_natCast_lt_one (n : ℕ) (hn : 0 < n) (h : A.valuation (n : Ω') < 1) :
    ∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧
      ∀ x : 𝓞 K, x ∈ v.asIdeal ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := by
  have hprime : (ltIdeal (K := K) A).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, mem_ltIdeal]
      simp
    · intro x y hxy
      rw [mem_ltIdeal] at hxy
      rw [mem_ltIdeal, mem_ltIdeal]
      have e : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := by norm_cast
      rw [e, map_mul, map_mul] at hxy
      rcases lt_or_eq_of_le (val_le_one A x) with hx | hx
      · exact Or.inl hx
      rcases lt_or_eq_of_le (val_le_one A y) with hy | hy
      · exact Or.inr hy
      rw [hx, hy, one_mul] at hxy
      exact absurd hxy (lt_irrefl 1)
  have hmem : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
    rw [mem_ltIdeal]
    simpa using h
  have hne : ((n : ℕ) : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne'
  refine ⟨⟨ltIdeal (K := K) A, hprime, fun hbot => hne (Ideal.mem_bot.1 (hbot ▸ hmem))⟩,
    fun x => (mem_ltIdeal A x).symm, fun x => mem_ltIdeal A x⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hl⟩`. Establish `h` using `(hv _).2 hl`. Simplify using `using h`. Introduce `h`.

Take `⟨v, hv, hmem⟩` from `exists_placeOver_of_valuation_natCast_lt_one (K := K) A l (Fact.out : l.Prime).pos h`. Conclude with `⟨v, hv, (hmem _).2 (by simpa using h)⟩`.
-/
theorem exists_over_above_iff (l : ℕ) [Fact l.Prime] :
    (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v ∧ ((l : ℕ) : 𝓞 K) ∈ v.asIdeal) ↔
      A.valuation (l : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv, hl⟩
    have h := (hv _).2 hl
    simpa using h
  · intro h
    obtain ⟨v, hv, hmem⟩ := exists_placeOver_of_valuation_natCast_lt_one (K := K) A l (Fact.out : l.Prime).pos h
    exact ⟨v, hv, (hmem _).2 (by simpa using h)⟩

end Formalism.VB.Cmp
