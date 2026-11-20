import Formalism.ConjugateSelfDual.Statement
import Formalism.ConjugateSelfDual.StatementRest

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.MainNotions.V.Pf.ShaCmp

variable {K Ω' : Type*} [Field K] [NumberField K] [Field Ω'] [Algebra K Ω'] (A : ValuationSubring Ω')

/- English proof (translation)
Establish `hx : IsIntegral ℤ (algebraMap K Ω' (x : K))` using `(x.2.map (IsScalarTower.toAlgHom ℤ K Ω'))`. Establish `hA : IsIntegral A (algebraMap K Ω' (x : K))` using `hx.tower_top`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hA`. Rewrite using `[← ha]`. Conclude with `(A.valuation_le_one_iff _).mpr a.2`.
-/
theorem val_le_one (x : 𝓞 K) : A.valuation (algebraMap K Ω' (x : K)) ≤ 1 := by
  have hx : IsIntegral ℤ (algebraMap K Ω' (x : K)) :=
    (x.2.map (IsScalarTower.toAlgHom ℤ K Ω'))
  have hA : IsIntegral A (algebraMap K Ω' (x : K)) := hx.tower_top
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hA
  rw [← ha]
  exact (A.valuation_le_one_iff _).mpr a.2

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
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ltIdeal (x : 𝓞 K) : x ∈ ltIdeal (K := K) A ↔ A.valuation (algebraMap K Ω' (x : K)) < 1 := Iff.rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv⟩`. Use `⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩` and prove the remaining obligations. Establish `h1` using `(hv (Ideal.absNorm v.asIdeal : 𝓞 K)).mpr (Ideal.absNorm_mem v.asIdeal)`. Simplify using `using h1`.

Introduce and unpack `⟨n, hn, hv⟩`. Establish `hP : (ltIdeal (K` using `K) A).IsPrime := by`. Use `⟨fun h => ?_, fun {x y} hxy => ?_⟩` and prove the remaining obligations. Establish `h1 : (1 : 𝓞 K) ∈ ltIdeal (K` using `K) A := by rw [h]; trivial`. Rewrite `h1` using `[mem_ltIdeal]`.

Simplify using `at h1`. Rewrite using `[mem_ltIdeal, mem_ltIdeal]`. Rewrite `hxy` using `[mem_ltIdeal]`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `hx1 : A.valuation (algebraMap K Ω' (x : K)) = 1` using `le_antisymm (val_le_one A x) hc.1`. Establish `hy1 : A.valuation (algebraMap K Ω' (y : K)) = 1` using `le_antisymm (val_le_one A y) hc.2`. Establish `e : ((x * y : 𝓞 K) : K) = (x : K) * (y : K)` using `by norm_cast`. Rewrite `hxy` using `[e, map_mul, map_mul, hx1, hy1, one_mul]`. Conclude with `lt_irrefl _ hxy`.

Establish `hne : ltIdeal (K` using `K) A ≠ ⊥ := by`. Introduce `h`. Establish `h1 : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K` using `K) A := by`. Rewrite using `[mem_ltIdeal]`. Simplify using `using hv`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `(Nat.cast_ne_zero.mpr hn.ne') h1`. Conclude with `⟨⟨ltIdeal A, hP, hne⟩, fun x => Iff.rfl⟩`.
-/
theorem exists_over_iff : (∃ v : HeightOneSpectrum (𝓞 K), Formalism.ConjugateSelfDual.IsPlaceOver A v) ↔
    ∃ n : ℕ, 0 < n ∧ A.valuation (n : Ω') < 1 := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨Ideal.absNorm v.asIdeal, Nat.pos_of_ne_zero fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h), ?_⟩
    have h1 := (hv (Ideal.absNorm v.asIdeal : 𝓞 K)).mpr (Ideal.absNorm_mem v.asIdeal)
    simpa using h1
  · rintro ⟨n, hn, hv⟩
    have hP : (ltIdeal (K := K) A).IsPrime := by
      refine ⟨fun h => ?_, fun {x y} hxy => ?_⟩
      · have h1 : (1 : 𝓞 K) ∈ ltIdeal (K := K) A := by rw [h]; trivial
        rw [mem_ltIdeal] at h1
        simp at h1
      · rw [mem_ltIdeal, mem_ltIdeal]
        rw [mem_ltIdeal] at hxy
        by_contra hc
        push_neg at hc
        have hx1 : A.valuation (algebraMap K Ω' (x : K)) = 1 := le_antisymm (val_le_one A x) hc.1
        have hy1 : A.valuation (algebraMap K Ω' (y : K)) = 1 := le_antisymm (val_le_one A y) hc.2
        have e : ((x * y : 𝓞 K) : K) = (x : K) * (y : K) := by norm_cast
        rw [e, map_mul, map_mul, hx1, hy1, one_mul] at hxy
        exact lt_irrefl _ hxy
    have hne : ltIdeal (K := K) A ≠ ⊥ := by
      intro h
      have h1 : ((n : ℕ) : 𝓞 K) ∈ ltIdeal (K := K) A := by
        rw [mem_ltIdeal]; simpa using hv
      rw [h, Ideal.mem_bot] at h1
      exact (Nat.cast_ne_zero.mpr hn.ne') h1
    exact ⟨⟨ltIdeal A, hP, hne⟩, fun x => Iff.rfl⟩

end Formalism.MainNotions.V.Pf.ShaCmp
