import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CoordDiv

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {c | ∀ v, c v ∈ HeightOneSpectrum.adicCompletionIntegers F v}
  mul_mem' := fun {a b} ha hb v => mul_mem (ha v) (hb v)
  one_mem' := fun v => one_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  add_mem' := fun {a b} ha hb v => add_mem (ha v) (hb v)
  zero_mem' := fun v => zero_mem (HeightOneSpectrum.adicCompletionIntegers F v)
  neg_mem' := fun {a} ha v => neg_mem (ha v)

/- English proof (translation)
Introduce `v`. Rewrite using `[FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]`. Conclude with `HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a`.
-/
theorem algebraMap_mem (a : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (a : F) ∈ intAdeles F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, RingOfIntegers.coe_eq_algebraMap]
  exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v a

/- English proof (translation)
Take `⟨a, ha⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by`. Establish `hv` using `h v`. Rewrite `hv` using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`. Conclude with `hv`. Conclude with `⟨a, ha⟩`.
-/
theorem exists_of_mem (k : F) (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) k ∈ intAdeles F) :
    ∃ a : 𝓞 F, (a : F) = k := by
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F k fun v => by
    have hv := h v
    rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at hv
    exact hv
  exact ⟨a, ha⟩

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e`. Rewrite using `[div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN', map_one, one_mul]`. Take `⟨a, ha⟩` from `exists_of_mem F _ (hk ▸ he)`. Establish `hx : (x : F) = N * (a : F)`.

Rewrite using `[ha]`. Clear the denominators using the available nonvanishing facts. Conclude with `⟨a, by exact_mod_cast hx⟩`.
-/
theorem dvd_of_eq (x : 𝓞 F) (N : ℕ) (hN : 0 < N) (e : FiniteAdeleRing (𝓞 F) F)
    (he : e ∈ intAdeles F)
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) (x : F) = (N : FiniteAdeleRing (𝓞 F) F) * e) :
    ∃ a : 𝓞 F, x = (N : 𝓞 F) * a := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hk : algebraMap F (FiniteAdeleRing (𝓞 F) F) ((x : F) / N) = e := by
    rw [div_eq_mul_inv, map_mul, h, mul_comm, ← mul_assoc,
      ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)) N, ← map_mul, inv_mul_cancel₀ hN',
      map_one, one_mul]
  obtain ⟨a, ha⟩ := exists_of_mem F _ (hk ▸ he)
  have hx : (x : F) = N * (a : F) := by
    rw [ha]
    field_simp
  exact ⟨a, by exact_mod_cast hx⟩

/- English proof (translation)
Establish `h2` using `congrArg (Algebra.norm ℤ) h`. Rewrite `h2` using `[map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z, show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap, Algebra.norm_algebraMap]`. Conclude with `(Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩`.
-/
theorem int_dvd (z : ℤ) (N : ℕ) (a : 𝓞 F) (h : (z : 𝓞 F) = (N : 𝓞 F) * a) : (N : ℤ) ∣ z := by

  have h2 := congrArg (Algebra.norm ℤ) h
  rw [map_mul, ← eq_intCast (algebraMap ℤ (𝓞 F)) z,
    show (N : 𝓞 F) = algebraMap ℤ (𝓞 F) (N : ℤ) by simp, Algebra.norm_algebraMap,
    Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').mp ⟨_, h2⟩

/- English proof (translation)
Introduce `F _ _ β _ ω r N hN hr hsum i`. Take `⟨e, he, hsum⟩` from `hsum`. Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.mpr hN.ne'`. Establish `hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F)`. Use `(isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))` as an intermediate fact.

Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F` using `fun j => algebraMap_mem F (ω j)`. Establish `hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F` using `fun z => intCast_mem _ z`. Use `choose z c hc hrc using fun j => hr j N hN`. Establish `hc' : ∀ j, c j ∈ intAdeles F` using `hc`.

Establish `hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) = ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F)`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]`. Take `⟨a, ha⟩` from `dvd_of_eq F (∑ j, z j • ω j) N hN (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F)) (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by`.

Rewrite using `[hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hrc j]`. Use the proof step `ring)`. Establish `hm : ∀ j, z j = N * ω.repr a j`.

Introduce `j`. Establish `h1` using `congrArg (fun y => ω.repr y j) ha`. Establish `h2 : (N : 𝓞 F) * a = (N : ℤ) • a` using `by rw [zsmul_eq_mul]; push_cast; rfl`. Simplify using `only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1`. Simplify using `using h1`.

Establish `key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j)`. Introduce `j`. Rewrite using `[hrc j, hm j]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩` and prove the remaining obligations. Introduce `M hM`. Take `⟨z', c', hc'', hr'⟩` from `hr i (M * N) (Nat.mul_pos hM hN)`. Establish `hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F` using `sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')`. Take `⟨a', ha'⟩` from `dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by`.

Establish `e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) = (z' : FiniteAdeleRing (𝓞 F) F)`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]`. Establish `e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c'`. Rewrite using `[hr']`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, key i]`. Use `push_cast`. Use the proof step `ring)`. Take `⟨t, ht⟩` from `int_dvd F z' N a' ha'`. Use `⟨t, c', hc'', hu.mul_left_cancel ?_⟩` and prove the remaining obligations.

Rewrite using `[← key i, hr', ht]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coord_divisible : ∀ (F : Type) [Field F] [NumberField F] (β : Type) [Fintype β] (ω : Module.Basis β ℤ (𝓞 F)) (r : β → FiniteAdeleRing (𝓞 F) F) (N : ℕ), 0 < N → (∀ i, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ r i = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c)) → (∃ e : FiniteAdeleRing (𝓞 F) F, (∀ v, (e : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ ∑ i, r i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (ω i : 𝓞 F) = (N : FiniteAdeleRing (𝓞 F) F) * e) → ∀ i, ∃ s : FiniteAdeleRing (𝓞 F) F, (∀ M : ℕ, 0 < M → ∃ (z : ℤ) (c : FiniteAdeleRing (𝓞 F) F), (∀ v, (c : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ s = (z : FiniteAdeleRing (𝓞 F) F) + (M : FiniteAdeleRing (𝓞 F) F) * c) ∧ r i = (N : FiniteAdeleRing (𝓞 F) F) * s := by
  intro F _ _ β _ ω r N hN hr hsum i
  obtain ⟨e, he, hsum⟩ := hsum
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'

  have hu : IsUnit (N : FiniteAdeleRing (𝓞 F) F) := by
    have := (isUnit_iff_ne_zero.mpr hN').map (algebraMap F (FiniteAdeleRing (𝓞 F) F))
    rwa [map_natCast] at this
  have hω : ∀ j, algebraMap F (FiniteAdeleRing (𝓞 F) F) ((ω j : 𝓞 F) : F) ∈ intAdeles F :=
    fun j => algebraMap_mem F (ω j)
  have hint : ∀ z : ℤ, (z : FiniteAdeleRing (𝓞 F) F) ∈ intAdeles F := fun z => intCast_mem _ z

  choose z c hc hrc using fun j => hr j N hN
  have hc' : ∀ j, c j ∈ intAdeles F := hc

  have hL : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((∑ j, z j • ω j : 𝓞 F)) : F) =
      ∑ j, (z j : FiniteAdeleRing (𝓞 F) F) * algebraMap F _ ((ω j : 𝓞 F) : F) := by
    rw [RingOfIntegers.coe_eq_algebraMap, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, map_zsmul, zsmul_eq_mul, RingOfIntegers.coe_eq_algebraMap]
  obtain ⟨a, ha⟩ := dvd_of_eq F (∑ j, z j • ω j) N hN
    (e - ∑ j, c j * algebraMap F _ ((ω j : 𝓞 F) : F))
    (sub_mem he (sum_mem fun j _ => mul_mem (hc' j) (hω j))) (by
      rw [hL, mul_sub, Finset.mul_sum, ← hsum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hrc j]
      ring)

  have hm : ∀ j, z j = N * ω.repr a j := by
    intro j
    have h1 := congrArg (fun y => ω.repr y j) ha
    have h2 : (N : 𝓞 F) * a = (N : ℤ) • a := by rw [zsmul_eq_mul]; push_cast; rfl
    simp only [ω.repr_sum_self, h2, map_zsmul, Finsupp.smul_apply, smul_eq_mul] at h1
    simpa using h1
  have key : ∀ j, r j = N * ((ω.repr a j : FiniteAdeleRing (𝓞 F) F) + c j) := by
    intro j
    rw [hrc j, hm j]
    push_cast
    ring
  refine ⟨(ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i, ?_, key i⟩
  intro M hM

  obtain ⟨z', c', hc'', hr'⟩ := hr i (M * N) (Nat.mul_pos hM hN)
  have hs : (ω.repr a i : FiniteAdeleRing (𝓞 F) F) + c i - M * c' ∈ intAdeles F :=
    sub_mem (add_mem (hint _) (hc' i)) (mul_mem (natCast_mem _ M) hc'')
  obtain ⟨a', ha'⟩ := dvd_of_eq F (z' : 𝓞 F) N hN _ hs (by
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((z' : 𝓞 F)) : F) =
        (z' : FiniteAdeleRing (𝓞 F) F) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_intCast, map_intCast]
    have e2 : (z' : FiniteAdeleRing (𝓞 F) F) = r i - ((M * N : ℕ) : FiniteAdeleRing (𝓞 F) F) * c' := by
      rw [hr']
      ring
    rw [e1, e2, key i]
    push_cast
    ring)
  obtain ⟨t, ht⟩ := int_dvd F z' N a' ha'
  refine ⟨t, c', hc'', hu.mul_left_cancel ?_⟩
  rw [← key i, hr', ht]
  push_cast
  ring

end GlobalTheory.CoordDiv
