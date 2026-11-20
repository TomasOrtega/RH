import Mathlib
open TensorProduct

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Establish `hirr : Irreducible (X ^ p - C (⟨z ^ p, hzp⟩ : L))`. Apply `X_pow_sub_C_irreducible_of_prime hp.out` to reduce the goal to its premises. Introduce `b hb`. Apply `hz` to reduce the goal to its premises. Establish `hb' : (b : K) ^ p = z ^ p`.

Use `congrArg (fun t : L => (t : K)) hb` as an intermediate fact. Simplify using `using this`. Establish `h0 : ((b : K) - z) ^ p = 0`. Rewrite using `[sub_pow_char, hb', sub_self]`. Establish `: (b : K) = z` using `sub_eq_zero.mp ((pow_eq_zero_iff hp.out.ne_zero).mp h0)`.

Rewrite using `[← this]`. Conclude with `b.2`. Establish `hmonic : (X ^ p - C (⟨z ^ p, hzp⟩ : L)).Monic` using `monic_X_pow_sub_C _ hp.out.ne_zero`. Establish `haeval : aeval z (X ^ p - C (⟨z ^ p, hzp⟩ : L)) = 0`. Simplify using `only [map_sub, map_pow, aeval_X, aeval_C]`.

Conclude with `sub_self _`. Establish `hint : IsIntegral L z` using `⟨_, hmonic, by rw [← aeval_def]; exact haeval⟩`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic hirr haeval hmonic, natDegree_X_pow_sub_C]`.
-/
theorem cfmax_finrank (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p]
    (L : Subfield K) (z : K) (hz : z ∉ L) (hzp : z ^ p ∈ L) :
    IsIntegral L z ∧ Module.finrank L (IntermediateField.adjoin L ({z} : Set K)) = p := by
  have hirr : Irreducible (X ^ p - C (⟨z ^ p, hzp⟩ : L)) := by
    apply X_pow_sub_C_irreducible_of_prime hp.out
    intro b hb
    apply hz
    have hb' : (b : K) ^ p = z ^ p := by
      have := congrArg (fun t : L => (t : K)) hb
      simpa using this
    have h0 : ((b : K) - z) ^ p = 0 := by
      rw [sub_pow_char, hb', sub_self]
    have : (b : K) = z := sub_eq_zero.mp ((pow_eq_zero_iff hp.out.ne_zero).mp h0)
    rw [← this]; exact b.2
  have hmonic : (X ^ p - C (⟨z ^ p, hzp⟩ : L)).Monic := monic_X_pow_sub_C _ hp.out.ne_zero
  have haeval : aeval z (X ^ p - C (⟨z ^ p, hzp⟩ : L)) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    exact sub_self _
  have hint : IsIntegral L z := ⟨_, hmonic, by rw [← aeval_def]; exact haeval⟩
  refine ⟨hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, ← minpoly.eq_of_irreducible_of_monic hirr haeval hmonic,
    natDegree_X_pow_sub_C]

/- English proof (translation)
Introduce `p _ K _ _ F hF f hf`. Establish `hch : ∀ c ⊆ {L : Subfield K | F ≤ L ∧ f ∉ L}, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {L : Subfield K | F ≤ L ∧ f ∉ L}, ∀ z ∈ c, z ≤ ub`. Introduce `c hc hchain y hy`. Use `⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), ?_⟩, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Rewrite using `[Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hchain.directedOn]`.

Introduce and unpack `⟨s, hs, hfs⟩`. Conclude with `(hc hs).2 hfs`. Take `⟨L, -, hmax⟩` from `zorn_le_nonempty₀ {L : Subfield K | F ≤ L ∧ f ∉ L} hch F ⟨le_rfl, hf⟩`. Use `⟨L, hmax.prop.1, hmax.prop.2, ?_⟩` and prove the remaining obligations. Establish `hpow : ∀ y : K, y ^ p ∈ L` using `fun y => hmax.prop.1 (hF y)`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Distinguish the cases in `hy : y ∈ L`. Conclude with `IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : L)`. Take `⟨hiy, hdy⟩` from `cfmax_finrank p K L y hy (hpow y)`.

Take `⟨_, hdf⟩` from `cfmax_finrank p K L f hmax.prop.2 (hpow f)`. Establish `hfy : f ∈ IntermediateField.adjoin L ({y} : Set K)`. Assume the negation of the conclusion as `hfy`. Establish `hLM : L ≤ (IntermediateField.adjoin L ({y} : Set K)).toSubfield` using `fun x hx => (IntermediateField.adjoin L ({y} : Set K)).algebraMap_mem (⟨x, hx⟩ : L)`. Establish `hM : (IntermediateField.adjoin L ({y} : Set K)).toSubfield ∈ {L : Subfield K | F ≤ L ∧ f ∉ L}` using `⟨hmax.prop.1.trans hLM, hfy⟩`.

Conclude with `hy (hmax.le_of_ge hM hLM (IntermediateField.mem_adjoin_simple_self L y))`. Establish `hle : IntermediateField.adjoin L ({f} : Set K) ≤ IntermediateField.adjoin L ({y} : Set K)` using `IntermediateField.adjoin_simple_le_iff.mpr hfy`. Use `haveI : FiniteDimensional L (IntermediateField.adjoin L ({y} : Set K)) := IntermediateField.adjoin.finiteDimensional hiy`. Establish `heq` using `IntermediateField.eq_of_le_of_finrank_eq hle (hdf.trans hdy.symm)`. Rewrite using `[heq]`.

Conclude with `IntermediateField.mem_adjoin_simple_self L y`.
-/
theorem cfmax_main : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (F : Subfield K), (∀ y : K, y ^ p ∈ F) → ∀ f : K, f ∉ F → ∃ L : Subfield K, F ≤ L ∧ f ∉ L ∧ IntermediateField.adjoin L ({f} : Set K) = ⊤ := by
  intro p _ K _ _ F hF f hf
  have hch : ∀ c ⊆ {L : Subfield K | F ≤ L ∧ f ∉ L}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {L : Subfield K | F ≤ L ∧ f ∉ L}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hchain y hy
    refine ⟨sSup c, ⟨(hc hy).1.trans (le_sSup hy), ?_⟩, fun z hz => le_sSup hz⟩
    rw [Subfield.mem_sSup_of_directedOn ⟨y, hy⟩ hchain.directedOn]
    rintro ⟨s, hs, hfs⟩
    exact (hc hs).2 hfs
  obtain ⟨L, -, hmax⟩ := zorn_le_nonempty₀ {L : Subfield K | F ≤ L ∧ f ∉ L} hch F ⟨le_rfl, hf⟩
  refine ⟨L, hmax.prop.1, hmax.prop.2, ?_⟩
  have hpow : ∀ y : K, y ^ p ∈ L := fun y => hmax.prop.1 (hF y)
  rw [eq_top_iff]
  intro y _
  by_cases hy : y ∈ L
  · exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : L)
  · obtain ⟨hiy, hdy⟩ := cfmax_finrank p K L y hy (hpow y)
    obtain ⟨_, hdf⟩ := cfmax_finrank p K L f hmax.prop.2 (hpow f)
    have hfy : f ∈ IntermediateField.adjoin L ({y} : Set K) := by
      by_contra hfy
      have hLM : L ≤ (IntermediateField.adjoin L ({y} : Set K)).toSubfield := fun x hx =>
        (IntermediateField.adjoin L ({y} : Set K)).algebraMap_mem (⟨x, hx⟩ : L)
      have hM : (IntermediateField.adjoin L ({y} : Set K)).toSubfield ∈
          {L : Subfield K | F ≤ L ∧ f ∉ L} := ⟨hmax.prop.1.trans hLM, hfy⟩
      exact hy (hmax.le_of_ge hM hLM (IntermediateField.mem_adjoin_simple_self L y))
    have hle : IntermediateField.adjoin L ({f} : Set K) ≤ IntermediateField.adjoin L ({y} : Set K) :=
      IntermediateField.adjoin_simple_le_iff.mpr hfy
    haveI : FiniteDimensional L (IntermediateField.adjoin L ({y} : Set K)) :=
      IntermediateField.adjoin.finiteDimensional hiy
    have heq := IntermediateField.eq_of_le_of_finrank_eq hle (hdf.trans hdy.symm)
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self L y

end GlobalTheory
