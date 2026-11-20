import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E`. Use `set n := f.natDegree with hn`. Establish `hvr : A.valuation r ≠ 0` using `(Valuation.ne_zero_iff _).mpr hr`. Establish `hvrn : A.valuation r ^ n ≠ 0` using `pow_ne_zero _ hvr`.

Establish `happ : ∀ i, ∃ e : E, A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n`. Introduce `i`. Distinguish the cases in `hb : β = 0`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Take `⟨e, he⟩` from `hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)`.

Conclude with `⟨e, by simpa [map_pow] using he⟩`. Use `⟨0, ?_⟩` and prove the remaining obligations. Simplify using `only [hb, map_zero, zero_pow hi.ne', mul_zero]`. Conclude with `zero_lt_iff.mpr hvrn`. Establish `hbi : β ^ i ≠ 0` using `pow_ne_zero _ hb`.

Take `⟨e, he⟩` from `hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i) (div_ne_zero (pow_ne_zero _ hr) hbi)`. Use `⟨e, ?_⟩` and prove the remaining obligations. Establish `hvb : A.valuation β ^ i ≠ 0`. Rewrite using `[← map_pow]`. Conclude with `(Valuation.ne_zero_iff _).mpr hbi`.

Rewrite `he` using `[map_div₀, map_pow, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Use `choose c hc using happ`. Set `p : E[X]` to `∑ i : Fin n, C (c i) * X ^ (i : ℕ)`. Establish `hp : p.degree < n` using `degree_sum_fin_lt _`.

Set `g : E[X]` to `X ^ n + p`. Establish `hgm : g.Monic` using `monic_X_pow_add hp`. Establish `hgd : g.natDegree = n` using `by show (X ^ n + p).natDegree = n`. Rewrite using `[natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]`. Establish `h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i` using `by conv_lhs => rw [hf.as_sum]`.

Simplify using `[eval_finset_sum, ← hn]`. Establish `hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i` using `by show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _`. Simplify using `only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]`. Establish `hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i`.

Establish `: aeval β g = aeval β g - f.eval β` using `by rw [hβ, sub_zero]`. Rewrite using `[this, hga, h0]`. Simplify using `[sub_mul, Finset.sum_sub_distrib]`. Establish `hvg : A.valuation (aeval β g) < A.valuation r ^ n`. Rewrite using `[hgβ]`.

Use `Valuation.map_sum_lt _ hvrn fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Conclude with `hc i`. Use `set G := g.map (algebraMap E Ω) with hG`. Establish `hGm : G.Monic` using `hgm.map _`.

Establish `hGd : G.natDegree = n` using `by rw [hG, natDegree_map, hgd]`. Establish `hprod : (G.roots.map fun a => X - C a).prod = G` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree`. Establish `hev : aeval β g = (G.roots.map fun a => β - a).prod`. Rewrite using `[aeval_def, ← eval_map, ← hG]`. Use `conv_lhs => rw [← hprod]`.

Rewrite using `[eval_multiset_prod, Multiset.map_map]`. Simplify using `[Function.comp_def]`. Establish `hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Establish `h1 : A.valuation r ^ n ≤ A.valuation (aeval β g)`. Rewrite using `[hev, map_multiset_prod, Multiset.map_map]`. Establish `hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n`. Rewrite using `[Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hcard]`. Use `_ ≤ _ := Multiset.pow_card_le_prod (by`. Introduce `x hx`. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.mp hx`. Conclude with `hcon a ha)`.

Conclude with `absurd hvg (not_lt.mpr h1)`. Take `⟨a, ha, hva⟩` from `hex`. Use `⟨g, hgm, hgd, a, ?_, ?_⟩` and prove the remaining obligations. Use `(mem_roots hGm.ne_zero).mp ha` as an intermediate fact. Rewrite using `[aeval_def, ← eval_map]`.

Conclude with `this`. Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis.
-/
theorem exists_monic_base_root_near : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  intro E Ω _ _ _ _ _ A hdense f hf hfix β hβ r hr
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set n := f.natDegree with hn
  have hvr : A.valuation r ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
  have hvrn : A.valuation r ^ n ≠ 0 := pow_ne_zero _ hvr
  have happ : ∀ i, ∃ e : E,
      A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i < A.valuation r ^ n := by
    intro i
    by_cases hb : β = 0
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · obtain ⟨e, he⟩ := hdense (f.coeff 0) (fun d hd => hfix d hd 0) (r ^ n) (pow_ne_zero _ hr)
        exact ⟨e, by simpa [map_pow] using he⟩
      · refine ⟨0, ?_⟩
        simp only [hb, map_zero, zero_pow hi.ne', mul_zero]
        exact zero_lt_iff.mpr hvrn
    · have hbi : β ^ i ≠ 0 := pow_ne_zero _ hb
      obtain ⟨e, he⟩ := hdense (f.coeff i) (fun d hd => hfix d hd i) (r ^ n / β ^ i)
        (div_ne_zero (pow_ne_zero _ hr) hbi)
      refine ⟨e, ?_⟩
      have hvb : A.valuation β ^ i ≠ 0 := by
        rw [← map_pow]; exact (Valuation.ne_zero_iff _).mpr hbi
      rw [map_div₀, map_pow, map_pow] at he
      calc A.valuation (algebraMap E Ω e - f.coeff i) * A.valuation β ^ i
          < A.valuation r ^ n / A.valuation β ^ i * A.valuation β ^ i :=
            mul_lt_mul_of_pos_right he (zero_lt_iff.mpr hvb)
        _ = A.valuation r ^ n := div_mul_cancel₀ _ hvb
  choose c hc using happ
  let p : E[X] := ∑ i : Fin n, C (c i) * X ^ (i : ℕ)
  have hp : p.degree < n := degree_sum_fin_lt _
  let g : E[X] := X ^ n + p
  have hgm : g.Monic := monic_X_pow_add hp
  have hgd : g.natDegree = n := by
    show (X ^ n + p).natDegree = n
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  have h0 : f.eval β = β ^ n + ∑ i ∈ Finset.range n, f.coeff i * β ^ i := by
    conv_lhs => rw [hf.as_sum]
    simp [eval_finset_sum, ← hn]
  have hga : aeval β g = β ^ n + ∑ i ∈ Finset.range n, algebraMap E Ω (c i) * β ^ i := by
    show aeval β (X ^ n + ∑ i : Fin n, C (c i) * X ^ (i : ℕ)) = _
    simp only [map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C]
    rw [Fin.sum_univ_eq_sum_range (fun i => algebraMap E Ω (c i) * β ^ i) n]
  have hgβ : aeval β g = ∑ i ∈ Finset.range n, (algebraMap E Ω (c i) - f.coeff i) * β ^ i := by
    have : aeval β g = aeval β g - f.eval β := by rw [hβ, sub_zero]
    rw [this, hga, h0]
    simp [sub_mul, Finset.sum_sub_distrib]
  have hvg : A.valuation (aeval β g) < A.valuation r ^ n := by
    rw [hgβ]
    refine Valuation.map_sum_lt _ hvrn fun i _ => ?_
    rw [map_mul, map_pow]; exact hc i
  set G := g.map (algebraMap E Ω) with hG
  have hGm : G.Monic := hgm.map _
  have hGd : G.natDegree = n := by rw [hG, natDegree_map, hgd]
  have hprod : (G.roots.map fun a => X - C a).prod = G :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hGm IsAlgClosed.card_roots_eq_natDegree
  have hev : aeval β g = (G.roots.map fun a => β - a).prod := by
    rw [aeval_def, ← eval_map, ← hG]
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, Multiset.map_map]
    simp [Function.comp_def]
  have hex : ∃ a ∈ G.roots, A.valuation (β - a) < A.valuation r := by
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation r ^ n ≤ A.valuation (aeval β g) := by
      rw [hev, map_multiset_prod, Multiset.map_map]
      have hcard : (G.roots.map (A.valuation ∘ fun a => β - a)).card = n := by
        rw [Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, hGd]
      calc A.valuation r ^ n = A.valuation r ^ (G.roots.map (A.valuation ∘ fun a => β - a)).card := by
            rw [hcard]
        _ ≤ _ := Multiset.pow_card_le_prod (by
            intro x hx
            obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
            exact hcon a ha)
    exact absurd hvg (not_lt.mpr h1)
  obtain ⟨a, ha, hva⟩ := hex
  refine ⟨g, hgm, hgd, a, ?_, ?_⟩
  · have := (mem_roots hGm.ne_zero).mp ha
    rw [aeval_def, ← eval_map]; exact this
  · rwa [Valuation.map_sub_swap]

end GlobalTheory.WeilDeligne
