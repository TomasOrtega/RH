import Mathlib
import GroundTheory.AutomorphicForms.HarishChandraCentre.MemOfMemSupportToFinsupp
import GroundTheory.AutomorphicForms.HarishChandraCentre.RhoOneEqZeroOfRhoZeroEqZero

namespace GroundTheory.Automorphic.HarishChandra

attribute [local instance 100] LieRing.ofAssociativeRing

open MvPolynomial

variable {n : ℕ}

noncomputable def transposeExp (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ :=
  Finsupp.mapDomain Prod.swap m

/- English proof (translation)
The claim follows from `Finsupp.mapDomain_injective Prod.swap_injective`.
-/
theorem transposeExp_injective : Function.Injective (transposeExp (n := n)) :=
  Finsupp.mapDomain_injective Prod.swap_injective

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [transposeExp]`. Consider the case `cons a w ih`. Rewrite using `[List.map_cons, show ((Prod.swap a :: w.map Prod.swap : List _) : Multiset _) = {Prod.swap a} + ((w.map Prod.swap : List _) : Multiset _) by simp, show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp, Multiset.toFinsupp_add, Multiset.toFinsupp_add, Multiset.toFi …`.
-/
theorem toFinsupp_map_swap (w : List (Fin n × Fin n)) :
    Multiset.toFinsupp ((w.map Prod.swap : List _) : Multiset (Fin n × Fin n)) =
      transposeExp (Multiset.toFinsupp (w : Multiset (Fin n × Fin n))) := by
  induction w with
  | nil => simp [transposeExp]
  | cons a w ih =>
    rw [List.map_cons,
      show ((Prod.swap a :: w.map Prod.swap : List _) : Multiset _) =
        {Prod.swap a} + ((w.map Prod.swap : List _) : Multiset _) by simp,
      show ((a :: w : List _) : Multiset _) = {a} + (w : Multiset _) by simp,
      Multiset.toFinsupp_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton,
      Multiset.toFinsupp_singleton, ih, transposeExp, transposeExp, Finsupp.mapDomain_add,
      Finsupp.mapDomain_single]

/- English proof (translation)
Establish `h1` using `degree_toFinsupp ((expand m).map Prod.swap)`. Rewrite `h1` using `[toFinsupp_map_swap, toFinsupp_expand, List.length_map, length_expand]`. Conclude with `h1`.
-/
theorem degree_transposeExp (m : Fin n × Fin n →₀ ℕ) :
    (transposeExp m).degree = m.degree := by
  have h1 := degree_toFinsupp ((expand m).map Prod.swap)
  rw [toFinsupp_map_swap, toFinsupp_expand, List.length_map, length_expand] at h1
  exact h1

/- English proof (translation)
Rewrite using `[canon, constantCoeff_rho_one_word_monomial _ _ (by rw [length_expand, h]), toFinsupp_map_swap, toFinsupp_expand]`.
-/
theorem constantCoeff_rho_one_canon_monomial (m s : Fin n × Fin n →₀ ℕ) (h : m.degree = s.degree) :
    constantCoeff (rho 1 (canon m) (monomial s 1)) ≠ 0 ↔ transposeExp m = s := by
  rw [canon, constantCoeff_rho_one_word_monomial _ _ (by rw [length_expand, h]),
    toFinsupp_map_swap, toFinsupp_expand]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨m, hms, hm⟩` from `hne`. Use `set s' := s.filter fun m => c m ≠ 0`. Establish `hne' : s'.Nonempty` using `⟨m, Finset.mem_filter.2 ⟨hms, hm⟩⟩`.

Take `⟨m₀, hm₀, hmax⟩` from `s'.exists_max_image Finsupp.degree hne'`. Rewrite `hm₀` using `[Finset.mem_filter]`. Use `set N := transposeExp m₀`. Establish `hN : N.degree = m₀.degree` using `degree_transposeExp m₀`. Establish `hhom : (monomial N (1 : ℂ)).IsHomogeneous m₀.degree`.

Rewrite using `[← hN]`. Conclude with `isHomogeneous_monomial _ rfl`. Establish `key : ∀ m ∈ s, m ≠ m₀ → c m * constantCoeff (rho 1 (canon m) (monomial N 1)) = 0`. Introduce `m hm hne`. Distinguish the cases in `hc : c m = 0`.

Rewrite using `[hc, zero_mul]`. Establish `hdeg : m.degree ≤ m₀.degree` using `hmax m (Finset.mem_filter.2 ⟨hm, hc⟩)`. Break down `hdeg.lt_or_eq with hlt | heq` into its components or cases. Rewrite using `[canon, constantCoeff_rho_one_word_of_lt _ _ _ hhom (by rw [length_expand]; exact hlt), mul_zero]`. Establish `: ¬ constantCoeff (rho 1 (canon m) (monomial N 1)) ≠ 0`.

Rewrite using `[constantCoeff_rho_one_canon_monomial _ _ (by rw [heq, hN])]`. Conclude with `fun h' => hne (transposeExp_injective h')`. Rewrite using `[not_not.1 this, mul_zero]`. Establish `hsum` using `congrArg (fun T : Module.End ℂ (Poly n) => constantCoeff (T (monomial N 1))) h`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero, LinearMap.zero_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C] at hsum`.

Rewrite `hsum` using `[Finset.sum_eq_single m₀ (fun m hm hne => key m hm hne) (fun h' => absurd hm₀.1 h')]`. Establish `h0 : constantCoeff (rho 1 (canon m₀) (monomial N 1)) ≠ 0` using `(constantCoeff_rho_one_canon_monomial _ _ hN.symm).2 rfl`. Conclude with `hm₀.2 ((mul_eq_zero.1 hsum).resolve_right h0)`.
-/
theorem coeff_eq_zero_of_rho_one (s : Finset (Fin n × Fin n →₀ ℕ)) (c : (Fin n × Fin n →₀ ℕ) → ℂ)
    (h : rho 1 (∑ m ∈ s, c m • canon m) = 0) : ∀ m ∈ s, c m = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨m, hms, hm⟩ := hne
  set s' := s.filter fun m => c m ≠ 0
  have hne' : s'.Nonempty := ⟨m, Finset.mem_filter.2 ⟨hms, hm⟩⟩
  obtain ⟨m₀, hm₀, hmax⟩ := s'.exists_max_image Finsupp.degree hne'
  rw [Finset.mem_filter] at hm₀
  set N := transposeExp m₀
  have hN : N.degree = m₀.degree := degree_transposeExp m₀
  have hhom : (monomial N (1 : ℂ)).IsHomogeneous m₀.degree := by
    rw [← hN]; exact isHomogeneous_monomial _ rfl
  have key : ∀ m ∈ s, m ≠ m₀ → c m * constantCoeff (rho 1 (canon m) (monomial N 1)) = 0 := by
    intro m hm hne
    by_cases hc : c m = 0
    · rw [hc, zero_mul]
    have hdeg : m.degree ≤ m₀.degree := hmax m (Finset.mem_filter.2 ⟨hm, hc⟩)
    rcases hdeg.lt_or_eq with hlt | heq
    · rw [canon, constantCoeff_rho_one_word_of_lt _ _ _ hhom (by rw [length_expand]; exact hlt),
        mul_zero]
    · have : ¬ constantCoeff (rho 1 (canon m) (monomial N 1)) ≠ 0 := by
        rw [constantCoeff_rho_one_canon_monomial _ _ (by rw [heq, hN])]
        exact fun h' => hne (transposeExp_injective h')
      rw [not_not.1 this, mul_zero]
  have hsum := congrArg (fun T : Module.End ℂ (Poly n) => constantCoeff (T (monomial N 1))) h
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, map_zero,
    LinearMap.zero_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.constantCoeff_C] at hsum
  rw [Finset.sum_eq_single m₀ (fun m hm hne => key m hm hne) (fun h' => absurd hm₀.1 h')] at hsum
  have h0 : constantCoeff (rho 1 (canon m₀) (monomial N 1)) ≠ 0 :=
    (constantCoeff_rho_one_canon_monomial _ _ hN.symm).2 rfl
  exact hm₀.2 ((mul_eq_zero.1 hsum).resolve_right h0)

/- English proof (translation)
Rewrite using `[linearIndependent_iff']`. Introduce `s c hs`. Conclude with `coeff_eq_zero_of_rho_one s c (by rw [hs, map_zero])`.
-/
theorem linearIndependent_canon : LinearIndependent ℂ (canon (n := n)) := by
  rw [linearIndependent_iff']
  intro s c hs
  exact coeff_eq_zero_of_rho_one s c (by rw [hs, map_zero])

noncomputable def pbw : Module.Basis (Fin n × Fin n →₀ ℕ) ℂ (U n) :=
  Module.Basis.mk linearIndependent_canon span_canon_eq_top.ge

/- English proof (translation)
The claim follows from `Module.Basis.mk_apply _ _ _`.
-/
@[simp] theorem pbw_apply (m : Fin n × Fin n →₀ ℕ) : pbw (n := n) m = canon m :=
  Module.Basis.mk_apply _ _ _

/- English proof (translation)
Use `conv_rhs => rw [← pbw.linearCombination_repr u]`. Rewrite using `[Finsupp.linearCombination_apply, Finsupp.sum]`. Simplify using the standard rewrite rules.
-/
theorem sum_repr_canon (u : U n) :
    ∑ m ∈ (pbw.repr u).support, pbw.repr u m • canon m = u := by
  conv_rhs => rw [← pbw.linearCombination_repr u]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  simp

/- English proof (translation)
Rewrite `h`, the goal using `[← sum_repr_canon u]`. Use `coeff_eq_zero_of_rho_one _ _ h` as an intermediate fact. Conclude with `Finset.sum_eq_zero fun m hm => by rw [this m hm, zero_smul]`.
-/
theorem eq_zero_of_rho_one_eq_zero {u : U n} (h : rho 1 u = 0) : u = 0 := by
  rw [← sum_repr_canon u] at h ⊢
  have := coeff_eq_zero_of_rho_one _ _ h
  exact Finset.sum_eq_zero fun m hm => by rw [this m hm, zero_smul]

/- English proof (translation)
The claim follows from `eq_zero_of_rho_one_eq_zero (rho_one_eq_zero_of_rho_zero_eq_zero u h)`.
-/
theorem eq_zero_of_rho_zero_eq_zero {u : U n} (h : rho 0 u = 0) : u = 0 :=
  eq_zero_of_rho_one_eq_zero (rho_one_eq_zero_of_rho_zero_eq_zero u h)

end GroundTheory.Automorphic.HarishChandra
