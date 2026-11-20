import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open Polynomial

universe u

noncomputable section

section ReesFiltration

variable {A : Type u} [CommRing A] (I : Ideal A) {H : Type u} [AddCommGroup H] [Module A H]

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[pow_succ', Submodule.mul_smul, ← add_assoc]`. Conclude with `(Submodule.smul_mono le_rfl ih).trans (hK _)`.
-/
lemma pow_smul_le_of_smul_le {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (i j : ℕ) : I ^ i • K j ≤ K (j + i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', Submodule.mul_smul, ← add_assoc]
    exact (Submodule.smul_mono le_rfl ih).trans (hK _)

def reesFiltration {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1)) :
    Submodule (reesAlgebra I) (PolynomialModule A H) where
  carrier := {p | ∀ n, p.coeff n ∈ K n}
  add_mem' {p q} hp hq n := by
    have : (p + q).coeff n = p.coeff n + q.coeff n := rfl
    rw [this]
    exact add_mem (hp n) (hq n)
  zero_mem' n := by
    change (0 : PolynomialModule A H).coeff n ∈ K n
    exact (K n).zero_mem
  smul_mem' r p hp n := by
    change ((r : A[X]) • p).coeff n ∈ K n
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun x hx => ?_
    have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    have hr : (r : A[X]).coeff x.1 ∈ I ^ x.1 := (mem_reesAlgebra_iff I _).1 r.2 x.1
    have := pow_smul_le_of_smul_le I hK x.1 x.2 (Submodule.smul_mem_smul hr (hp x.2))
    rwa [add_comm, hx'] at this

/- English proof (translation)
Take `⟨s, hs⟩` from `hfg`. Use `set c := s.sup fun p => p.coeff.support.sup id`. Establish `hdeg : ∀ p ∈ s, ∀ j, c < j → p.coeff j = 0`. Introduce `p hp j hj`. Assume the negation of the conclusion as `h`.

Establish `h1 : j ≤ p.coeff.support.sup id` using `Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)`. Establish `h2 : p.coeff.support.sup id ≤ c` using `Finset.le_sup (f := fun p => p.coeff.support.sup id) hp`. Use linear arithmetic over natural numbers and integers. Use `⟨c, fun n => le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Establish `hmem : PolynomialModule.single A (n + c) x ∈ reesFiltration I hK`. Introduce `m`. Rewrite using `[PolynomialModule.coeff_single, Finsupp.single_apply]`. Use `split_ifs with h`. Conclude with `h ▸ hx`.

Conclude with `(K m).zero_mem`. Rewrite `hmem` using `[← hs, Submodule.mem_span_finset]`. Take `⟨f, -, hf⟩` from `hmem`. Establish `hx' : x = (∑ p ∈ s, f p • p).coeff (n + c)`. Rewrite using `[hf, PolynomialModule.coeff_single, Finsupp.single_eq_same]`.

Rewrite using `[hx']`. Establish `hsum : (∑ p ∈ s, f p • p).coeff = ∑ p ∈ s, (f p • p).coeff` using `map_sum (PolynomialModule.coeffAddEquiv (R := A) (M := H)) _ s`. Rewrite using `[hsum, Finsupp.finsetSum_apply]`. Use `Submodule.sum_mem _ fun p hp => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(((f p : reesAlgebra I) : A[X]) • p).coeff (n + c) ∈ _`.

Rewrite using `[PolynomialModule.smul_apply]`. Use `Submodule.sum_mem _ fun y hy => ?_` and prove the remaining obligations. Establish `hy' : y.1 + y.2 = n + c` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hy`. Distinguish the cases in `hj : c < y.2`. Rewrite using `[hdeg p hp y.2 hj, smul_zero]`.

Conclude with `Submodule.zero_mem _`. Use `replace hj := not_lt.1 hj`. Establish `hr : ((f p : reesAlgebra I) : A[X]).coeff y.1 ∈ I ^ y.1` using `(mem_reesAlgebra_iff I _).1 (f p).2 y.1`. Establish `hp' : p.coeff y.2 ∈ K y.2`. Establish `: p ∈ reesFiltration I hK` using `hs ▸ Submodule.subset_span hp`.

Conclude with `this y.2`. Establish `hy1 : y.1 = n + (c - y.2)` using `by omega`. Rewrite `hr` using `[hy1, pow_add]`. Establish `h1 : ((f p : reesAlgebra I) : A[X]).coeff y.1 • p.coeff y.2 ∈ (I ^ n * I ^ (c - y.2)) • K y.2` using `hy1 ▸ Submodule.smul_mem_smul hr hp'`. Rewrite `h1` using `[Submodule.mul_smul]`.

Use `Submodule.smul_mono le_rfl ?_ h1` and prove the remaining obligations. Use `pow_smul_le_of_smul_le I hK (c - y.2) y.2` as an intermediate fact. Rewrite `this` using `[show y.2 + (c - y.2) = c by omega]`. Then use the resulting hypothesis. Use `pow_smul_le_of_smul_le I hK n c` as an intermediate fact. Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis.
-/
theorem exists_eq_pow_smul_of_fg {K : ℕ → Submodule A H} (hK : ∀ n, I • K n ≤ K (n + 1))
    (hfg : (reesFiltration I hK).FG) : ∃ c, ∀ n, K (n + c) = I ^ n • K c := by
  classical
  obtain ⟨s, hs⟩ := hfg
  set c := s.sup fun p => p.coeff.support.sup id
  have hdeg : ∀ p ∈ s, ∀ j, c < j → p.coeff j = 0 := by
    intro p hp j hj
    by_contra h
    have h1 : j ≤ p.coeff.support.sup id :=
      Finset.le_sup (f := id) (Finsupp.mem_support_iff.2 h)
    have h2 : p.coeff.support.sup id ≤ c := Finset.le_sup (f := fun p => p.coeff.support.sup id) hp
    omega
  refine ⟨c, fun n => le_antisymm ?_ ?_⟩
  · intro x hx
    have hmem : PolynomialModule.single A (n + c) x ∈ reesFiltration I hK := by
      intro m
      rw [PolynomialModule.coeff_single, Finsupp.single_apply]
      split_ifs with h
      · exact h ▸ hx
      · exact (K m).zero_mem
    rw [← hs, Submodule.mem_span_finset] at hmem
    obtain ⟨f, -, hf⟩ := hmem
    have hx' : x = (∑ p ∈ s, f p • p).coeff (n + c) := by
      rw [hf, PolynomialModule.coeff_single, Finsupp.single_eq_same]
    rw [hx']
    have hsum : (∑ p ∈ s, f p • p).coeff = ∑ p ∈ s, (f p • p).coeff :=
      map_sum (PolynomialModule.coeffAddEquiv (R := A) (M := H)) _ s
    rw [hsum, Finsupp.finsetSum_apply]
    refine Submodule.sum_mem _ fun p hp => ?_
    change (((f p : reesAlgebra I) : A[X]) • p).coeff (n + c) ∈ _
    rw [PolynomialModule.smul_apply]
    refine Submodule.sum_mem _ fun y hy => ?_
    have hy' : y.1 + y.2 = n + c := Finset.HasAntidiagonal.mem_antidiagonal.1 hy
    by_cases hj : c < y.2
    · rw [hdeg p hp y.2 hj, smul_zero]
      exact Submodule.zero_mem _
    · replace hj := not_lt.1 hj
      have hr : ((f p : reesAlgebra I) : A[X]).coeff y.1 ∈ I ^ y.1 :=
        (mem_reesAlgebra_iff I _).1 (f p).2 y.1
      have hp' : p.coeff y.2 ∈ K y.2 := by
        have : p ∈ reesFiltration I hK := hs ▸ Submodule.subset_span hp
        exact this y.2
      have hy1 : y.1 = n + (c - y.2) := by omega
      rw [hy1, pow_add] at hr
      have h1 : ((f p : reesAlgebra I) : A[X]).coeff y.1 • p.coeff y.2 ∈
          (I ^ n * I ^ (c - y.2)) • K y.2 := hy1 ▸ Submodule.smul_mem_smul hr hp'
      rw [Submodule.mul_smul] at h1
      refine Submodule.smul_mono le_rfl ?_ h1
      have := pow_smul_le_of_smul_le I hK (c - y.2) y.2
      rwa [show y.2 + (c - y.2) = c by omega] at this
  · have := pow_smul_le_of_smul_le I hK n c
    rwa [add_comm] at this

end ReesFiltration

end

end GroundTheory.Arith.SchemeCoh
