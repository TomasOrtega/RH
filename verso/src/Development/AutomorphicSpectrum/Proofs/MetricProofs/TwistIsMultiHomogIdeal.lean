import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Tw

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`. Express the relevant statement in the definitionally equal form `(⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h`. Consider the cases of `h`. Both sides reduce to the same expression.
-/
theorem oldIdx_injective {K : Type} {ι : K → Type} :
    Function.Injective (oldIdx (ι := ι)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  change (⟨some a, b⟩ : (o : Option K) × Tb ι o) = ⟨some c, d⟩ at h
  cases h
  rfl

/- English proof (translation)
Introduce `m hm o`. Establish `hinj : Function.Injective (oldIdx (ι` using `ι)) := oldIdx_injective`. Express the relevant statement in the definitionally equal form `m ∈ (MvPolynomial.rename oldIdx f).support at hm`. Rewrite `hm` using `[MvPolynomial.support_rename_of_injective hinj, Finset.mem_image]`. Take `⟨m', hm', rfl⟩` from `hm`.

Consider the cases of `o with`. Consider the case `none`. Simplify using `only [Option.elim_none]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`.

Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises. Introduce and unpack `⟨q, hq⟩`. Establish `h0` using `congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq`. Simplify using `[oldIdx] at h0`. Consider the case `some k`.

Simplify using `only [Option.elim_some]`. Use `(Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _ (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)` and prove the remaining obligations. Conclude with `Finsupp.mapDomain_apply hinj m' ⟨k, i⟩`.
-/
theorem isMultiHomog_inc {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsMultiHomog (inc f : MRing (Tb ι)) (fun o => o.elim 0 a) := by
  classical
  intro m hm o
  have hinj : Function.Injective (oldIdx (ι := ι)) := oldIdx_injective
  change m ∈ (MvPolynomial.rename oldIdx f).support at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  cases o with
  | none =>
    simp only [Option.elim_none]
    apply Finset.sum_eq_zero
    intro i _
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨q, hq⟩
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) hq
    simp [oldIdx] at h0
  | some k =>
    simp only [Option.elim_some]
    refine (Fintype.sum_equiv (show Tb ι (some k) ≃ ι k from Equiv.refl _) _
      (fun i => m' ⟨k, i⟩) (fun i => ?_)).trans (hf m' hm' k)
    exact Finsupp.mapDomain_apply hinj m' ⟨k, i⟩

/- English proof (translation)
Consider the cases of `o with`. Consider the case `none`. Simplify using `only [Option.elim_none]`. Use `(Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _ (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two]`.

Apply the tactic sequence `fin_cases j <;> simp [Finsupp.single_apply] <;> (intro h`. Establish `h2` using `eq_of_heq (Sigma.mk.inj_iff.mp h).2`. Establish `h3` using `congrArg (fun t : Fin 2 => (t : ℕ)) h2`. Conclude with `absurd h3 (by decide))`. Consider the case `some k`.

Simplify using `only [Option.elim_some]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `h`.

Establish `h0` using `congrArg (fun z : (o : Option K) × Tb ι o => z.1) h`. Simplify using `at h0`.
-/
theorem sum_single_none {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (j : Fin 2) (o : Option K) :
    ∑ i, (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨o, i⟩ = o.elim 2 (fun _ => 0) := by
  classical
  cases o with
  | none =>
    simp only [Option.elim_none]
    refine (Fintype.sum_equiv (show Tb ι none ≃ Fin 2 from Equiv.refl _) _
      (fun i : Fin 2 => (Finsupp.single (⟨none, j⟩ : Σ o, Tb ι o) 2) ⟨none, i⟩) (fun _ => rfl)).trans ?_
    rw [Fin.sum_univ_two]
    fin_cases j <;> simp [Finsupp.single_apply] <;>
      (intro h
       have h2 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
       have h3 := congrArg (fun t : Fin 2 => (t : ℕ)) h2
       exact absurd h3 (by decide))
  | some k =>
    simp only [Option.elim_some]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    have h0 := congrArg (fun z : (o : Option K) × Tb ι o => z.1) h
    simp at h0

/- English proof (translation)
Introduce `m hm o`. Establish `h1 : (xN ^ 2 : MRing (Tb ι)) = MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ)`. Simplify using `only [xN, MvPolynomial.X_pow_eq_monomial]`. Establish `h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) = MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ)`. Simplify using `only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]`.

Establish `hq : (quad p : MRing (Tb ι)) = MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) + MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ)`. Unfold `quad`. Rewrite using `[h1, h2]`. Rewrite `hm` using `[hq]`. Establish `hm2` using `Finset.mem_union.mp (MvPolynomial.support_add hm)`.

Break down `hm2 with h | h` into its components or cases. Establish `h'` using `Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)`. Substitute `h'` using the available equality. Conclude with `sum_single_none (ι := ι) 0 o`. Establish `h'` using `Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)`.

Substitute `h'` using the available equality. Conclude with `sum_single_none (ι := ι) 1 o`.
-/
theorem isMultiHomog_quad {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)] (p : ℕ) :
    IsMultiHomog (quad p : MRing (Tb ι)) (fun o => o.elim 2 (fun _ => 0)) := by
  classical
  intro m hm o
  have h1 : (xN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) := by
    simp only [xN, MvPolynomial.X_pow_eq_monomial]
  have h2 : (MvPolynomial.C (p : ℤ) * yN ^ 2 : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    simp only [yN, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  have hq : (quad p : MRing (Tb ι)) =
      MvPolynomial.monomial (Finsupp.single (⟨none, (0 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (1 : ℤ) +
      MvPolynomial.monomial (Finsupp.single (⟨none, (1 : Fin 2)⟩ : (o : Option K) × Tb ι o) 2) (p : ℤ) := by
    unfold quad
    rw [h1, h2]
  rw [hq] at hm
  have hm2 := Finset.mem_union.mp (MvPolynomial.support_add hm)
  rcases hm2 with h | h
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 0 o
  · have h' := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset h)
    subst h'
    exact sum_single_none (ι := ι) 1 o

/- English proof (translation)
Take `⟨S, hS, rfl⟩` from `hW`. Use `⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `f (⟨g, hg, rfl⟩ | hf)`. Take `⟨a, ha⟩` from `hS g hg`. Conclude with `⟨_, isMultiHomog_inc ha⟩`.

Rewrite `hf` using `[Set.mem_singleton_iff]`. Substitute `hf` using the available equality. Conclude with `⟨_, isMultiHomog_quad p⟩`. Rewrite using `[twist, Ideal.map_span, Ideal.span_union]`.
-/
theorem isMultiHomogIdeal_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) : IsMultiHomogIdeal (twist p W) := by
  obtain ⟨S, hS, rfl⟩ := hW
  refine ⟨(inc '' S) ∪ {quad p}, ?_, ?_⟩
  · rintro f (⟨g, hg, rfl⟩ | hf)
    · obtain ⟨a, ha⟩ := hS g hg
      exact ⟨_, isMultiHomog_inc ha⟩
    · rw [Set.mem_singleton_iff] at hf
      subst hf
      exact ⟨_, isMultiHomog_quad p⟩
  · rw [twist, Ideal.map_span, Ideal.span_union]

end GlobalTheory.CompanionTheory.Ar.Tw
