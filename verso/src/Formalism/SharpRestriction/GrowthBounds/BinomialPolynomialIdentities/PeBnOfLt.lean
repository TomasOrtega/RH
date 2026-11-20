import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.RestPathFrom

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`. Simplify using `only [iv, Prod.mk.injEq] at h`. Conclude with `Prod.ext (Fin.ext h.1) h.2`.
-/
theorem iv_inj (N n : ℕ) : Function.Injective (iv N n) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  simp only [iv, Prod.mk.injEq] at h
  exact Prod.ext (Fin.ext h.1) h.2

/- English proof (translation)
Simplify using `[Bn, h]`.
-/
theorem pe_Bn_of_lt {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : i < N) : Bn B i = B ⟨i, h⟩ := by simp [Bn, h]

/- English proof (translation)
Simplify using `[Bn, h]`.
-/
theorem Bn_of_ge {N : ℕ} (B : Fin N → ℕ) {i : ℕ} (h : ¬ i < N) : Bn B i = 0 := by simp [Bn, h]

/- English proof (translation)
Use extensionality with `e`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩ i`. Distinguish the cases in `h : i < N`. Rewrite using `[if_pos h, pe_Bn_of_lt B h, ← hm ⟨i, h⟩]`.

Unfold `multideg`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Establish `: ((i, a) : ℕ × Fin n) = iv N n (⟨i, h⟩, a)` using `rfl`. Rewrite using `[this, Finsupp.mapDomain_apply (iv_inj N n)]`. Rewrite using `[if_neg h]`.

Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Apply `Finsupp.mapDomain_of_notMem_range` to reduce the goal to its premises. Introduce and unpack `⟨⟨x, y⟩, hxy⟩`. Simplify using `only [iv, Prod.mk.injEq] at hxy`. Conclude with `h (hxy.1 ▸ x.2)`.

Introduce `he`. Establish `hsupp : (↑e.support : Set (ℕ × Fin n)) ⊆ Set.range (iv N n)`. Introduce and unpack `⟨i, a⟩ hia`. Distinguish the cases in `h : i < N`. Conclude with `⟨(⟨i, h⟩, a), rfl⟩`.

It suffices to derive a contradiction. Establish `h0` using `he i`. Rewrite `h0` using `[if_neg h]`. Use `(Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a)` as an intermediate fact. Simplify using `only [Finset.mem_coe, Finsupp.mem_support_iff] at hia`.

Conclude with `hia this`. Use `⟨e.comapDomain (iv N n) (iv_inj N n).injOn, ?_, Finsupp.mapDomain_comapDomain _ (iv_inj N n) e hsupp⟩` and prove the remaining obligations. Introduce `i`. Establish `h0` using `he i.val`. Rewrite `h0` using `[if_pos i.2, pe_Bn_of_lt B i.2]`.

Rewrite using `[← h0]`. Unfold `multideg`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.comapDomain_apply]`. Both sides reduce to the same expression.
-/
theorem expSet_eq (n N : ℕ) (B : Fin N → ℕ) :
    (fun m : Fin N × Fin n →₀ ℕ => m.mapDomain (iv N n)) '' {m | ∀ i, multideg m i = B i} =
      {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then Bn B i else 0} := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩ i
    by_cases h : i < N
    · rw [if_pos h, pe_Bn_of_lt B h, ← hm ⟨i, h⟩]
      unfold multideg
      refine Finset.sum_congr rfl fun a _ => ?_
      have : ((i, a) : ℕ × Fin n) = iv N n (⟨i, h⟩, a) := rfl
      rw [this, Finsupp.mapDomain_apply (iv_inj N n)]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun a _ => ?_
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨⟨x, y⟩, hxy⟩
      simp only [iv, Prod.mk.injEq] at hxy
      exact h (hxy.1 ▸ x.2)
  · intro he
    have hsupp : (↑e.support : Set (ℕ × Fin n)) ⊆ Set.range (iv N n) := by
      rintro ⟨i, a⟩ hia
      by_cases h : i < N
      · exact ⟨(⟨i, h⟩, a), rfl⟩
      · exfalso
        have h0 := he i
        rw [if_neg h] at h0
        have := (Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a)
        simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hia
        exact hia this
    refine ⟨e.comapDomain (iv N n) (iv_inj N n).injOn, ?_, Finsupp.mapDomain_comapDomain _ (iv_inj N n) e hsupp⟩
    intro i
    have h0 := he i.val
    rw [if_pos i.2, pe_Bn_of_lt B i.2] at h0
    rw [← h0]
    unfold multideg
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finsupp.comapDomain_apply]
    rfl

/- English proof (translation)
Introduce `R _ n N B`. Rewrite using `[(Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank n N (Bn B)).2.2 R, ← expSet_eq, Pol, MvPolynomial.restrictSupport_eq_span, Submodule.map_span, Set.image_image, Set.image_image]`. Use `congr 1`. Apply `Set.image_congr` to reduce the goal to its premises. Introduce `m _`.

Simplify using `[rename_monomial]`.
-/
theorem restPol : RestPol := by
  intro R _ n N B
  rw [(Formalism.InvariantFactorPaths.GelfandTsetlinBases.polynomial_b_rank n N (Bn B)).2.2 R, ← expSet_eq, Pol, MvPolynomial.restrictSupport_eq_span,
    Submodule.map_span, Set.image_image, Set.image_image]
  congr 1
  apply Set.image_congr
  intro m _
  simp [rename_monomial]

end Formalism.MainNotions.G.ColumnFamilies
