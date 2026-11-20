import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc

open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ _ R _ s n v hv`. Establish `hsum (k : ℤ) : ∑ i, (if i ∈ s then k else 0) = k * s.card`. Rewrite using `[Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]`. Establish `hdeg (m : ι →₀ ℕ) : ((m.degree : ℕ) : ℤ) = ∑ i, (m i : ℤ)`. Rewrite using `[Finsupp.degree_eq_sum]`.

Use `push_cast`. Both sides reduce to the same expression. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Set `k : ℕ` to `∑ i, (a.1 i).natAbs`. Establish `hk (i : ι) : 0 ≤ a.1 i + if i ∈ s then (k : ℤ) else 0` using `by split_ifs with h`. Establish `: (a.1 i).natAbs ≤ k` using `Finset.single_le_sum (f := fun i => (a.1 i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)`. Use linear arithmetic over natural numbers and integers. Simplify using `using a.2.2 i h`.

Set `m : ι →₀ ℕ` to `Finsupp.equivFunOnFinite.symm fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat`. Establish `hm (i : ι) : (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0` using `Int.toNat_of_nonneg (hk i)`. Rewrite using `[hv a k m hm]`. Use `awayFrac_mem_homLoc (monomial_mem_polyGrading m 1) ?_` and prove the remaining obligations. Rewrite using `[hdeg, Finset.sum_congr rfl fun i _ => hm i, Finset.sum_add_distrib, a.2.1, hsum]`.

Introduce and unpack `_ ⟨k, p, hp, rfl⟩`. Rewrite using `[p.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hd` using `mem_polyGrading_iff.1 hp m (mem_support_iff.1 hm)`. Establish `e : monomial m (coeff m p) = coeff m p • (monomial m 1 : MvPolynomial ι R)`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[e, LinearMap.map_smul_of_tower]`. Use `Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨fun i => m i - if i ∈ s then (k : ℤ) else 0, ?_, fun i hi => ?_⟩, hv _ k m fun i => ?_⟩)` and prove the remaining obligations. Rewrite using `[Finset.sum_sub_distrib, hsum, ← hdeg, hd, add_sub_cancel_right]`. Simplify using `[hi]`.

Simplify using the standard rewrite rules.
-/
theorem span_laurentMonomial_eq_homLoc :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R] (s : Finset ι) (n : ℤ)
      (v : {a : ι → ℤ // ∑ i, a i = n ∧ ∀ i, i ∉ s → 0 ≤ a i} →
        LocalizedModule.Away (xProd R s) (MvPolynomial ι R)),
      (∀ a (k : ℕ) (m : ι →₀ ℕ), (∀ i, (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0) →
        v a = awayFrac (MvPolynomial ι R) (xProd R s) k (monomial m 1)) →
      Submodule.span R (Set.range v) = homLoc (polyGrading ι R) s n := by
  intro ι _ _ R _ s n v hv
  have hsum (k : ℤ) : ∑ i, (if i ∈ s then k else 0) = k * s.card := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hdeg (m : ι →₀ ℕ) : ((m.degree : ℕ) : ℤ) = ∑ i, (m i : ℤ) := by
    rw [Finsupp.degree_eq_sum]; push_cast; rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    let k : ℕ := ∑ i, (a.1 i).natAbs
    have hk (i : ι) : 0 ≤ a.1 i + if i ∈ s then (k : ℤ) else 0 := by
      split_ifs with h
      · have : (a.1 i).natAbs ≤ k :=
          Finset.single_le_sum (f := fun i => (a.1 i).natAbs) (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ i)
        omega
      · simpa using a.2.2 i h
    let m : ι →₀ ℕ := Finsupp.equivFunOnFinite.symm
      fun i => (a.1 i + if i ∈ s then (k : ℤ) else 0).toNat
    have hm (i : ι) : (m i : ℤ) = a.1 i + if i ∈ s then (k : ℤ) else 0 :=
      Int.toNat_of_nonneg (hk i)
    rw [hv a k m hm]
    refine awayFrac_mem_homLoc (monomial_mem_polyGrading m 1) ?_
    rw [hdeg, Finset.sum_congr rfl fun i _ => hm i, Finset.sum_add_distrib, a.2.1, hsum]
  · rintro _ ⟨k, p, hp, rfl⟩
    rw [p.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hd := mem_polyGrading_iff.1 hp m (mem_support_iff.1 hm)
    have e : monomial m (coeff m p) = coeff m p • (monomial m 1 : MvPolynomial ι R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [e, LinearMap.map_smul_of_tower]
    refine Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨⟨fun i => m i - if i ∈ s then (k : ℤ) else 0, ?_, fun i hi => ?_⟩, hv _ k m fun i => ?_⟩)
    · rw [Finset.sum_sub_distrib, hsum, ← hdeg, hd, add_sub_cancel_right]
    · simp [hi]
    · simp

end GlobalTheory
