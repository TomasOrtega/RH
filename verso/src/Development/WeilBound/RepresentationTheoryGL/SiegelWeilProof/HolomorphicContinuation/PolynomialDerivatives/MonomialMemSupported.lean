import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.AdjoinFirstOperatorsPreservesFamily

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Core

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Rewrite using `[ha, monomial_zero]`. Conclude with `Subalgebra.zero_mem _`. Rewrite using `[mem_supported, vars_monomial ha]`. Introduce `k hk`.

Conclude with `hs k hk`.
-/
theorem monomial_mem_supported' {S : Set (Fin m × Fin n × Bool)} (s : Fin m × Fin n × Bool →₀ ℕ)
    (hs : ∀ k ∈ s.support, k ∈ S) (a : ℂ) : (monomial s a : PX m n) ∈ supported ℂ S := by
  by_cases ha : a = 0
  · rw [ha, monomial_zero]; exact Subalgebra.zero_mem _
  · rw [mem_supported, vars_monomial ha]
    intro k hk
    exact hs k hk

/- English proof (translation)
Unfold `box`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨s, hs, -, rfl⟩`. Conclude with `monomial_mem_supported' s hs 1`.
-/
theorem box_le_first_family (ε : Fin m → Bool) (R : Set (Fin m → ℕ)) : box ε R ≤ F1 (n := n) ε := by
  unfold box
  rw [Submodule.span_le]
  rintro _ ⟨s, hs, -, rfl⟩
  exact monomial_mem_supported' s hs 1

/- English proof (translation)
Introduce `p hp`. Rewrite using `[p.as_sum]`. Use `Submodule.sum_mem _ fun s hs => ?_` and prove the remaining obligations. Establish `hF : ∀ k ∈ s.support, inF1 ε k`. Introduce `k hk`.

Establish `: k ∈ p.vars`. Rewrite using `[mem_vars]`. Conclude with `⟨s, hs, hk⟩`. Conclude with `(mem_supported.mp hp) this`. Establish `: monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n)`.

Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hF, Set.mem_univ _, rfl⟩)`.
-/
theorem first_family_le_box (ε : Fin m → Bool) : F1 (n := n) ε ≤ box ε Set.univ := by
  intro p hp
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun s hs => ?_
  have hF : ∀ k ∈ s.support, inF1 ε k := by
    intro k hk
    have : k ∈ p.vars := by
      rw [mem_vars]; exact ⟨s, hs, hk⟩
    exact (mem_supported.mp hp) this
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hF, Set.mem_univ _, rfl⟩)

/- English proof (translation)
Unfold `box`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, hr, rfl⟩`. Conclude with `⟨s, hs, h hr, rfl⟩`.
-/
theorem box_mono (ε : Fin m → Bool) {R R' : Set (Fin m → ℕ)} (h : R ⊆ R') : box (n := n) ε R ≤ box ε R' := by
  unfold box
  refine Submodule.span_mono ?_
  rintro _ ⟨s, hs, hr, rfl⟩
  exact ⟨s, hs, h hr, rfl⟩

/- English proof (translation)
Use `set M : ℕ := R.sup fun r => ∑ a, r a`. Establish `hfin : {p : PX m n | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ (R : Set _) ∧ p = monomial s 1}.Finite`. Use `((Set.finite_univ (α := Fin m × Fin n × Bool → Fin (M + 1))).image fun f => (monomial (Finsupp.equivFunOnFinite.symm fun k => (f k : ℕ)) 1 : PX m n)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, hr, rfl⟩`. Establish `hle : ∀ k, s k ≤ M`.

Introduce `k`. Distinguish the cases in `hk : k ∈ s.support`. Establish `hk1` using `hs k hk`. Establish `h1 : s k ≤ rdeg ε s k.1`. Unfold `rdeg`.

Establish `: k = (k.1, k.2.1, !ε k.1)`. Take `⟨a, i, b⟩` from `k`. Simplify using `only [inF1] at hk1`. Simplify using `[hk1]`. Rewrite using `[this]`.

Conclude with `Finset.single_le_sum (f := fun i => s (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)`. Establish `h2 : rdeg ε s k.1 ≤ ∑ a, rdeg ε s a` using `Finset.single_le_sum (f := fun a => rdeg ε s a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)`. Establish `h3 : (∑ a, rdeg ε s a) ≤ M` using `Finset.le_sup (f := fun r : Fin m → ℕ => ∑ a, r a) (Finset.mem_coe.mp hr)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finsupp.notMem_support_iff.mp hk]`.

Conclude with `Nat.zero_le _`. Use `⟨fun k => ⟨s k, Nat.lt_succ_of_le (hle k)⟩, Set.mem_univ _, ?_⟩` and prove the remaining obligations. Use `congr 1`. Use extensionality with `k`. Simplify using the standard rewrite rules.

Conclude with `FiniteDimensional.span_of_finite ℂ hfin`.
-/
theorem box_finiteDimensional (ε : Fin m → Bool) (R : Finset (Fin m → ℕ)) :
    FiniteDimensional ℂ (box (n := n) ε (R : Set (Fin m → ℕ))) := by
  classical
  set M : ℕ := R.sup fun r => ∑ a, r a
  have hfin : {p : PX m n | ∃ s : Fin m × Fin n × Bool →₀ ℕ, (∀ k ∈ s.support, inF1 ε k) ∧ rdeg ε s ∈ (R : Set _) ∧
      p = monomial s 1}.Finite := by
    refine ((Set.finite_univ (α := Fin m × Fin n × Bool → Fin (M + 1))).image
      fun f => (monomial (Finsupp.equivFunOnFinite.symm fun k => (f k : ℕ)) 1 : PX m n)).subset ?_
    rintro _ ⟨s, hs, hr, rfl⟩
    have hle : ∀ k, s k ≤ M := by
      intro k
      by_cases hk : k ∈ s.support
      · have hk1 := hs k hk
        have h1 : s k ≤ rdeg ε s k.1 := by
          unfold rdeg
          have : k = (k.1, k.2.1, !ε k.1) := by
            obtain ⟨a, i, b⟩ := k
            simp only [inF1] at hk1
            simp [hk1]
          rw [this]
          exact Finset.single_le_sum (f := fun i => s (k.1, i, !ε k.1)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h2 : rdeg ε s k.1 ≤ ∑ a, rdeg ε s a :=
          Finset.single_le_sum (f := fun a => rdeg ε s a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        have h3 : (∑ a, rdeg ε s a) ≤ M := Finset.le_sup (f := fun r : Fin m → ℕ => ∑ a, r a) (Finset.mem_coe.mp hr)
        omega
      · rw [Finsupp.notMem_support_iff.mp hk]; exact Nat.zero_le _
    refine ⟨fun k => ⟨s k, Nat.lt_succ_of_le (hle k)⟩, Set.mem_univ _, ?_⟩
    congr 1
    ext k
    simp
  exact FiniteDimensional.span_of_finite ℂ hfin

/- English proof (translation)
Use function extensionality and compare the values at `a`. Unfold `rdeg`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.filter_apply_pos]`. Simplify using `[inF1]`.
-/
theorem rdeg_filter (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) :
    rdeg ε (s.filter (inF1 ε)) = rdeg ε s := by
  funext a
  unfold rdeg
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.filter_apply_pos]
  simp [inF1]

/- English proof (translation)
Use `⟨by rw [monomial_mul, Finsupp.filter_pos_add_filter_neg, one_mul], ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.subset_span ⟨s.filter (inF1 ε), fun k hk => ?_, by simp [rdeg_filter], rfl⟩` and prove the remaining obligations. Rewrite `hk` using `[Finsupp.support_filter, Finset.mem_filter]`. Conclude with `hk.2`. Use `monomial_mem_supported' _ (fun k hk => ?_) a` and prove the remaining obligations.

Rewrite `hk` using `[Finsupp.support_filter, Finset.mem_filter]`. Conclude with `hk.2`.
-/
theorem monomial_split (ε : Fin m → Bool) (s : Fin m × Fin n × Bool →₀ ℕ) (a : ℂ) :
    (monomial s a : PX m n) = monomial (s.filter (inF1 ε)) 1 * monomial (s.filter fun k => ¬ inF1 ε k) a ∧
      (monomial (s.filter (inF1 ε)) 1 : PX m n) ∈ box ε {rdeg ε s} ∧
      (monomial (s.filter fun k => ¬ inF1 ε k) a : PX m n) ∈ F2 ε := by
  refine ⟨by rw [monomial_mul, Finsupp.filter_pos_add_filter_neg, one_mul], ?_, ?_⟩
  · refine Submodule.subset_span ⟨s.filter (inF1 ε), fun k hk => ?_, by simp [rdeg_filter], rfl⟩
    rw [Finsupp.support_filter, Finset.mem_filter] at hk; exact hk.2
  · refine monomial_mem_supported' _ (fun k hk => ?_) a
    rw [Finsupp.support_filter, Finset.mem_filter] at hk
    exact hk.2

end PositivityTheory.Rg.Sw.LC.Core
