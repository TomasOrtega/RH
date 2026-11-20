import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFTC

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

/- English proof (translation)
Establish `h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support, emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1)` using `by conv_lhs => rw [decomp (ε := ε) Q]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun ν _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `congr 1`.

Conclude with `DFunLike.congr_fun (act_emb_same true v) _`. Conclude with `DFunLike.congr_fun (act_emb_other true false (by decide) v) _`. Rewrite `h1` using `[hQ]`. Establish `h2` using `congrArg (fun P => coeff μ (Th ε P)) h1`. Simplify using `only [map_sum, th_prod, coeff_sum_monomial] at h2`.

Distinguish the cases in `hμ : μ ∈ (Th ε Q).support`. Rewrite `h2` using `[if_pos hμ]`. Conclude with `h2.symm`. Establish `: coeff μ (Th ε Q) = 0` using `notMem_support_iff.1 hμ`. Rewrite using `[this, map_zero]`.
-/
theorem coeff_inv (v : Matrix (Rw ε true) (Rw ε true) ℂ) (Q : PX m n) (hQ : act (blk ε true v) Q = Q)
    (μ : VV (Rw ε false) n →₀ ℕ) : sub v (v.map star) ((Th ε Q).coeff μ) = (Th ε Q).coeff μ := by
  classical
  have h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support,
      emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [map_mul]
    congr 1
    · exact DFunLike.congr_fun (act_emb_same true v) _
    · exact DFunLike.congr_fun (act_emb_other true false (by decide) v) _
  rw [hQ] at h1
  have h2 := congrArg (fun P => coeff μ (Th ε P)) h1
  simp only [map_sum, th_prod, coeff_sum_monomial] at h2
  by_cases hμ : μ ∈ (Th ε Q).support
  · rw [if_pos hμ] at h2
    exact h2.symm
  · have : coeff μ (Th ε Q) = 0 := notMem_support_iff.1 hμ
    rw [this, map_zero]

end PositivityTheory.Rg.Sw.FFTSteps.CycF

namespace PositivityTheory.Rg.Sw.FFTSteps

open CycF

/- English proof (translation)
Introduce `hF m n ε Q hQ`. Establish `hact : ∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) → act (n` using `n) u Q = Q := hQ`. Establish `hc : ∀ μ, (Th ε Q).coeff μ ∈ pairAlg (Rw ε true) (Fin n) (Fin n)` using `fun μ => hF _ _ _ ((Th ε Q).coeff μ) (fun u hu => coeff_inv u Q (hact _ (blk_unitary true u hu) (blk_block true u)) μ)`. Take `⟨bs, hbs, hspan, hli⟩` from `exists_linearIndependent ℂ ((fun μ => (Th ε Q).coeff μ) '' ((Th ε Q).support : Set _))`. Establish `hfin : bs.Finite` using `(((Th ε Q).support.finite_toSet).image _).subset hbs`.

Use `letI : Fintype bs := hfin.fintype`. Establish `hmem : ∀ μ ∈ (Th ε Q).support, (Th ε Q).coeff μ ∈ Submodule.span ℂ (Set.range (fun j : bs => (j : PV (Rw ε true) (Fin n) (Fin n))))`. Introduce `μ hμ`. Rewrite using `[Subtype.range_coe, hspan]`. Conclude with `Submodule.subset_span ⟨μ, hμ, rfl⟩`.

Establish `hrep : ∀ μ : (Th ε Q).support, ∃ a : bs → ℂ, ∑ j, a j • (j : PV (Rw ε true) (Fin n) (Fin n)) = (Th ε Q).coeff μ.1` using `fun μ => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem μ.1 μ.2)`. Use `choose a ha using hrep`. Set `r : bs → PV (Rw ε false) (Fin n) (Fin n)` to `fun j => ∑ μ : (Th ε Q).support, a μ j • monomial μ.1 1`. Establish `hQ' : Q = ∑ j : bs, emb ε true (j : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r j)` using `by conv_lhs => rw [decomp (ε := ε) Q]`. Rewrite using `[← Finset.sum_coe_sort (Th ε Q).support]`.

Repeatedly rewrite using `[← ha]`. Simplify using `only [r, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]`. Conclude with `Finset.sum_comm`. Establish `hr : ∀ j, r j ∈ pairAlg (Rw ε false) (Fin n) (Fin n)`. Introduce `j`.

Use `hF _ _ _ (r j) (fun u hu => ?_)` and prove the remaining obligations. Establish `h1` using `hact _ (blk_unitary false u hu) (blk_block false u)`. Rewrite `h1` using `[hQ', map_sum]`. Establish `h2 : ∀ i : bs, act (blk ε false u) (emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r i)) = emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i))`. Introduce `i`.

Rewrite using `[map_mul]`. Use `congr 1`. Conclude with `DFunLike.congr_fun (act_emb_other false true (by decide) u) _`. Conclude with `DFunLike.congr_fun (act_emb_same false u) _`. Rewrite `h1` using `[h2]`.

Establish `h3 : ∑ i : bs, emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i) - r i) = 0`. Simplify using `only [map_sub, mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[h1, sub_self]`. Use `indep (fun i : bs => (i : PV (Rw ε true) (Fin n) (Fin n))) hli _ h3 j` as an intermediate fact. Conclude with `sub_eq_zero.1 this`.

Rewrite using `[hQ']`. Use `Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ ?_ ?_)` and prove the remaining obligations. Take `⟨μ, hμ, hj⟩` from `hbs j.2`. Apply `emb_pairAlg true` to reduce the goal to its premises. Rewrite using `[← hj]`.

Conclude with `hc μ`. Conclude with `emb_pairAlg false (hr j)`.
-/
theorem cycFFT : CycFFT := by
  classical
  intro hF m n ε Q hQ
  have hact : ∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      act (n := n) u Q = Q := hQ
  have hc : ∀ μ, (Th ε Q).coeff μ ∈ pairAlg (Rw ε true) (Fin n) (Fin n) := fun μ =>
    hF _ _ _ ((Th ε Q).coeff μ) (fun u hu => coeff_inv u Q (hact _ (blk_unitary true u hu) (blk_block true u)) μ)
  obtain ⟨bs, hbs, hspan, hli⟩ := exists_linearIndependent ℂ
    ((fun μ => (Th ε Q).coeff μ) '' ((Th ε Q).support : Set _))
  have hfin : bs.Finite := (((Th ε Q).support.finite_toSet).image _).subset hbs
  letI : Fintype bs := hfin.fintype
  have hmem : ∀ μ ∈ (Th ε Q).support, (Th ε Q).coeff μ ∈
      Submodule.span ℂ (Set.range (fun j : bs => (j : PV (Rw ε true) (Fin n) (Fin n)))) := by
    intro μ hμ
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hrep : ∀ μ : (Th ε Q).support, ∃ a : bs → ℂ,
      ∑ j, a j • (j : PV (Rw ε true) (Fin n) (Fin n)) = (Th ε Q).coeff μ.1 := fun μ =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem μ.1 μ.2)
  choose a ha using hrep
  let r : bs → PV (Rw ε false) (Fin n) (Fin n) := fun j => ∑ μ : (Th ε Q).support, a μ j • monomial μ.1 1
  have hQ' : Q = ∑ j : bs, emb ε true (j : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r j) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [← Finset.sum_coe_sort (Th ε Q).support]
    simp_rw [← ha]
    simp only [r, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  have hr : ∀ j, r j ∈ pairAlg (Rw ε false) (Fin n) (Fin n) := by
    intro j
    refine hF _ _ _ (r j) (fun u hu => ?_)
    have h1 := hact _ (blk_unitary false u hu) (blk_block false u)
    rw [hQ', map_sum] at h1
    have h2 : ∀ i : bs, act (blk ε false u) (emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r i)) =
        emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i)) := by
      intro i
      rw [map_mul]
      congr 1
      · exact DFunLike.congr_fun (act_emb_other false true (by decide) u) _
      · exact DFunLike.congr_fun (act_emb_same false u) _
    simp_rw [h2] at h1
    have h3 : ∑ i : bs, emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) *
        emb ε false (sub u (u.map star) (r i) - r i) = 0 := by
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
      rw [h1, sub_self]
    have := indep (fun i : bs => (i : PV (Rw ε true) (Fin n) (Fin n))) hli _ h3 j
    exact sub_eq_zero.1 this
  rw [hQ']
  refine Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ ?_ ?_)
  · obtain ⟨μ, hμ, hj⟩ := hbs j.2
    apply emb_pairAlg true
    rw [← hj]
    exact hc μ
  · exact emb_pairAlg false (hr j)

end PositivityTheory.Rg.Sw.FFTSteps
