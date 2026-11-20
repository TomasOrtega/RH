import Mathlib
import ReciprocityTheory.DualLattices.CyclicRecursionStatement

noncomputable section

open WittVector MvPolynomial

namespace ReciprocityTheory.PGsh

section TeichSum

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Rewrite using `[WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]`. Apply the tactic sequence `simp [Finset.sum_range_succ] <;> ring`.
-/
private lemma ghost_one {R : Type*} [CommRing R] (x : WittVector p R) :
    ghostComponent 1 x = x.coeff 0 ^ p + (p : R) * x.coeff 1 := by
  rw [WittVector.ghostComponent_apply, wittPolynomial_eq_sum_C_mul_X_pow]
  simp [Finset.sum_range_succ] <;> ring

/- English proof (translation)
Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a t ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, WittVector.add_coeff_zero, ih]`.
-/
private lemma coeff_zero_sum {R ι : Type*} [CommRing R] (s : Finset ι) (f : ι → WittVector p R) :
    (∑ i ∈ s, f i).coeff 0 = ∑ i ∈ s, (f i).coeff 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, WittVector.add_coeff_zero, ih]

/- English proof (translation)
Apply the tactic sequence `induction S using MvPolynomial.induction_on <;> simp_all`.
-/
private lemma ringHom_aeval {K ι : Type*} [CommRing K] (σ : K →+* K) (g : ι → K)
    (S : MvPolynomial ι ℤ) : σ (aeval g S) = aeval (σ ∘ g) S := by
  induction S using MvPolynomial.induction_on <;> simp_all

/- English proof (translation)
Establish `h0 : (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i`. Rewrite using `[coeff_zero_sum]`. Simplify using the standard rewrite rules. Use `⟨h0, ?_⟩` and prove the remaining obligations. Establish `hg : ghostComponent 1 (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)) = ∑ i ∈ s, (X i : MvPolynomial ι ℤ) ^ p`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[ghost_one]`. Simplify using `[WittVector.teichmuller_coeff_pos]`. Rewrite `hg` using `[ghost_one, h0]`.

Take the linear combination `hg`.
-/
private lemma univ_coeff {ι : Type} (s : Finset ι) :
    (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i ∧
    (p : MvPolynomial ι ℤ) * (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 1 =
      ∑ i ∈ s, X i ^ p - (∑ i ∈ s, X i) ^ p := by
  have h0 : (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)).coeff 0 = ∑ i ∈ s, X i := by
    rw [coeff_zero_sum]
    simp
  refine ⟨h0, ?_⟩
  have hg : ghostComponent 1 (∑ i ∈ s, teichmuller p (X i : MvPolynomial ι ℤ)) =
      ∑ i ∈ s, (X i : MvPolynomial ι ℤ) ^ p := by
    rw [map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ghost_one]
    simp [WittVector.teichmuller_coeff_pos]
  rw [ghost_one, h0] at hg
  linear_combination hg

/- English proof (translation)
Establish `hF : WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y) = y`. Use extensionality with `n`. Rewrite using `[WittVector.coeff_frobenius_charP, WittVector.map_coeff]`. Simplify using `[frobeniusEquiv_symm_pow_p]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hF]`. Use `_ = _ := WittVector.verschiebung_frobenius _`.
-/
private lemma verschiebung_eq_map_frobenius_symm_mul_p {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (y : WittVector p K) :
    WittVector.verschiebung y = WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y * p := by
  have hF : WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y) = y := by
    ext n
    rw [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
    simp [frobeniusEquiv_symm_pow_p]
  calc WittVector.verschiebung y = WittVector.verschiebung
        (WittVector.frobenius (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) y)) := by
        rw [hF]
    _ = _ := WittVector.verschiebung_frobenius _

/- English proof (translation)
Establish `h1 : ∀ z : WittVector p K, ∃ u : WittVector p K, z = teichmuller p (z.coeff 0) + WittVector.verschiebung u ∧ u.coeff 0 = z.coeff 1`. Introduce `z`. Use `⟨WittVector.mk p (fun n => z.coeff (n + 1)), ?_, rfl⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[WittVector.coeff_add_of_disjoint]`.

Break down `n with _ | n` into its components or cases. Simplify using `[WittVector.teichmuller_coeff_zero, WittVector.verschiebung_coeff_zero]`. Simplify using `[WittVector.teichmuller_coeff_pos, WittVector.verschiebung_coeff_succ]`. Introduce `m`. Break down `m with _ | m` into its components or cases.

Use `right`. Simplify using `[WittVector.verschiebung_coeff_zero]`. Use `left`. Simplify using `[WittVector.teichmuller_coeff_pos]`. Take `⟨u, hu, hu0⟩` from `h1 x`.

Rewrite `hu` using `[verschiebung_eq_map_frobenius_symm_mul_p]`. Take `⟨v, hv, -⟩` from `h1 (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u)`. Rewrite `hv` using `[verschiebung_eq_map_frobenius_symm_mul_p]`. Establish `hc : (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u).coeff 0 = (frobeniusEquiv K p).symm (x.coeff 1)`. Rewrite using `[WittVector.map_coeff, hu0]`.

Apply the tactic sequence `try rfl`. Rewrite `hv` using `[hc]`. Use `⟨WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul {K : Type} [CommRing K] [CharP K p] [PerfectRing K p]
    (x : WittVector p K) :
    ∃ w : WittVector p K, x = teichmuller p (x.coeff 0) +
      (p : WittVector p K) * teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
      (p : WittVector p K) ^ 2 * w := by
  have h1 : ∀ z : WittVector p K, ∃ u : WittVector p K,
      z = teichmuller p (z.coeff 0) + WittVector.verschiebung u ∧ u.coeff 0 = z.coeff 1 := by
    intro z
    refine ⟨WittVector.mk p (fun n => z.coeff (n + 1)), ?_, rfl⟩
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · rcases n with _ | n
      · simp [WittVector.teichmuller_coeff_zero, WittVector.verschiebung_coeff_zero]
      · simp [WittVector.teichmuller_coeff_pos, WittVector.verschiebung_coeff_succ]
    · intro m
      rcases m with _ | m
      · right
        simp [WittVector.verschiebung_coeff_zero]
      · left
        simp [WittVector.teichmuller_coeff_pos]
  obtain ⟨u, hu, hu0⟩ := h1 x
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hu
  obtain ⟨v, hv, -⟩ := h1 (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u)
  rw [verschiebung_eq_map_frobenius_symm_mul_p] at hv
  have hc : (WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u).coeff 0 =
      (frobeniusEquiv K p).symm (x.coeff 1) := by
    rw [WittVector.map_coeff, hu0]
    try rfl
  rw [hc] at hv
  refine ⟨WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v, ?_⟩
  calc x = teichmuller p (x.coeff 0) +
        WittVector.map ((frobeniusEquiv K p).symm : K →+* K) u * p := hu
    _ = teichmuller p (x.coeff 0) + (teichmuller p ((frobeniusEquiv K p).symm (x.coeff 1)) +
          WittVector.map ((frobeniusEquiv K p).symm : K →+* K) v * p) * p := by rw [hv]
    _ = _ := by ring

/- English proof (translation)
Introduce `ι s`. Use `⟨⟨_, (univ_coeff (p := p) s).2⟩, ?_⟩` and prove the remaining obligations. Introduce `K _ _ _ X S hS`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (∑ i ∈ s, teichmuller p (X i))`.

Establish `h0 : (∑ i ∈ s, teichmuller p (X i)).coeff 0 = ∑ i ∈ s, X i`. Rewrite using `[coeff_zero_sum]`. Simplify using the standard rewrite rules. Establish `hmap : WittVector.map (MvPolynomial.aeval X).toRingHom (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)) = ∑ i ∈ s, teichmuller p (X i)`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[WittVector.map_teichmuller]`. Simplify using the standard rewrite rules. Establish `hSeq : (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)).coeff 1 = S`. Establish `hp0 : (p : MvPolynomial ι ℤ) ≠ 0`.

Conclude with `(Fact.out : p.Prime).ne_zero` after adjusting the coercions. Conclude with `mul_left_cancel₀ hp0 ((univ_coeff (p := p) s).2.trans hS.symm)`. Establish `h1 : (∑ i ∈ s, teichmuller p (X i)).coeff 1 = MvPolynomial.aeval X S`. Rewrite using `[← hmap, WittVector.map_coeff, hSeq]`. Apply the tactic sequence `try rfl`.

Establish `hfr : (frobeniusEquiv K p).symm (MvPolynomial.aeval X S) = MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S` using `ringHom_aeval ((frobeniusEquiv K p).symm : K →+* K) X S`. Use `⟨w, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[h0, h1, hfr]`. Conclude with `hw`. Introduce `y t`.

Establish `hd : ((p : ℕ) : WittVector p K) ∣ (teichmuller p y + (p : WittVector p K) * t) - teichmuller p y` using `⟨t, by ring⟩`. Take `⟨w, hw⟩` from `dvd_sub_pow_of_dvd_sub hd 1`. Use `⟨w, ?_⟩` and prove the remaining obligations. Simplify using `only [pow_one] at hw`. Rewrite using `[show teichmuller p (y ^ p) = teichmuller p y ^ p from map_pow _ _ _]`.

Take the linear combination `hw`.
-/
theorem teichSum (p : ℕ) [Fact p.Prime] : TeichSumStatement p := by
  intro ι s
  refine ⟨⟨_, (univ_coeff (p := p) s).2⟩, ?_⟩
  intro K _ _ _ X S hS
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw⟩ := exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (∑ i ∈ s, teichmuller p (X i))
    have h0 : (∑ i ∈ s, teichmuller p (X i)).coeff 0 = ∑ i ∈ s, X i := by
      rw [coeff_zero_sum]
      simp
    have hmap : WittVector.map (MvPolynomial.aeval X).toRingHom
        (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)) =
          ∑ i ∈ s, teichmuller p (X i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [WittVector.map_teichmuller]
      simp
    have hSeq : (∑ i ∈ s, teichmuller p (MvPolynomial.X i : MvPolynomial ι ℤ)).coeff 1 = S := by
      have hp0 : (p : MvPolynomial ι ℤ) ≠ 0 := by
        exact_mod_cast (Fact.out : p.Prime).ne_zero
      exact mul_left_cancel₀ hp0 ((univ_coeff (p := p) s).2.trans hS.symm)
    have h1 : (∑ i ∈ s, teichmuller p (X i)).coeff 1 = MvPolynomial.aeval X S := by
      rw [← hmap, WittVector.map_coeff, hSeq]
      try rfl
    have hfr : (frobeniusEquiv K p).symm (MvPolynomial.aeval X S) =
        MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S :=
      ringHom_aeval ((frobeniusEquiv K p).symm : K →+* K) X S
    refine ⟨w, ?_⟩
    rw [h0, h1, hfr] at hw
    exact hw
  · intro y t
    have hd : ((p : ℕ) : WittVector p K) ∣ (teichmuller p y + (p : WittVector p K) * t) -
        teichmuller p y := ⟨t, by ring⟩
    obtain ⟨w, hw⟩ := dvd_sub_pow_of_dvd_sub hd 1
    refine ⟨w, ?_⟩
    simp only [pow_one] at hw
    rw [show teichmuller p (y ^ p) = teichmuller p y ^ p from map_pow _ _ _]
    linear_combination hw

end TeichSum

section Cyclic

private def cycT {V : Type} [AddCommGroup V] [Module ℚ V] (o : ℕ) (P : ℚ) (La : ZMod o → V)
    (i : ZMod o) : V :=
  ∑ n ∈ Finset.range o, P⁻¹ ^ (n + 1) • La (i + ((n + 1 : ℕ) : ZMod o))

end Cyclic

end ReciprocityTheory.PGsh
